"""Reviewed classification of every census key (FORMAL-001). Every key must match exactly ONE rule; the census
then fails on any unmatched (new) site. Rules are ordered from most to least specific; `keys` lists are exact.

Classes (the only effect-creating classes are LEAN_GATED and SIMULATED_OUTSIDE_LEAN_BOUNDARY):
  LEAN_GATED                     consequential effect; dominated by a fresh Lean T (legion_decide) for the exact action
  PRIMITIVE_INTERNAL             effect primitive only reachable from a LEAN_GATED (or exogenous) caller in the same class
  BYPASS_CLOSED                  was reachable without Lean; closure + negative test recorded
  EXOGENOUS_WORLD_DYNAMICS       world-scheduled events from the frozen spec (environment, not an agent effect)
  ANSWER_RECORD                  /analyze answer record; cannot feed any effect rule (closure B-R2-3)
  SEPARATE_TEST_WORLD            in-process World of a test harness; shares no state with the qualified world
  SIMULATED_OUTSIDE_LEAN_BOUNDARY  Federation/Marketplace simulated world effects: NOT Lean-admitted (verdict F wrt PE2)
  READ_ONLY_EXTERNAL             external GET only (provider readback)
  AUTH_TOKEN_EXCHANGE            OAuth client-credentials POST: no business effect
  LOOPBACK_IPC                   HTTP between local LEGION processes (authority, sidecar, agents, peers, hub, dashboard)
  MODEL_INFERENCE                LLM inference call (NVIDIA NIM): no effect
  PROCESS_TOOLING                subprocess for git, ACLs, the decider, workers, process supervision
  FAULT_INJECTION_OR_EXIT        os._exit for deterministic fault injection / parent-death watchdog
  REFLECTIVE_REVIEWED            reflective call reviewed: cannot reach an effect primitive
"""
import json
import re
import sys
from pathlib import Path

R2 = "LEGION-R2:tests/legion_struct/"
CO = "LEGION-Commerce:"
FE = "LEGION-Federation:"
MK = "LEGION-Marketplace:"

RULES = [
    # ---------------- consequential: R2 world commit boundary
    {"keys": [R2 + "world_server.py::Handler._actuate::WORLD.call_write"], "class": "LEAN_GATED",
     "gate": "_actuate: verify_fresh + reservation + task/tool/target + semantic binding + LeanDecider.decide(build_payload) "
             "== T, then mint_lean_ticket(exact action); LeanGatedWorld.call_write refuses a new effect without that ticket",
     "evidence": ["test_formal_core_boundary.py (B01-B18)", "test_formal_core_world_negatives.py", "test_formal001_closure.py"]},
    {"keys": [R2 + "causal_007/lean_gated_world.py::LeanGatedWorld.call_write::<call>.call_write"], "class": "PRIMITIVE_INTERNAL",
     "gate": "reached only after a single-use Lean ticket for (command_id, tool, target, args) or for an already applied command id "
             "(idempotent duplicate: no new effect)", "evidence": ["test_formal001_closure.py::test_b_r2_2_*"]},
    {"keys": [R2 + "world_engine.py::World.call_write::self._apply_effects", R2 + "world_engine.py::World.call_write::self._run_derived",
              R2 + "world_engine.py::World._apply_effects::self._apply_prepared", R2 + "world_engine.py::World._run_derived::self._apply_effects"],
     "class": "PRIMITIVE_INTERNAL", "gate": "World internals; in the qualified runtime the World is a LeanGatedWorld"},
    {"keys": [R2 + "world_engine.py::World.fire::self._apply_effects", R2 + "world_engine.py::World.fire::self._run_derived",
              R2 + "causal_007/lean_gated_world.py::LeanGatedWorld.fire::<call>.fire", R2 + "world_server.py::fire_due_events::WORLD.fire"],
     "class": "EXOGENOUS_WORLD_DYNAMICS",
     "gate": "events of the frozen world spec only (B-R2-4 closure: invented event dicts refused); time/after-effect triggers",
     "evidence": ["test_formal001_closure.py::test_b_r2_4_invented_event_cannot_fire"]},
    {"keys": [R2 + "world_server.py::Handler.do_POST::WORLD.analyze"], "class": "ANSWER_RECORD",
     "gate": "writes state.answers only; worlds whose effect rules read answers are refused at start (B-R2-3)",
     "evidence": ["test_formal001_closure.py::test_b_r2_3_answer_channel_rejected_and_13_worlds_clean"]},
    {"keys": [R2 + "causal_007/causal_host.py::CausalHost._apply::self.world.call_write",
              R2 + "causal_007/causal_host.py::CausalHost._apply::self.world.analyze",
              R2 + "causal_007/causal_host.py::CausalHost._apply::self.world.fire"], "class": "SEPARATE_TEST_WORLD",
     "gate": "own in-memory World instance; unreachable from every qualified runtime entry point (import closure)",
     "evidence": ["test_formal001_closure.py::test_causal_host_unreachable_from_qualified_runtime"]},
    {"keys": [R2 + "causal_007/lean_admission.py::LeanDecider._start::subprocess.Popen"], "class": "PROCESS_TOOLING",
     "gate": "starts the decider only if sha256 is the pinned qualified build (B-R2-1)",
     "evidence": ["test_formal001_closure.py::test_b_r2_1_*"]},
    # ---------------- consequential: Commerce external effects
    {"keys": [CO + "commerce_adapter/gateway.py::Gateway.create::self.call[POST]",
              CO + "commerce_adapter/gateway.py::Gateway.capture::self.call[POST]"], "class": "LEAN_GATED",
     "gate": "recheck(admission.check) in the SAME transaction immediately before; Gateway.require_lean demands that check's "
             "attestation lean_verdict == T bound to digest(intent) (FORMAL-001 B-COM-1/2); MOCK_ONLY test doubles exempt",
     "evidence": ["formal001_evidence/FORMAL001_COMMERCE_NEGATIVES.json", "SANDBOX_ADMISSION_TESTS_after_closure.json",
                  "LMF007_NEGATIVES_after_closure.json"]},
    {"keys": [CO + "commerce_adapter/gateway.py::Gateway.call::self.provider.request",
              CO + "commerce_adapter/paypal.py::PayPalSandbox.request::self._wire",
              CO + "commerce_adapter/paypal.py::PayPalSandbox._wire::urllib.request.Request[data/method]"], "class": "PRIMITIVE_INTERNAL",
     "gate": "Gateway.call enforces require_lean for every non-GET; PayPalSandbox(read_only=True) refuses POST (READ_ONLY_CLIENT)"},
    {"keys": [CO + "commerce_adapter/paypal.py::PayPalSandbox.oauth::self._wire"], "class": "AUTH_TOKEN_EXCHANGE"},
    {"keys": [CO + "commerce_adapter/readback.py::independent_readback::provider.request",
              CO + "commerce_demo/readback.py::main::provider.request"], "class": "READ_ONLY_EXTERNAL",
     "gate": "GET only; separate process; PayPalSandbox(read_only=True)"},
    {"keys": [CO + "commerce_demo/nim.py::chat::urllib.request.Request[data/method]", CO + "commerce_demo/nim.py::chat::urllib.request.urlopen",
              FE + "legion_federation/nim.py::chat::urllib.request.Request[data/method]", FE + "legion_federation/nim.py::chat::urllib.request.urlopen"],
     "class": "MODEL_INFERENCE"},
    {"keys": [R2 + "causal_007/provider_proxy.py::Handler.do_POST.call_fn::urllib.request.Request[data/method]",
              R2 + "causal_007/provider_proxy.py::Handler.do_POST.call_fn::urllib.request.urlopen"], "class": "MODEL_INFERENCE",
     "gate": "attested model-provider proxy: forwards agent LLM calls (inference only; no world or payment API)"},
    # ---------------- Federation / Marketplace simulated effects (NOT Lean-admitted)
    {"keys": [FE + "legion_federation/owner_peer.py::Owner.native::self.world.call_write",
              FE + "legion_federation/world_peer.py::Peer.handle_request::c.world.call_write",
              FE + "legion_federation/role_handlers.py::admin::o.world.fire",
              FE + "legion_federation/world_peer.py::make_handler.H.do_POST::<subscript>.world.fire"],
     "class": "SIMULATED_OUTSIDE_LEAN_BOUNDARY",
     "gate": "federation-edge T/F/Z policy (tested, not Lean-proved) + pinned Core native preconditions; SIMULATED world state only; "
             "the only external effect derived from a federation contract (PayPal) goes through the Lean-gated Commerce Gateway. "
             "Latent: admin event endpoints pass the request's event to pinned World.fire, whose fallback applies a caller dict "
             "(operator admin token only)."},
    # ---------------- loopback IPC between local processes
    {"pattern": r"^LEGION-R2:.*(attempt_authority\.py::AuthorityClient\._call|mission_host\.py::(_get|World\.up)|"
                r"sidecar_server\.py::CausalState\._fetch_world_records|supervisor\.py::Supervisor\._wait_health|struct_agent\.py::http|"
                r"struct_readback\.py::get)::urllib", "class": "LOOPBACK_IPC",
     "gate": "127.0.0.1 between LEGION processes; world effects only via /actuate (actuator token + Lean); provider_proxy forwards model "
             "calls (inference)"},
    {"pattern": r"^LEGION-(Federation|Marketplace):.*(hub\.py::(get|post)|role_handlers\.py::post|tools/(judge_world_cases|run_world_cases)\.py::"
                r"(get|Client\.post)|dashboard\.py::main\.H\.do_POST|e2e\.py::(get|post)|judge\.py::get)::urllib", "class": "LOOPBACK_IPC",
     "gate": "127.0.0.1 signed-envelope HTTP between owner peers, hub, registry, judge, dashboard (simulated effects only)"},
    # ---------------- process tooling / exits
    {"pattern": r"::os\._exit$", "class": "FAULT_INJECTION_OR_EXIT"},
    {"pattern": r"::subprocess\.(run|Popen|check_output|check_call)$", "class": "PROCESS_TOOLING",
     "gate": "git/ACL/worker/decider/process supervision; no provider credentials are passed to a child that could POST except "
             "commerce_demo.readback (read_only=True)"},
    # ---------------- reflective
    {"pattern": r"::(getattr\(<dynamic>\)|__import__|importlib\.import_module)$", "class": "REFLECTIVE_REVIEWED",
     "gate": "test monkeypatch shims, profiling wrappers and fixture loaders; reviewed: no effect primitive reachable by name"},
]


def classify(keys):
    out, errors = {}, []
    for k in keys:
        hits = [r for r in RULES if "keys" in r and k in r["keys"]]          # explicit keys take precedence
        if not hits:
            hits = [r for r in RULES if "pattern" in r and re.search(r["pattern"], k)]
        if len(hits) != 1:
            errors.append({"key": k, "matching_rules": len(hits)})
            continue
        r = hits[0]
        out[k] = {kk: v for kk, v in r.items() if kk not in ("keys", "pattern")}
    unused = [r.get("keys") or r.get("pattern") for r in RULES
              if not any(("keys" in r and k in r["keys"]) or ("pattern" in r and re.search(r["pattern"], k)) for k in keys)]
    return out, errors, unused


if __name__ == "__main__":
    raw = json.loads(Path(sys.argv[1]).read_text())
    keys = [r["key"] for r in raw["rows"]]
    table, errors, unused = classify(keys)
    Path(sys.argv[2]).write_text(json.dumps({"schema": "legion.formal001.classification.v1", "classes": table,
                                             "rules_source": "make_classification.py"}, indent=1, sort_keys=True))
    print(json.dumps({"classified": len(table), "errors": errors, "unused_rules": unused}, indent=1))
    sys.exit(1 if errors else 0)
