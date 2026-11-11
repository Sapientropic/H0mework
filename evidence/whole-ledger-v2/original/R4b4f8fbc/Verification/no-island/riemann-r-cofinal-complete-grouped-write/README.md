# Complete grouped write of the original Gamma requests

CP532 groups every original request by its Gamma Step. Flattening the groups recovers the full ordered batch and its executed trace. Adding their signed requests recovers the original native boundary. The sum of the actual Step Joint cochains equals the original next Joint boundary.

One canonical method pays the grouped trace and completion together with the original whole-ledger disposition and literal next. For any actual request, the control locates its complete nonempty Step group in the native trace. Omitting or duplicating that group changes the trace.

The independent audit checks 74 new mathematical declarations, including 63 private declarations, and inventories 1,084 compiler extras. It imports the paid base once and checks the transitive axioms.

```sh
python3 Verification/no-island/riemann-r-cofinal-complete-grouped-write/certify.py \
  --repo "$PWD" --compiled-root "$CP532_COMPILED_ROOT" \
  --base-lean-path-file "$CP532_LEAN_PATH_FILE" --output "$CP532_AUDIT_DIR"
```

Add `--verify-inputs-only` to check the tracked sources and compiled provenance without Lean.
