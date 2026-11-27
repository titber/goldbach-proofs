# Native local check of BinaryShiftExceptionUnion

This application is based on `lsernau/grh-lean@72fead102f663d5c7a407964a13dc0cf9d977207`, project `grh-compact`.
Use its original Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Keep the project and all build products separate from any 4.36 checkout. Run from `grh-compact`, with this exact Lean's bin directory on PATH, and Python 3.11+.

```powershell
lake exe cache get Mathlib
# Either replay compact from source:
lake env python -u scripts/verify_binary_shift.py
# OR restore the published compact module artifacts, with checks, then compile the application:
git -c core.autocrlf=false clone -b grh-lean-cache https://github.com/leanprover-community/riemann-hypothesis.git ../cache-reference
git -C ../cache-reference -c core.autocrlf=false checkout --detach 5ba920829cb7286b51f4d233b493f5b1287bf51b
python -u scripts/restore_compact_cache.py ../cache-reference/grh-compact
lake env python -u scripts/verify_binary_shift.py --validated-cache
```

The optional cache shares the compact source tree `b834f80c6399db99d54ce171ba541c4a95a4f90f` with the base. Its receipt and SHA-256 checks identify the build products; they are not an independent verification of GRH. The cached route also checks Lake's native dependency traces, compiles the GRH consumer, the exception-density lemma and the frozen application, then typechecks the isolated audit. See `.lake/binary-shift-replay/` for compiler stdout and diagnostics.

The exception-density source and the application reduction are from the local `goldbach-proofs` research branch (conditional proof at `62adb2c`). The native version supplies the theorem imported from upstream `Main`, not a hypothesis. The audit uses the frozen lease statement itself as the expected type. No website or Jenkins submission is performed.
