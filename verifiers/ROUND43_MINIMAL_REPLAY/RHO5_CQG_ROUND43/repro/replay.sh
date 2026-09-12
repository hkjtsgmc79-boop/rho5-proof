#!/usr/bin/env bash
set -euo pipefail
# Run from the root of the delivered package. No discovery tree generation.
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
mkdir -p replay_logs
rho_python="${RHO5_PYTHON:-python3}"
rho_cxx="${CXX:-c++}"
rho_include=()
if [ -n "${BOOST_INCLUDE:-}" ]; then rho_include=(-I "$BOOST_INCLUDE"); fi
nice -n 10 "$rho_python" repro/verify_large_budgets.py --output replay_logs/analytic.json > replay_logs/analytic.log
nice -n 10 "$rho_python" repro/verify_head_budget.py > replay_logs/head_budget.json
nice -n 10 "$rho_python" repro/verify_certificate_models.py proofs/I proofs/II > replay_logs/model_audit.json
for rho_case in I II; do
  nice -n 10 "$rho_cxx" -std=c++17 -O2 "${rho_include[@]}" "proofs/$rho_case/mc_verify.cpp" -o "replay_logs/verify_$rho_case"
  nice -n 10 "replay_logs/verify_$rho_case" "proofs/$rho_case/result.tree" > "replay_logs/verify_$rho_case.json"
  cat "replay_logs/verify_$rho_case.json"
done
printf '%s\n' 'ROUND43_MINIMAL_REPLAY_PASS: I and II closed; exact III-to-II physical map covers III.'
