import Rho5.Integration.StagedAssembly

/-! Actual loaded module names, for binding the objects used by this integration.
No upstream proof body is replayed or printed. -/
run_cmd do
  let env ← Lean.getEnv
  for m in env.header.moduleNames do
    Lean.logInfo m!"C02_LOADED_MODULE {m}"
