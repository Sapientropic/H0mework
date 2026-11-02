import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.Format
import Lean.Elab.Command
set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Contract
open Input.Challenge.Redress.Shared.Iteration
variable (raw : Requests.Cursor) (count : Nat)
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicSourceOwnedIterationContract.case001 : (execute 0 raw).finish = raw := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicSourceOwnedIterationContract.case002 : (execute (count+1) raw).first? = some (produce raw) := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicSourceOwnedIterationContract.case003 : (execute 0 raw).sourceInputs = [] := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicSourceOwnedIterationContract.case004 : (execute 1 raw).sourceInputs = [] := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicSourceOwnedIterationContract.case005 : (execute 2 raw).sourceInputs.length = 1 := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicSourceOwnedIterationContract.case006 : executeLegacy count raw = Current.execute count (Current.initial raw) := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicSourceOwnedIterationContract.case007 : (execute (count+1) raw).sourceInputs =
    (Current.Autonomous.execute (produce raw).target count).inputs := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicSourceOwnedIterationContract.case008 (run : Run raw count) : Input.Event.Evolution raw.saved run.finish.saved := run.native
#eval IO.println "DEFAULT SOURCE CONTINUATION CONTRACT PASS: 8/8"
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Contract
open Lean Elab Command
private def includes (text needle : String) : Bool := 1 < (text.splitOn needle).length
private def actualBody (env : Environment) (root : Name) : CommandElabM String := do
  let some index := env.getModuleIdxFor? root | throwError "missing actual source producer {root}"
  let entries := IR.declMapExt.getModuleEntries env index ++ IR.declMapExt.getModuleIREntries env index
  let actual := entries.filter fun decl => decl.name.toString.startsWith root.toString
  unless !actual.isEmpty do throwError "missing executable source producer {root}"
  return String.intercalate "\n" (actual.toList.map fun decl => toString decl)
elab "#check_default_continuation" : command => do
  let env ← getEnv
  let actual ← actualBody env `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.execute
  unless includes actual "Iteration.produce" && includes actual "Autonomous.execute" do
    throwError "public default is not original first planner followed by own-source continuation"
  if includes actual "blocked" then throwError "public default seals a typed planner block"
  let legacy ← actualBody env `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.executeLegacy
  unless includes legacy "Current.execute" do throwError "explicit legacy override is missing"
  let basis ← actualBody env `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.FutureOrigin.advance
  if includes basis "readyNative" || includes basis "reconstructedNative" then throwError "basis advance eagerly constructs a full event route"
  logInfo "DEFAULT SOURCE CONTINUATION IR PASS: original first call; actual source tail; explicit legacy; deferred native route"
#check_default_continuation
