import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateBraLeftData
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexRowAliases
import Lean.Elab.Tactic
import Lean.Util.FoldConsts
set_option autoImplicit false
namespace LowEnergy.ActualCandidateBra
open Lean Meta Elab Tactic

elab "eval_bra_left" index:num : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let rows := target.getUsedConstants.filterMap fun name =>
    if name.toString.startsWith "_private.SourceActualCandidateVertexValues" &&
        name.toString.endsWith (".row_"++toString index.getNat) then
      some (mkIdent name) else none
  unless rows.size = 1 do throwError "Expected exactly the paid actual source row"
  let value := mkIdent (Name.str `LowEnergy.ActualCandidateBra ("leftRow"++toString index.getNat))
  evalTactic (← `(tactic| norm_num [tensor, $value:ident, $[$rows:ident],*,
    ActualCandidateVertexLiterals.coefficient]))
  unless (← getGoals).isEmpty do
    let ids := (← (← getMainGoal).getType).getUsedConstants.filterMap fun name =>
      if name.toString.startsWith "LowEnergy.ActualCandidateBra.leftCoefficient" then
        some (mkIdent name) else none
    evalTactic (← `(tactic| norm_num [$[$ids:ident],*]))
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| try simp +decide))
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| ring))
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| try simp))
  unless (← getGoals).isEmpty do throwError m!"Actual source-row contraction did not close: {← (← getMainGoal).getType}"
end LowEnergy.ActualCandidateBra
