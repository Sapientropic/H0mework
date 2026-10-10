import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateBraEntryColumns
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateBraPairBasis
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateBraLeftData
import Lean.Elab.Tactic
import Lean.Util.FoldConsts
set_option autoImplicit false
namespace LowEnergy.ActualCandidateBra
open Lean Meta Elab Tactic

elab "eval_bra_pair_row" index:num : tactic => withMainContext do
  let row := index.getNat
  let initial ← (← getMainGoal).getType
  let some (_,_,right) := initial.eq? | throwError "Expected an actual pair-row equality"
  let column := right.getAppArgs.back!
  unless column.isFVar do throwError "Expected the actual free source-column index"
  let columnId := mkIdent (← column.fvarId!.getDecl).userName
  let left := mkIdent (Name.str `LowEnergy.ActualCandidateBra ("leftRow"++toString row))
  let pair := mkIdent (Name.str `LowEnergy.ActualCandidateBra ("pairRow"++toString row))
  evalTactic (← `(tactic| unfold $left:ident))
  let columns := (Array.range 27).map fun i => mkIdent
    (Name.str `LowEnergy.ActualCandidateBra ("actual_entry_column"++toString i))
  evalTactic (← `(tactic| simp only [$[$columns:ident],*]))
  evalTactic (← `(tactic| fin_cases $columnId:ident))
  let goals ← getGoals
  for goal in goals do
    setGoals [goal]
    let columnValues := (← goal.getType).getUsedConstants.filterMap fun name =>
      if name.toString.startsWith "LowEnergy.ActualCandidateBra.column" then
        some (mkIdent name) else none
    evalTactic (← `(tactic| norm_num [$[$columnValues:ident],*, $pair:ident,
      ActualCandidateVertexLiterals.coefficient]))
    unless (← getGoals).isEmpty do
      let ids := (← (← getMainGoal).getType).getUsedConstants.filterMap fun name =>
        if name.toString.startsWith "_private.H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValues" ||
            name.toString.startsWith "LowEnergy.ActualCandidateBra.leftCoefficient" ||
            name.toString.startsWith "LowEnergy.ActualCandidateBra.pairCoefficient" then
          some (mkIdent name) else none
      evalTactic (← `(tactic| norm_num [$[$ids:ident],*, ActualCandidateVertexLiterals.coefficient]))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| try simp +decide))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| try simp only [sqrt30_factor]))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| try ring_nf))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| norm_num [Complex.I_sq, sqrt2_square, sqrt15_square]))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| try ring))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| try simp))
    unless (← getGoals).isEmpty do
      throwError m!"Actual source pair row {row} did not close: {← (← getMainGoal).getType}"
  setGoals []
end LowEnergy.ActualCandidateBra
