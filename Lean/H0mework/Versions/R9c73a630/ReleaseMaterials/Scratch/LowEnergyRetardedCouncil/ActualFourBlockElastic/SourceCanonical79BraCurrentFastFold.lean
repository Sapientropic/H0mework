import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraCurrentFold
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators

theorem sparse_current_factor (i j : Fin 79) :
    sparseCurrentPoint i j =
      ∑s : Fin 8,sourceWeight (sourcePolynomialPoint true) i s *
        (∑t : Fin 8,ActualCandidateBra.primalPairPoint (sourceField i s) (sourceField j t) *
          sourceWeight (sourcePolynomialPoint false) j t) := by
  simp only [sparseCurrentPoint,Finset.mul_sum,mul_assoc]

open Lean Meta Elab Tactic
private def sparseReadName (row : Nat) (weights : Bool) : Name :=
  let moduleName := if row = 0 then "SourceCanonical79SourceSparsePilot" else
    "SourceCanonical79SourceSparseRows" ++ toString (row/16)
  let ns := Name.str (Name.str (Name.num (Name.append `_private ("H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic." ++ moduleName).toName) 0)
    "LowEnergy") "ActualCanonical79Imaginary"
  Name.str ns ((if weights then "weights" else "fields") ++ toString row)

elab "eval_bra_current_row_fast" index:num : tactic => withMainContext do
  let row := index.getNat
  let initial ← (← getMainGoal).getType
  let some (_,_,right) := initial.eq? | throwError "Expected an actual current-row equality"
  let column := right.getAppArgs.back!
  unless column.isFVar do throwError "Expected the actual free source-column index"
  let columnId := mkIdent (← column.fvarId!.getDecl).userName
  let rowName := Name.str `LowEnergy.ActualCanonical79Imaginary ("currentRow"++toString row)
  let current := mkIdent (if (← getEnv).contains rowName then rowName else
    `LowEnergy.ActualCanonical79Imaginary.primalCurrentPoint)
  let leftIds := #[sparseReadName row false,sparseReadName row true] |>.map mkIdent
  evalTactic (← `(tactic| rw [sparse_current_factor]))
  evalTactic (← `(tactic| simp only [$[$leftIds:ident],*,Fin.sum_univ_succ]))
  evalTactic (← `(tactic| norm_num [sourcePolynomialPoint,ActualCandidateBra.primalPairPoint]))
  evalTactic (← `(tactic| fin_cases $columnId:ident))
  let goals ← getGoals
  for goal in goals do
    setGoals [goal]
    let some (_,_,rhs) := (← goal.getType).eq? | throwError "Expected the same current equality"
    let j := rhs.getAppArgs.back!
    let some jn ← getNatValue? (← whnf (mkApp2 (mkConst ``Fin.val) (mkNatLit 79) j)) |
      throwError "Expected a closed actual current column"
    let readIds := #[sparseReadName row false,sparseReadName row true,
      sparseReadName jn false,sparseReadName jn true] |>.map mkIdent
    evalTactic (← `(tactic| simp only [$[$readIds:ident],*]))
    evalTactic (← `(tactic| norm_num [sourcePolynomialPoint,
      ActualCandidateBra.primalPairPoint,primalCurrentPoint,$current:ident]))
    unless (← getGoals).isEmpty do
      let ids := (← (← getMainGoal).getType).getUsedConstants.filterMap fun name =>
        if name.toString.startsWith "LowEnergy.ActualCandidateBra.pairRow" ||
            name.toString.startsWith "LowEnergy.ActualCandidateBra.pairCoefficient" ||
            name.toString.startsWith "LowEnergy.ActualCanonical79Imaginary.currentCoefficient" then
          some (mkIdent name) else none
      evalTactic (← `(tactic| norm_num [$[$ids:ident],*]))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| try simp only [ActualCandidateBra.sqrt30_factor]))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| try ring_nf))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,
        ActualCandidateBra.sqrt15_square]))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| try ring))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| try simp))
    unless (← getGoals).isEmpty do
      throwError m!"Actual source current row {row} did not close: {← (← getMainGoal).getType}"
  setGoals []
end LowEnergy.ActualCanonical79Imaginary
