import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraCurrentFastFold
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79SourcePolynomialLiterals
import Lean.Meta.Tactic.Rewrite
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators

open Lean Meta Elab Tactic
private def sparseReadName (row : Nat) (weights : Bool) : Name :=
  let moduleName := if row = 0 then "SourceCanonical79SourceSparsePilot" else
    "SourceCanonical79SourceSparseRows" ++ toString (row/16)
  let ns := Name.str (Name.str (Name.num (Name.append `_private ("H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic." ++ moduleName).toName) 0)
    "LowEnergy") "ActualCanonical79Imaginary"
  Name.str ns ((if weights then "weights" else "fields") ++ toString row)

private def rewriteCurrentFunction (proof : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let r ← goal.rewrite (← goal.getType) proof (config := { transparency := .default })
  let next ← goal.replaceTargetEq r.eNew r.eqProof
  setGoals (next :: r.mvarIds)

private def rewriteCurrentReads (row : Nat) (negative : Bool) : TacticM Unit := do
  let fp ← mkConstWithFreshMVarLevels (sparseReadName row false)
  rewriteCurrentFunction (← mkAppM ``funext #[fp])
  let wp ← mkConstWithFreshMVarLevels (sparseReadName row true)
  let v := mkApp (mkConst ``sourcePolynomialPoint) (mkConst (if negative then ``Bool.true else ``Bool.false))
  rewriteCurrentFunction (← mkAppM ``funext #[mkApp wp v])
  if (← (← getMainGoal).getType).getUsedConstants.contains ``sourcePolynomialPoint then
    rewriteCurrentFunction (mkApp (mkConst ``actual_source_polynomial_literal)
      (mkConst (if negative then ``Bool.true else ``Bool.false)))

elab "eval_bra_current_entry" rowIndex:num columnIndex:num : tactic => withMainContext do
  let row := rowIndex.getNat
  let jn := columnIndex.getNat
  let rowName := Name.str `LowEnergy.ActualCanonical79Imaginary ("currentRow"++toString row)
  let current := mkIdent (if (← getEnv).contains rowName then rowName else
    `LowEnergy.ActualCanonical79Imaginary.primalCurrentPoint)
  evalTactic (← `(tactic| rw [sparse_current_factor]))
  rewriteCurrentReads row true
  rewriteCurrentReads jn false
  evalTactic (← `(tactic| norm_num [Fin.sum_univ_succ,polynomialLiteral,
    ActualCandidateBra.primalPairPoint,primalCurrentPoint,$current:ident,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons]))
  for _ in [:3] do
    unless (← getGoals).isEmpty do
      let ids := (← (← getMainGoal).getType).getUsedConstants.filterMap fun name =>
        if name.toString.startsWith "LowEnergy.ActualCandidateBra.pairRow" ||
            name.toString.startsWith "LowEnergy.ActualCandidateBra.pairCoefficient" ||
            name.toString.startsWith "LowEnergy.ActualCanonical79Imaginary.currentCoefficient" then
          some (mkIdent name) else none
      evalTactic (← `(tactic| norm_num [$[$ids:ident],*]))

elab "eval_bra_current_row_functions" index:num : tactic => withMainContext do
  let row := index.getNat
  let initial ← (← getMainGoal).getType
  let some (_,_,right) := initial.eq? | throwError "Expected an actual current-row equality"
  let column := right.getAppArgs.back!
  unless column.isFVar do throwError "Expected the actual free source-column index"
  let columnId := mkIdent (← column.fvarId!.getDecl).userName
  let rowName := Name.str `LowEnergy.ActualCanonical79Imaginary ("currentRow"++toString row)
  let current := mkIdent (if (← getEnv).contains rowName then rowName else
    `LowEnergy.ActualCanonical79Imaginary.primalCurrentPoint)
  evalTactic (← `(tactic| rw [sparse_current_factor]))
  rewriteCurrentReads row true
  evalTactic (← `(tactic| simp only [Fin.sum_univ_succ]))
  evalTactic (← `(tactic| norm_num [polynomialLiteral,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]))
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| fin_cases $columnId:ident))
  let goals ← getGoals
  let mut residuals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    let some (_,_,rhs) := (← goal.getType).eq? | throwError "Expected the same current equality"
    let j := rhs.getAppArgs.back!
    let some jn ← getNatValue? (← whnf (mkApp2 (mkConst ``Fin.val) (mkNatLit 79) j)) |
      throwError "Expected a closed actual current column"
    rewriteCurrentReads jn false
    evalTactic (← `(tactic| norm_num [polynomialLiteral,
      ActualCandidateBra.primalPairPoint,primalCurrentPoint,$current:ident,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]))
    for _ in [:3] do
     unless (← getGoals).isEmpty do
      let ids := (← (← getMainGoal).getType).getUsedConstants.filterMap fun name =>
        if name.toString.startsWith "LowEnergy.ActualCandidateBra.pairRow" ||
            name.toString.startsWith "LowEnergy.ActualCandidateBra.pairCoefficient" ||
            name.toString.startsWith "LowEnergy.ActualCanonical79Imaginary.currentCoefficient" then
          some (mkIdent name) else none
      evalTactic (← `(tactic| norm_num [$[$ids:ident],*]))
    residuals := residuals ++ (← getUnsolvedGoals)
  setGoals residuals
end LowEnergy.ActualCanonical79Imaginary
