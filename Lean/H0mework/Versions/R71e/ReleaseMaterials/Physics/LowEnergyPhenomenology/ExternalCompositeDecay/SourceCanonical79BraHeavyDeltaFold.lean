import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNativeRightRead
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraCurrentRadicalPowers
import Lean.Meta.Tactic.Rewrite
import Lean.Util.FoldConsts
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators
open Lean Meta Elab Tactic

private def deltaReadName (row : Nat) (weights : Bool) : Name :=
  let moduleName := if row = 0 then "SourceCanonical79SourceSparsePilot" else
    "SourceCanonical79SourceSparseRows" ++ toString (row/16)
  let ns := Name.str (Name.str (Name.num (Name.append `_private ("H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay." ++ moduleName).toName) 0)
    "LowEnergy") "ActualCanonical79Imaginary"
  Name.str ns ((if weights then "weights" else "fields") ++ toString row)

private def deltaRewriteFunction (proof : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let r ← goal.rewrite (← goal.getType) proof (config := { transparency := .default })
  let next ← goal.replaceTargetEq r.eNew r.eqProof
  setGoals (next :: r.mvarIds)

private def deltaRewriteReads (row : Nat) (negative : Bool) : TacticM Unit := do
  let fp ← mkConstWithFreshMVarLevels (deltaReadName row false)
  deltaRewriteFunction (← mkAppM ``funext #[fp])
  let wp ← mkConstWithFreshMVarLevels (deltaReadName row true)
  let v := mkApp (mkConst ``sourcePolynomialPoint) (mkConst (if negative then ``Bool.true else ``Bool.false))
  deltaRewriteFunction (← mkAppM ``funext #[mkApp wp v])
  if (← (← getMainGoal).getType).getUsedConstants.contains ``sourcePolynomialPoint then
    deltaRewriteFunction (mkApp (mkConst ``actual_source_polynomial_literal)
      (mkConst (if negative then ``Bool.true else ``Bool.false)))

private def deltaParseCurrent (row : Nat) : TacticM Unit := do
  let rowName := Name.str `LowEnergy.ActualCanonical79Imaginary ("currentRow"++toString row)
  let current := mkIdent (if (← getEnv).contains rowName then rowName else
    `LowEnergy.ActualCanonical79Imaginary.primalCurrentPoint)
  evalTactic (← `(tactic| norm_num [sourceIndex97,nativeIndex79,polynomialLiteral,
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

elab "eval_heavy_native_current" index:num : tactic => withMainContext do
  let row := index.getNat
  let some (_,_,rhs) := (← (← getMainGoal).getType).eq? | throwError "Expected current equality"
  let j := rhs.getAppArgs.back!
  unless j.getAppFn.isConstOf ``nativeIndex79 do throwError "Expected actual native restriction"
  let n := j.getAppArgs.back!
  unless n.isFVar do throwError "Expected actual native free index"
  let nId := mkIdent (← n.fvarId!.getDecl).userName
  evalTactic (← `(tactic| rw [sparse_current_native_right]))
  deltaRewriteReads row true
  evalTactic (← `(tactic| simp only [Fin.sum_univ_succ]))
  evalTactic (← `(tactic| norm_num [polynomialLiteral,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]))
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| fin_cases $nId:ident))
  let goals ← getGoals
  let mut residuals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    withMainContext do deltaParseCurrent row
    residuals := residuals ++ (← getUnsolvedGoals)
  setGoals residuals

elab "eval_heavy_heavy_current" index:num : tactic => withMainContext do
  let row := index.getNat
  let some (_,_,rhs) := (← (← getMainGoal).getType).eq? | throwError "Expected current equality"
  let j := rhs.getAppArgs.back!
  unless j.isFVar do throwError "Expected actual free heavy column"
  let jId := mkIdent (← j.fvarId!.getDecl).userName
  evalTactic (← `(tactic| rw [sparse_current_factor]))
  deltaRewriteReads row true
  evalTactic (← `(tactic| simp only [Fin.sum_univ_succ]))
  evalTactic (← `(tactic| norm_num [polynomialLiteral,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]))
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| fin_cases $jId:ident))
  let goals ← getGoals
  let mut residuals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    withMainContext do
      evalTactic (← `(tactic| try omega))
      unless (← getGoals).isEmpty do
        let some (_,_,rhs) := (← (← getMainGoal).getType).eq? | throwError "Expected current equality"
        let cj := rhs.getAppArgs.back!
        let some jn ← getNatValue? (← whnf (mkApp2 (mkConst ``Fin.val) (mkNatLit 79) cj)) |
          throwError "Expected closed heavy index"
        deltaRewriteReads jn false
        deltaParseCurrent row
    residuals := residuals ++ (← getUnsolvedGoals)
  setGoals residuals

end LowEnergy.ActualCanonical79Imaginary
