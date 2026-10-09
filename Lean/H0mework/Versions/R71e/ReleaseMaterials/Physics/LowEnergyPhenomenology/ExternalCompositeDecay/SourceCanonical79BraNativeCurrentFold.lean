import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraCurrentFastFold
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79NativeSourceRows
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79SourcePolynomialLiterals
import Lean.Meta.Tactic.Rewrite
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators
open Lean Meta Elab Tactic

private def nativeReadName (row : Nat) (weights : Bool) : Name :=
  let moduleName := if row = 0 then "SourceCanonical79SourceSparsePilot" else
    "SourceCanonical79SourceSparseRows" ++ toString (row/16)
  let ns := Name.str (Name.str (Name.num (Name.append `_private ("H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay." ++ moduleName).toName) 0)
    "LowEnergy") "ActualCanonical79Imaginary"
  Name.str ns ((if weights then "weights" else "fields") ++ toString row)

private def nativeRewriteFunction (proof : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let r ← goal.rewrite (← goal.getType) proof (config := { transparency := .default })
  let next ← goal.replaceTargetEq r.eNew r.eqProof
  setGoals (next :: r.mvarIds)

private def nativeRewriteReads (row : Nat) (negative : Bool) : TacticM Unit := do
  let fp ← mkConstWithFreshMVarLevels (nativeReadName row false)
  nativeRewriteFunction (← mkAppM ``funext #[fp])
  let wp ← mkConstWithFreshMVarLevels (nativeReadName row true)
  let v := mkApp (mkConst ``polynomialLiteral)
    (mkConst (if negative then ``Bool.true else ``Bool.false))
  nativeRewriteFunction (← mkAppM ``funext #[mkApp wp v])

private def nativeRewritePolynomials : TacticM Unit := do
  for negative in [true,false] do
    let b := mkConst (if negative then ``Bool.true else ``Bool.false)
    nativeRewriteFunction (← mkAppM ``actual_source_polynomial_literal #[b])

private def nativeExpandCoefficients : TacticM Unit := do
  unless (← getGoals).isEmpty do
    let ids := (← (← getMainGoal).getType).getUsedConstants.filterMap fun name =>
      if name.toString.startsWith "LowEnergy.ActualCandidateBra.pairRow" ||
          name.toString.startsWith "LowEnergy.ActualCandidateBra.pairCoefficient" ||
          name.toString.startsWith "LowEnergy.ActualCanonical79Imaginary.currentCoefficient" then
        some (mkIdent name) else none
    unless ids.isEmpty do evalTactic (← `(tactic| norm_num [$[$ids:ident],*]))

/-- Close only native-left/heavy-right entries. Native-right entries use the
separate delta-source and literal-data identity. -/
elab "reduce_bra_native_heavy_row" index:num : tactic => withMainContext do
  let row := index.getNat
  unless row < 48 do throwError "Expected a native source row"
  let some (_,_,rhs) := (← (← getMainGoal).getType).eq? |
    throwError "Expected the native current-row equality"
  let column := rhs.getAppArgs.back!
  unless column.isFVar do throwError "Expected the free source-column index"
  let columnId := mkIdent (← column.fvarId!.getDecl).userName
  let rowName := Name.str `LowEnergy.ActualCanonical79Imaginary ("currentRow"++toString row)
  let current := mkIdent (if (← getEnv).contains rowName then rowName else
    `LowEnergy.ActualCanonical79Imaginary.primalCurrentPoint)
  evalTactic (← `(tactic| rw [sparse_current_factor]))
  nativeRewritePolynomials
  nativeRewriteReads row true
  evalTactic (← `(tactic| simp only [Fin.sum_univ_succ]))
  evalTactic (← `(tactic| norm_num [polynomialLiteral,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]))
  evalTactic (← `(tactic| fin_cases $columnId:ident))
  let goals ← getGoals
  let mut pending : List MVarId := []
  for goal in goals do
    setGoals [goal]
    evalTactic (← `(tactic| try omega))
    unless (← getGoals).isEmpty do
      let some (_,_,r) := (← (← getMainGoal).getType).eq? |
        throwError "Expected the same native current equality"
      let j := r.getAppArgs.back!
      let some jn ← getNatValue? (← whnf (mkApp2 (mkConst ``Fin.val) (mkNatLit 79) j)) |
        throwError "Expected a closed current column"
      nativeRewriteReads jn false
      evalTactic (← `(tactic| norm_num [polynomialLiteral,Matrix.cons_val_zero,
        Matrix.cons_val_succ,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
        ActualCandidateBra.primalPairPoint,primalCurrentPoint,$current:ident]))
      nativeExpandCoefficients
      nativeExpandCoefficients
      nativeExpandCoefficients
      pending := pending ++ (← getGoals)
  setGoals pending

elab "reduce_bra_native_closed" row:num column:num : tactic => withMainContext do
  let i := row.getNat
  let j := column.getNat
  unless i < 48 && j < 79 do throwError "Expected a closed native source entry"
  let rowName := Name.str `LowEnergy.ActualCanonical79Imaginary ("currentRow"++toString i)
  let current := mkIdent (if (← getEnv).contains rowName then rowName else
    `LowEnergy.ActualCanonical79Imaginary.primalCurrentPoint)
  evalTactic (← `(tactic| rw [sparse_current_factor]))
  nativeRewritePolynomials
  nativeRewriteReads i true
  nativeRewriteReads j false
  evalTactic (← `(tactic| norm_num [Fin.sum_univ_succ,polynomialLiteral,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons,ActualCandidateBra.primalPairPoint,
    primalCurrentPoint,$current:ident]))
  nativeExpandCoefficients
  nativeExpandCoefficients
  nativeExpandCoefficients


macro "eval_bra_native_heavy_row" index:num : tactic =>
  `(tactic| (
    reduce_bra_native_heavy_row $index
    all_goals
      try norm_num [Matrix.cons_val_zero,Matrix.cons_val_succ]
      try simp only [ActualCandidateBra.sqrt30_factor]
      ring_nf! <;>
        norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,
          ActualCandidateBra.sqrt15_square] <;> ring!))

macro "eval_bra_native_closed" row:num column:num : tactic =>
  `(tactic| (
    reduce_bra_native_closed $row $column
    all_goals
      try simp only [ActualCandidateBra.sqrt30_factor]
      ring_nf! <;>
        norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,
          ActualCandidateBra.sqrt15_square] <;> ring!))

end LowEnergy.ActualCanonical79Imaginary
