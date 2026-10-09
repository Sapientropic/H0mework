import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79ImaginaryNumeratorData
import Lean.Elab.Tactic
import Lean.Util.FoldConsts
set_option autoImplicit false
namespace LowEnergy.ActualCanonical79Imaginary
open Lean Meta Elab Tactic

/-- Select the actual return vector entry while retaining its original let
bindings. Removing an unused let is definitional zeta reduction. -/
private partial def selectReturn (index : Nat) (body : Expr) : MetaM Expr := do
  match body with
  | .letE name type value rest nonDep =>
      let rest ← selectReturn index rest
      if rest.hasLooseBVar 0 then return .letE name type value rest nonDep
      else return rest.lowerLooseBVars 1 1
  | _ =>
      unless body.getAppFn.constName? = some ``Matrix.vecCons do
        throwError "Unexpected original numerator return: {body.getAppFn.constName?}"
      let arguments := body.getAppArgs
      unless arguments.size = 5 do throwError "Unexpected original return vector arity"
      let mut vector := body.appFn!
      for _ in [:index] do
        let arguments := vector.getAppArgs
        unless vector.getAppFn.constName? = some ``Matrix.vecCons && arguments.size = 4 do
          throwError "Original numerator vector is shorter than its index"
        vector := arguments[3]!
      let arguments := vector.getAppArgs
      unless vector.getAppFn.constName? = some ``Matrix.vecCons && arguments.size = 4 do
        throwError "The original numerator entry is missing"
      return arguments[2]!

private def arithmetic (current target : Expr) : TacticM Expr := do
  let proof ← mkFreshExprMVar (← mkEq current target)
  let saved ← getGoals
  setGoals [proof.mvarId!]
  let values := (← (← getMainGoal).getType).getUsedConstants.filterMap fun name =>
    if name.toString.startsWith "LowEnergy.ActualCanonical79Imaginary.group" &&
        name.toString.endsWith "Value" then some (mkIdent name) else none
  evalTactic (← `(tactic| norm_num [$[$values:ident],*, numeratorPoint,
    numeratorValue0, numeratorValue1, numeratorValue2, numeratorValue3, numeratorValue4]))
  unless (← getGoals).isEmpty do
    let ids := (← (← getMainGoal).getType).getUsedConstants.filterMap fun name =>
      if name.toString.startsWith "LowEnergy.ActualCanonical79Imaginary.nodeCoefficient" ||
          name.toString.startsWith "LowEnergy.ActualCanonical79Imaginary.numeratorCoefficient" then
        some (mkIdent name) else none
    evalTactic (← `(tactic| norm_num [$[$ids:ident],*, Complex.I_sq, Complex.I_mul_I]))
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| ring_nf))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| simp only [Complex.I_pow_eq_pow_mod', Nat.reduceMod,
      pow_zero, pow_one, Complex.I_sq, Complex.I_pow_three]))
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| norm_num [Complex.I_sq, Complex.I_mul_I]))
  unless (← getGoals).isEmpty do
    throwError m!"Original numerator arithmetic did not close: {← (← getMainGoal).getType}"
  setGoals saved
  instantiateMVars proof

private partial def foldGroups (resultType current target : Expr) : TacticM Expr := do
  match current with
  | .letE name type value body _ =>
      let text := name.toString
      unless text.startsWith "g" do throwError "Unexpected original numerator binding"
      let some group := (text.drop 1).toString.toNat? | throwError "Unknown original group"
      let point := mkConst (Name.str `LowEnergy.ActualCanonical79Imaginary
        ("group"++toString group++"Value"))
      let proof := mkConst (Name.str `LowEnergy.ActualCanonical79Imaginary
        ("actual_group"++toString group++"_point"))
      let next := body.instantiate1 point
      let u ← getLevel type
      let v ← getLevel resultType
      let step := mkApp6 (mkConst ``congrArg [u,v]) type resultType value point
        (.lam name type body .default) proof
      let rest ← foldGroups resultType next target
      return mkApp6 (mkConst ``Eq.trans [v]) resultType current next target step rest
  | _ => arithmetic current target

/-- Every generated equality is between the original selected numerator and
its point data; both vector selection and unused-binding pruning are checked
by the kernel against the unmodified original source definition. -/
elab "eval_canonical_numerator" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (resultType,left,right) := target.eq? | throwError "Expected an original numerator point equality"
  unless left.getAppFn.constName? = some ``MixedSpectatorCanonical79Data.numeratorPolynomial do
    throwError "The goal does not read the original numerator"
  let arguments := left.getAppArgs
  unless arguments.size = 3 do throwError "Expected the original full numerator application"
  let indexValue ← whnf (← mkAppM ``Fin.val #[arguments[2]!])
  let some index ← getNatValue? indexValue | throwError "Expected a literal original numerator index"
  unless index < 526 do throwError "Original numerator index out of range"
  let info ← getConstInfo ``MixedSpectatorCanonical79Data.numeratorPolynomial
  let some source := info.value? | throwError "Original numerator definition is missing"
  let selected ← selectReturn index (source.beta arguments)
  let proof ← foldGroups resultType selected right
  goal.assign proof
  replaceMainGoal []
end LowEnergy.ActualCanonical79Imaginary
