import H0mework.Physics.Bell.RealFamily
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Strict real-family audit and independent synthetic controls; no empirical data. -/

set_option autoImplicit false

open Lean Elab Command

private partial def realClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then realClosure env rest seen
    else
      let children := match env.checked.get.find? name with
        | some info => info.getUsedConstantsAsSet.toArray.toList
        | none => []
      realClosure env (children ++ rest) (seen.insert name)

open SaturationMonoid.PhysicsCore Stage10.Bell

run_cmd do
  let env ← getEnv
  let root := ``RealFamily.prediction
  let some info := env.checked.get.find? root | throwError "MISSING_MOUTH"
  if info.type.isForall then throwError "CALLER_PARAMETER"
  let closure := realClosure env [root]
  let required := [``RealFamily.vector, ``RealFamily.vector_normalized, ``RealFamily.joint_born,
    ``RealFamily.born, ``RealFamily.nonnegative, ``RealFamily.le_one, ``RealFamily.normalized,
    ``RealFamily.left_marginal, ``RealFamily.right_marginal, ``RealFamily.correlation,
    ``RealFamily.left_mean, ``RealFamily.right_mean, ``RealFamily.shape,
    ``RealFamily.phi_reduction, ``RealFamily.legacy_frame, ``jointEffect,
    ``Stage9DEF.State.vectorEvaluation_positive]
  for name in required do
    unless closure.contains name do throwError "MISSING_PRODUCER {name}"
  let nsPrefix := "SaturationMonoid.PhysicsCore.Stage10.Bell.RealFamily."
  let declarations := env.constants.toList.filter fun (n, _) =>
    nsPrefix.isPrefixOf (privateToUserName n).toString
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_AXIOMS {name}: {axioms}"
  let primitive := realClosure env [``RealFamily.vector, ``RealFamily.delta, ``RealFamily.chi]
  for name in [``RealFamily.probability, ``RealFamily.prediction, ``Stage9DEF.Source.vector,
      ``Stage10.Runtime.tick, ``probability] do
    if primitive.contains name then throwError "TARGET_OR_RUNTIME_IN_PREPARATION {name}"
  let prior := realClosure env [``deterministicPreparationPrediction,
    ``Stage10.Runtime.sameOccurrenceActivation, ``Stage10.Recovery.stageOneThroughTenClosure]
  for name in prior.toArray do
    if nsPrefix.isPrefixOf (privateToUserName name).toString then
      throwError "OLD_CHAIN_REVERSE_DEPENDENCY {name}"
  let axioms ← collectAxioms root
  logInfo m!"REAL_FAMILY_CERTIFIED declarations={declarations.length} nodes={closure.size} required={required.length} axioms={axioms}"
  logInfo m!"REAL_FAMILY_FIREWALL primitive={primitive.size} old_chain={prior.size}"

namespace RealFamilyIndependentControls
open Matrix Stage9DEF State
noncomputable section
private def z : Axis := ⟨0, 1, by norm_num⟩
private def x : Axis := ⟨1, 0, by norm_num⟩
private def uneven : RealFamily.Preparation := ⟨3/5, 4/5, by norm_num⟩
private def product : RealFamily.Preparation := ⟨1, 0, by norm_num⟩
private def negative : RealFamily.Preparation := ⟨3/5, -4/5, by norm_num⟩
private def maximal : RealFamily.Preparation :=
  ⟨Real.sqrt (1/2), Real.sqrt (1/2), by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1/2 by norm_num)]⟩

example : Fintype.card Source.Index = 8 := by decide
example : RealFamily.vector uneven (0, 0) = (3/5 : ℂ) := by
  norm_num [RealFamily.vector, uneven]
example : RealFamily.vector uneven (1, 1) = (4/5 : ℂ) := by
  norm_num [RealFamily.vector, uneven]
example : RealFamily.vector uneven (2, 0) = 0 := by
  simp only [RealFamily.vector,
    if_neg (by decide : ((2, 0) : Source.Index) ≠ (0, 0)),
    if_neg (by decide : ((2, 0) : Source.Index) ≠ (1, 1))]
example : RealFamily.probability uneven z z false false = 9/25 := by
  norm_num [RealFamily.probability, RealFamily.delta, RealFamily.chi, uneven, z, sign]
example : (∑ y : Bool, RealFamily.probability uneven z x false y) ≠ 1/2 := by
  rw [RealFamily.left_marginal]
  norm_num [RealFamily.delta, uneven, z, sign]
example : RealFamily.probability product x x false false = 1/4 := by
  norm_num [RealFamily.probability, RealFamily.delta, RealFamily.chi, product, x, sign]
example : RealFamily.probability negative x x false false = 1/100 := by
  norm_num [RealFamily.probability, RealFamily.delta, RealFamily.chi, negative, x, sign]
example (a b : Axis) (u v : Bool) :
    RealFamily.probability maximal a b u v =
      probability a (heraldAxis true (colorXFrame b)) u v :=
  RealFamily.prediction.phiReduction maximal rfl a b u v
example (p : RealFamily.Preparation) (a b b' : Axis) (u : Bool) :
    (∑ v : Bool, RealFamily.probability p a b u v) =
      ∑ v : Bool, RealFamily.probability p a b' u v := by
  rw [RealFamily.prediction.leftMarginal, RealFamily.prediction.leftMarginal]

end
end RealFamilyIndependentControls
