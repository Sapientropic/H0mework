import H0mework.Realization.Operations.BinaryInputs
import H0mework.Versions.R2.Arithmetic.UnitArithmetic.Root
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-! Complete correlated input and independently updated slots are mathematical
controls of the raw history operation, without assigning source authority to a
selected linear combination. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeBinary.Controls

open ArithmeticGeneration SourceOperationEffects

noncomputable section

abbrev H := UnitHistory
def base : H := CanonicalUnitArithmeticRoot.unitHistory
def doubled : H := base.parallel base

def correlated : Free (H × H) :=
  Finsupp.single (base, base) 1 + Finsupp.single (doubled, doubled) 1

def marginal : Free H := Finsupp.single base 1 + Finsupp.single doubled 1

theorem correlated_inventory_retains_joint_inputs :
    Finsupp.lmapDomain ℤ ℤ Prod.fst correlated = marginal ∧
      Finsupp.lmapDomain ℤ ℤ Prod.snd correlated = marginal ∧
      pushJoint UnitHistory.parallel correlated =
        Finsupp.single (base.parallel base) 1 + Finsupp.single (doubled.parallel doubled) 1 ∧
      pushJoint UnitHistory.parallel correlated (base.parallel doubled) = 0 ∧
      pushJoint UnitHistory.parallel (joint marginal marginal) (base.parallel doubled) = 2 := by
  have complete : pushJoint UnitHistory.parallel correlated =
      Finsupp.single (base.parallel base) 1 + Finsupp.single (doubled.parallel doubled) 1 := by
    simp only [correlated, map_add, pushJoint_point]
  refine ⟨?_, ?_, complete, ?_, ?_⟩
  · simp only [correlated, marginal, map_add, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]
  · simp only [correlated, marginal, map_add, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]
  · rw [complete]
    norm_num [base, doubled, CanonicalUnitArithmeticRoot.unitHistory, UnitHistory.parallel,
      Finsupp.single_apply]
    decide
  · simp only [marginal, map_add, LinearMap.add_apply, joint_point, pushJoint_point]
    norm_num [base, doubled, CanonicalUnitArithmeticRoot.unitHistory, UnitHistory.parallel,
      Finsupp.single_apply]
    decide

def leftIncrement : Env (Value H H H) (Var H H H)
  | .left, value => Finsupp.single (value.parallel base) 1 - Finsupp.single value 1
  | .right, _ => 0
  | .result, _ => 0

def rightIncrement : Env (Value H H H) (Var H H H)
  | .left, _ => 0
  | .right, value => Finsupp.single (value.parallel doubled) 1 - Finsupp.single value 1
  | .result, _ => 0

theorem same_value_slots_keep_independent_and_joint_updates :
    leftIncrement .right base = 0 ∧ rightIncrement .left base = 0 ∧
      (expression UnitHistory.parallel base base).eval (environment + leftIncrement) =
        Finsupp.single (doubled.parallel base) 1 ∧
      (expression UnitHistory.parallel base base).eval (environment + rightIncrement) =
        Finsupp.single (base.parallel (base.parallel doubled)) 1 ∧
      (expression UnitHistory.parallel base base).eval
          (environment + (leftIncrement + rightIncrement)) =
        Finsupp.single (doubled.parallel (base.parallel doubled)) 1 ∧
      lift UnitHistory.parallel (leftIncrement .left base) (rightIncrement .right base) ≠ 0 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [expression_mixed_update]
    simp only [leftIncrement, map_zero, map_sub, AddMonoidHom.sub_apply, lift_point, doubled]
    abel
  · rw [expression_mixed_update]
    simp only [rightIncrement, map_zero, map_sub, lift_point]
    abel
  · rw [expression_mixed_update]
    simp only [Pi.add_apply, leftIncrement, rightIncrement, zero_add, add_zero, map_sub,
      AddMonoidHom.sub_apply, lift_point, doubled]
    abel
  · have coefficient :
        lift UnitHistory.parallel (leftIncrement .left base) (rightIncrement .right base)
          (doubled.parallel (base.parallel doubled)) = 1 := by
      simp only [leftIncrement, rightIncrement, map_sub, AddMonoidHom.sub_apply, lift_point]
      norm_num [base, doubled, CanonicalUnitArithmeticRoot.unitHistory, UnitHistory.parallel,
        Finsupp.single_apply]
      decide
    intro killed
    have erased := congrArg
      (fun value : Free H => value (doubled.parallel (base.parallel doubled))) killed
    rw [coefficient] at erased
    exact one_ne_zero erased

end

end SourceNativeBinary.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
