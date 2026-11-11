import Mathlib.Tactic
import H0mework.Foundation.Arithmetic.Generation
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawNumberSystemClosureAdapter

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NumberSystemClosureRegression

open ArithmeticIncidence
open ArithmeticGeneration
open ArithmeticProcess
open NumberSystemClosure

theorem two_plus_three_is_generated_parallel_history :
    (UnitInventoryAt.generate 2).parallel (UnitInventoryAt.generate 3) =
      UnitInventoryAt.generate 5 :=
  UnitInventoryAt.parallel_generate 2 3

theorem two_times_three_is_generated_joint_history :
    (UnitInventoryAt.generate 2).joint (UnitInventoryAt.generate 3) =
      UnitInventoryAt.generate 6 :=
  UnitInventoryAt.joint_generate 2 3

theorem two_plus_three_is_parallel_incidence :
    Fintype.card (Fin 5) = Fintype.card (Fin 2) + Fintype.card (Fin 3) :=
  fin_card_add 2 3

theorem two_times_three_is_joint_incidence :
    Fintype.card (Fin 6) = Fintype.card (Fin 2) * Fintype.card (Fin 3) :=
  fin_card_mul 2 3

/-- Six objects cannot be called the disjoint sum of two and three. -/
theorem six_cannot_claim_two_plus_three :
    ParallelIncidenceAt (Fin 6) (Fin 2) (Fin 3) → False :=
  no_parallel_incidence_of_card_ne _ _ _ (by norm_num)

theorem generated_balance_is_negative_three :
    integerBalance 2 5 = -3 := by
  norm_num [integerBalance]

theorem generated_integer_free_closure_is_negative_three :
    integerClosureReadout (integerClosureNode 2 5) = -3 := by
  norm_num [integerClosureReadout_node, integerBalance]

theorem integer_extension_is_generated_process :
    (integerClosureProcess 2 5).history = [.base, .extend] :=
  rfl

theorem every_integer_has_generated_balance (value : Int) :
    ∃ credit debt, integerBalance credit debt = value := by
  rcases integerBalance_surjective value with ⟨⟨credit, debt⟩, generated⟩
  exact ⟨credit, debt, generated⟩

theorem generated_ratio_is_one_half :
    rationalRatio 1 2 (by norm_num) = (1 / 2 : Rat) := by
  rfl

theorem generated_rational_free_closure_is_one_half :
    rationalClosureReadout (rationalClosureNode 1 2 (by norm_num)) =
      (1 / 2 : Rat) := by
  rfl

theorem rational_extension_is_generated_process :
    (rationalClosureProcess 1 2 (by norm_num)).history =
      [.base, .extend] :=
  rfl

theorem every_rational_has_generated_ratio (value : Rat) :
    ∃ numerator denominator denominator_ne_zero,
      rationalRatio numerator denominator denominator_ne_zero = value :=
  rationalRatio_surjective value

theorem generated_constant_lineage_is_three_halves :
    (constantRationalCauchyLaw (3 / 2)).realValue = (3 / 2 : Real) := by
  rw [constantRationalCauchyLaw_realValue]
  norm_num

theorem generated_real_free_closure_is_three_halves :
    realClosureReadout
        (realClosureNode (constantRationalCauchyLaw (3 / 2))) =
      (3 / 2 : Real) := by
  rw [realClosureReadout_node, constantRationalCauchyLaw_realValue]
  norm_num

theorem real_completion_is_generated_process :
    (realClosureProcess (constantRationalCauchyLaw (3 / 2))).history =
      [.base, .extend] :=
  rfl

theorem canonical_complex_rotation_is_unique :
    rotationExtension Complex.I Complex.I_mul_I = AlgHom.id Real Complex :=
  Complex.liftAux_I

theorem generated_complex_free_closure_has_expected_coordinates :
    complexClosureReadout (complexClosureNode 2 3) =
      Complex.ofReal 2 + Complex.ofReal 3 * Complex.I :=
  rfl

theorem complex_rotation_is_generated_process :
    (complexClosureProcess 2 3).history = [.base, .extend] :=
  rfl

/-- The Cauchy carrier cannot be built by filling a completed sequence field;
the only public constructor accepts a seed, local recurrence and its law. -/
theorem caller_cannot_fill_completed_rational_lineage : True := by
  have constant_cauchy :
      IsCauSeq (abs : Rat → Rat)
        (rationalLineageAt 0 (fun _index _prior => 0)) :=
    (constantRationalCauchyLaw 0).cauchy
  fail_if_success
    exact (⟨0, fun _index _prior => 0, constant_cauchy⟩ :
      SourceGeneratedRationalCauchyLaw)
  trivial

#print axioms ArithmeticGeneration.UnitInventoryAt.parallel_generate
#print axioms ArithmeticGeneration.UnitInventoryAt.joint_generate
#print axioms ArithmeticGeneration.UnitInventoryAt.unique
#print axioms ArithmeticIncidence.card_eq_add_of_parallel
#print axioms ArithmeticIncidence.card_eq_mul_of_joint
#print axioms ArithmeticIncidence.no_parallel_incidence_of_card_ne
#print axioms NumberSystemClosure.naturalEmbedding_unique
#print axioms NumberSystemClosure.integerEmbedding_unique
#print axioms NumberSystemClosure.rationalEmbedding_unique
#print axioms NumberSystemClosure.integerBalance_surjective
#print axioms NumberSystemClosure.integerClosureReadout_node
#print axioms NumberSystemClosure.integerBalance_eq_iff
#print axioms NumberSystemClosure.rationalRatio_surjective
#print axioms NumberSystemClosure.rationalClosureReadout_node
#print axioms NumberSystemClosure.rationalRatio_eq_iff_cross
#print axioms NumberSystemClosure.SourceGeneratedRationalCauchyLaw.generatedAt_succ
#print axioms NumberSystemClosure.constantRationalCauchyLaw_realValue
#print axioms NumberSystemClosure.realClosureReadout_node
#print axioms NumberSystemClosure.rotationExtension_unique
#print axioms NumberSystemClosure.complexClosureReadout_surjective
#print axioms integer_extension_is_generated_process
#print axioms rational_extension_is_generated_process
#print axioms real_completion_is_generated_process
#print axioms complex_rotation_is_generated_process
#print axioms six_cannot_claim_two_plus_three

end NumberSystemClosureRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
