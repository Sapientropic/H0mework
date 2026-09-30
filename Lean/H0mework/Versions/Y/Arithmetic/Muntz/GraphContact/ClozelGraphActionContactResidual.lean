import H0mework.Versions.Y.Arithmetic.Muntz.FunctionalGraphAction
import H0mework.Versions.Y.Arithmetic.Muntz.CoPoissonLogContact

/-!
# Exact graph-action residual for the A1c weighted contact

The actual nonzero Mellin shell identifies the graph action's norm residual
with failure of the endpoint-weighted co-Poisson contact.  This is a total
representation statement: it does not assert that the residual vanishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex MeasureTheory
open ClozelEndpointSourceEffect
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open QRich
open SourceGeneratedFunctionalGraphPerfectification
open scoped SchwartzMap

noncomputable section

abbrev WeightedCoPoissonContact
    (observation : GeneratedRiemannZeroObservation) :=
  ∀ test : SchwartzMap ℝ ℂ,
    (observation.coordinate -
        coordinateReversal observation.coordinate) *
      coPoissonLogOrbitMap test 0 = 0

abbrev QuarterGraphActionResidualFibre
    (observation : GeneratedRiemannZeroObservation) :=
  {value : QuarterMellinL2Test (observation.coordinate / 2) //
    graphActionNormResidual
      (zeroOwnedQuarterGraphCovariance observation) value ≠ 0}

def selectedQuarterNoGoShellTest
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test (observation.coordinate / 2) :=
  ⟨positiveMellinQuarterNoGoShell,
    ⟨positiveMellinQuarterNoGoShellL2.2,
      (positiveMellinQuarterNoGoShellElement
        (observation.coordinate / 2)
        (selectedPositiveParameter_re_pos observation nontrivial)).2⟩⟩

theorem selectedQuarterNoGoShellTest_functional_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Functional (observation.coordinate / 2)
        (selectedQuarterNoGoShellTest observation nontrivial) ≠ 0 := by
  change positiveMellinFunctional (observation.coordinate / 2)
      (positiveMellinQuarterNoGoShellElement
        (observation.coordinate / 2)
        (selectedPositiveParameter_re_pos observation nontrivial)) ≠ 0
  exact positiveMellinQuarterNoGoShellElement_value_ne_zero
    (observation.coordinate / 2)
    (selectedPositiveParameter_re_pos observation nontrivial)

theorem quarterGraph_character_norm_one_of_shell_residual_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (residualZero : graphActionNormResidual
      (zeroOwnedQuarterGraphCovariance observation)
      (selectedQuarterNoGoShellTest observation nontrivial) = 0) :
    ‖(positiveMellinQuarterNoGoScale : ℂ) ^
        ((1 / 4 : ℂ) - observation.coordinate / 2)‖ = 1 := by
  let test := selectedQuarterNoGoShellTest observation nontrivial
  let feature := quarterMellinL2Feature (observation.coordinate / 2)
  let functional := quarterMellinL2Functional (observation.coordinate / 2)
  let covariance := zeroOwnedQuarterGraphCovariance observation
  let character : ℂ := (positiveMellinQuarterNoGoScale : ℂ) ^
    ((1 / 4 : ℂ) - observation.coordinate / 2)
  have graphNorm := sub_eq_zero.mp residualZero
  have graphNormSq := congrArg (fun normValue : ℝ => normValue ^ 2) graphNorm
  rw [WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2] at graphNormSq
  change
      ‖feature (covariance.sourceAction test)‖ ^ 2 +
          ‖functional (covariance.sourceAction test)‖ ^ 2 =
        ‖feature test‖ ^ 2 + ‖functional test‖ ^ 2 at graphNormSq
  have featureCovariance :=
    LinearMap.congr_fun covariance.feature_covariance test
  change covariance.hilbertAction (feature test) =
    feature (covariance.sourceAction test) at featureCovariance
  have energyNorm :=
    (positiveMellinQuarterEnergyTranslationIsometry
      (Real.log positiveMellinQuarterNoGoScale)).norm_map (feature test)
  have featureNorm :
      ‖feature (covariance.sourceAction test)‖ = ‖feature test‖ := by
    rw [← featureCovariance]
    exact energyNorm
  have functionalCovariance :=
    LinearMap.congr_fun covariance.functional_eigenlaw test
  change functional (covariance.sourceAction test) =
    character • functional test at functionalCovariance
  rw [featureNorm, functionalCovariance, norm_smul] at graphNormSq
  have functionalNe : functional test ≠ 0 :=
    selectedQuarterNoGoShellTest_functional_ne_zero observation nontrivial
  have functionalNormPos : 0 < ‖functional test‖ :=
    norm_pos_iff.mpr functionalNe
  have characterNormNonneg : 0 ≤ ‖character‖ := norm_nonneg _
  have productSquare :
      (‖character‖ * ‖functional test‖) ^ 2 =
        ‖functional test‖ ^ 2 := by
    nlinarith [graphNormSq]
  rw [mul_pow] at productSquare
  have functionalNormSquareNe : ‖functional test‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (ne_of_gt functionalNormPos)
  have characterNormSquare : ‖character‖ ^ 2 = 1 := by
    apply (mul_right_cancel₀ functionalNormSquareNe)
    simpa only [one_mul] using productSquare
  change ‖character‖ = 1
  nlinarith [characterNormSquare]

theorem coordinate_eq_reversal_of_quarterGraph_character_norm_one
    (observation : GeneratedRiemannZeroObservation)
    (characterNorm :
      ‖(positiveMellinQuarterNoGoScale : ℂ) ^
          ((1 / 4 : ℂ) - observation.coordinate / 2)‖ = 1) :
    observation.coordinate = coordinateReversal observation.coordinate := by
  have scaleGreaterThanOne : 1 < positiveMellinQuarterNoGoScale := by
    norm_num [positiveMellinQuarterNoGoScale]
  have scalePositive : 0 < positiveMellinQuarterNoGoScale :=
    lt_trans zero_lt_one scaleGreaterThanOne
  rw [Complex.norm_cpow_eq_rpow_re_of_pos scalePositive] at characterNorm
  have exponentZero :
      ((1 / 4 : ℂ) - observation.coordinate / 2).re = 0 := by
    apply (Real.strictMono_rpow_of_base_gt_one
      scaleGreaterThanOne).injective
    simpa using characterNorm
  have coordinateRealPart : observation.coordinate.re = 1 / 2 := by
    rw [sub_re, div_ofNat_re] at exponentZero
    norm_num at exponentZero ⊢
    linarith
  apply Complex.ext
  · simp [coordinateReversal]
    linarith
  · simp [coordinateReversal]

theorem weightedCoPoissonContact_of_quarterGraph_character_norm_one
    (observation : GeneratedRiemannZeroObservation)
    (characterNorm :
      ‖(positiveMellinQuarterNoGoScale : ℂ) ^
          ((1 / 4 : ℂ) - observation.coordinate / 2)‖ = 1) :
    WeightedCoPoissonContact observation := by
  have fixed := coordinate_eq_reversal_of_quarterGraph_character_norm_one
    observation characterNorm
  have coefficientZero : observation.coordinate -
      coordinateReversal observation.coordinate = 0 :=
    sub_eq_zero.mpr fixed
  intro test
  rw [coefficientZero, zero_mul]

theorem quarterGraph_source_residual_zero_of_character_norm_one
    (observation : GeneratedRiemannZeroObservation)
    (characterNorm :
      ‖(positiveMellinQuarterNoGoScale : ℂ) ^
          ((1 / 4 : ℂ) - observation.coordinate / 2)‖ = 1)
    (value : QuarterMellinL2Test (observation.coordinate / 2)) :
    graphActionNormResidual
        (zeroOwnedQuarterGraphCovariance observation) value = 0 := by
  let feature := quarterMellinL2Feature (observation.coordinate / 2)
  let functional := quarterMellinL2Functional (observation.coordinate / 2)
  let covariance := zeroOwnedQuarterGraphCovariance observation
  let character : ℂ := (positiveMellinQuarterNoGoScale : ℂ) ^
    ((1 / 4 : ℂ) - observation.coordinate / 2)
  apply sub_eq_zero.mpr
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2]
  change
      ‖feature (covariance.sourceAction value)‖ ^ 2 +
          ‖functional (covariance.sourceAction value)‖ ^ 2 =
        ‖feature value‖ ^ 2 + ‖functional value‖ ^ 2
  have featureCovariance :=
    LinearMap.congr_fun covariance.feature_covariance value
  change covariance.hilbertAction (feature value) =
    feature (covariance.sourceAction value) at featureCovariance
  have energyNorm :=
    (positiveMellinQuarterEnergyTranslationIsometry
      (Real.log positiveMellinQuarterNoGoScale)).norm_map (feature value)
  have featureNorm :
      ‖feature (covariance.sourceAction value)‖ = ‖feature value‖ := by
    rw [← featureCovariance]
    exact energyNorm
  have functionalCovariance :=
    LinearMap.congr_fun covariance.functional_eigenlaw value
  change functional (covariance.sourceAction value) =
    character • functional value at functionalCovariance
  rw [featureNorm, functionalCovariance, norm_smul, characterNorm, one_mul]

theorem quarterGraphResidual_nonempty_iff_character_norm_ne_one
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Nonempty (QuarterGraphActionResidualFibre observation) ↔
      ‖(positiveMellinQuarterNoGoScale : ℂ) ^
          ((1 / 4 : ℂ) - observation.coordinate / 2)‖ ≠ 1 := by
  constructor
  · rintro ⟨⟨value, residualNe⟩⟩ characterNorm
    exact residualNe
      (quarterGraph_source_residual_zero_of_character_norm_one
        observation characterNorm value)
  · intro characterNormNe
    exact ⟨⟨selectedQuarterNoGoShellTest observation nontrivial,
      fun residualZero => characterNormNe
        (quarterGraph_character_norm_one_of_shell_residual_zero
          observation nontrivial residualZero)⟩⟩

theorem coordinate_eq_reversal_of_weightedCoPoissonContact
    (observation : GeneratedRiemannZeroObservation)
    (contact : WeightedCoPoissonContact observation) :
    observation.coordinate = coordinateReversal observation.coordinate := by
  apply sub_eq_zero.mp
  exact (mul_eq_zero.mp
    (contact remainderWitnessSchwartz)).resolve_right
      coPoissonLogOrbitMap_witness_ne_zero

theorem quarterGraph_character_norm_one_iff_coordinate_eq_reversal
    (observation : GeneratedRiemannZeroObservation) :
    ‖(positiveMellinQuarterNoGoScale : ℂ) ^
        ((1 / 4 : ℂ) - observation.coordinate / 2)‖ = 1 ↔
      observation.coordinate = coordinateReversal observation.coordinate := by
  constructor
  · exact coordinate_eq_reversal_of_quarterGraph_character_norm_one observation
  · intro fixed
    have realPart := congrArg Complex.re fixed
    have coordinateRealPart : observation.coordinate.re = 1 / 2 := by
      simp [coordinateReversal] at realPart
      linarith
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      positiveMellinQuarterNoGoScale_pos]
    have exponentZero :
        ((1 / 4 : ℂ) - observation.coordinate / 2).re = 0 := by
      rw [sub_re, div_ofNat_re]
      norm_num
      linarith
    rw [exponentZero, Real.rpow_zero]

theorem weightedCoPoissonContact_iff_coordinate_eq_reversal
    (observation : GeneratedRiemannZeroObservation) :
    WeightedCoPoissonContact observation ↔
      observation.coordinate = coordinateReversal observation.coordinate := by
  constructor
  · exact coordinate_eq_reversal_of_weightedCoPoissonContact observation
  · intro fixed test
    have coefficientZero : observation.coordinate -
        coordinateReversal observation.coordinate = 0 :=
      sub_eq_zero.mpr fixed
    rw [coefficientZero, zero_mul]

/-- The continuation branch is exactly failure of the requested contact,
not a phantom non-perfect case or a second source. -/
theorem quarterGraphResidual_nonempty_iff_not_weightedCoPoissonContact
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Nonempty (QuarterGraphActionResidualFibre observation) ↔
      ¬ WeightedCoPoissonContact observation := by
  constructor
  · intro residual contact
    have characterNormNe :=
      (quarterGraphResidual_nonempty_iff_character_norm_ne_one
        observation nontrivial).1 residual
    have fixed :=
      (weightedCoPoissonContact_iff_coordinate_eq_reversal observation).1
        contact
    exact characterNormNe
      ((quarterGraph_character_norm_one_iff_coordinate_eq_reversal
        observation).2 fixed)
  · intro contactFails
    apply (quarterGraphResidual_nonempty_iff_character_norm_ne_one
      observation nontrivial).2
    intro characterNorm
    have fixed :=
      (quarterGraph_character_norm_one_iff_coordinate_eq_reversal
        observation).1 characterNorm
    exact contactFails
      ((weightedCoPoissonContact_iff_coordinate_eq_reversal observation).2
        fixed)

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
