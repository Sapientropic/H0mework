import Mathlib.Analysis.MellinInversion
import H0mework.Realization.Coherent.Completion
import H0mework.Versions.V2.Arithmetic.RiemannGraph.IntegralGraphOrbit

/-!
# Actual integral-orbit energy/measurement kernel compatibility

The literal integral dilation orbit has no event whose `L²` energy coordinate
vanishes while its Mellin measurement coordinate survives.  The result is
proved at the source-test level and then transported through the actual
selected/reversal orbit factorizations.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram

open Complex MeasureTheory
open Character
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ThetaJRoleRepresentation
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedIntegralCoherentCompletion
open SourceGeneratedIntegralCharacterGroupRing
open scoped ENNReal FourierTransform

noncomputable section

/-- The literal quarter-Mellin `L²` feature already detects every source
value that its Mellin functional can detect. -/
theorem quarterMellinL2Feature_eq_zero_imp_functional_eq_zero
    (z : ℂ) (value : QuarterMellinL2Test z)
    (energyZero : quarterMellinL2Feature z value = 0) :
    quarterMellinL2Functional z value = 0 := by
  have zeroMem : MemLp (0 : ℝ → ℂ)
      (2 : ℝ≥0∞) (volume : Measure ℝ) := MemLp.zero
  have transformAE :
      positiveMellinLogQuarterTransform value.1 =ᵐ[volume] 0 := by
    apply (MemLp.toLp_eq_toLp_iff value.2.1 zeroMem).mp
    rw [zeroMem.toLp_zero]
    exact energyZero
  have reflectedAE :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      transformAE
  change (fun u : ℝ =>
      positiveMellinLogQuarterTransform value.1 (-u)) =ᵐ[volume] 0 at reflectedAE
  have mellinInputAE :
      (fun u : ℝ =>
        (Real.exp (-z.re * u) : ℂ) *
          positiveMellinExtension value.1 (Real.exp (-u))) =ᵐ[volume] 0 := by
    filter_upwards [reflectedAE] with u hu
    have sourceZero :
        value.1 ⟨Real.exp (-u), Real.exp_pos (-u)⟩ = 0 := by
      change (Real.exp ((-u) / 4) : ℂ) *
          value.1 ⟨Real.exp (-u), Real.exp_pos (-u)⟩ = 0 at hu
      exact (mul_eq_zero.mp hu).resolve_left
        (ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    simp [positiveMellinExtension, Real.exp_pos, sourceZero]
  change mellin (positiveMellinExtension value.1) z = 0
  rw [mellin_eq_fourier]
  rw [Real.fourier_congr_ae (by
    simpa [smul_eq_mul] using mellinInputAE)]
  rw [Real.fourier_eq]
  simp

/-- The source test underlying each selected integral basis event. -/
def selectedIntegralDilationTestOrbit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ]
      QuarterMellinL2Test (selectedCoPoissonMuntzParameter observation) :=
  canonicalBasis.constr ℤ fun scale =>
    quarterDilationTestAction
      (selectedCoPoissonMuntzParameter observation)
      (scaleSquare scale) (scaleSquare_pos scale)
      (normalizedCoPoissonMuntzQuarterShellTest
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial))

/-- The source test underlying each reversal integral basis event. -/
def reversalIntegralDilationTestOrbit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ]
      QuarterMellinL2Test (reversalCoPoissonMuntzParameter observation) :=
  canonicalBasis.constr ℤ fun scale =>
    quarterDilationTestAction
      (reversalCoPoissonMuntzParameter observation)
      (scaleSquare scale) (scaleSquare_pos scale)
      (normalizedCoPoissonMuntzQuarterShellTest
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial))

@[simp] theorem selectedIntegralDilationTestOrbit_delta
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    selectedIntegralDilationTestOrbit observation nontrivial (delta scale) =
      quarterDilationTestAction
        (selectedCoPoissonMuntzParameter observation)
        (scaleSquare scale) (scaleSquare_pos scale)
        (normalizedCoPoissonMuntzQuarterShellTest
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)) := by
  rw [← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

@[simp] theorem reversalIntegralDilationTestOrbit_delta
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    reversalIntegralDilationTestOrbit observation nontrivial (delta scale) =
      quarterDilationTestAction
        (reversalCoPoissonMuntzParameter observation)
        (scaleSquare scale) (scaleSquare_pos scale)
        (normalizedCoPoissonMuntzQuarterShellTest
          (reversalCoPoissonMuntzParameter observation)
          (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)) := by
  rw [← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

/-- The production selected graph orbit is literally the graph of the
selected integral test orbit, not an abstract replacement map. -/
theorem selectedIntegralGraphOrbit_factorization
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedIntegralGraphOrbit observation nontrivial =
      ((graphFeature
        (quarterMellinL2Feature
          (selectedCoPoissonMuntzParameter observation))
        (quarterMellinL2Functional
          (selectedCoPoissonMuntzParameter observation))).restrictScalars ℤ).comp
        (selectedIntegralDilationTestOrbit observation nontrivial) := by
  apply canonicalBasis.ext
  intro scale
  rw [canonicalBasis_apply, selectedIntegralGraphOrbit_delta,
    LinearMap.comp_apply, selectedIntegralDilationTestOrbit_delta]
  rfl

/-- The production reversal graph orbit is literally the graph of the
reversal integral test orbit. -/
theorem reversalIntegralGraphOrbit_factorization
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalIntegralGraphOrbit observation nontrivial =
      ((graphFeature
        (quarterMellinL2Feature
          (reversalCoPoissonMuntzParameter observation))
        (quarterMellinL2Functional
          (reversalCoPoissonMuntzParameter observation))).restrictScalars ℤ).comp
        (reversalIntegralDilationTestOrbit observation nontrivial) := by
  apply canonicalBasis.ext
  intro scale
  rw [canonicalBasis_apply, reversalIntegralGraphOrbit_delta,
    LinearMap.comp_apply, reversalIntegralDilationTestOrbit_delta]
  rfl

/-- Complex scalar extension preserves the selected graph factorization. -/
theorem selectedComplexifiedIntegralGraphOrbit_factorization
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    complexifiedFeature
        (selectedIntegralGraphOrbit observation nontrivial) =
      (graphFeature
        (quarterMellinL2Feature
          (selectedCoPoissonMuntzParameter observation))
        (quarterMellinL2Functional
          (selectedCoPoissonMuntzParameter observation))).comp
        (complexifiedLinearMap
          (selectedIntegralDilationTestOrbit observation nontrivial)) := by
  apply LinearMap.ext
  intro value
  induction value using TensorProduct.induction_on with
  | zero => simp
  | add left right left_ih right_ih =>
      simpa only [map_add] using congrArg₂ (· + ·) left_ih right_ih
  | tmul coefficient event =>
      rw [complexifiedFeature_tmul, LinearMap.comp_apply,
        complexifiedLinearMap_tmul, map_smul]
      have point := LinearMap.congr_fun
        (selectedIntegralGraphOrbit_factorization observation nontrivial) event
      rw [LinearMap.comp_apply] at point
      exact congrArg (fun target => coefficient • target) point

theorem reversalComplexifiedIntegralGraphOrbit_factorization
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    complexifiedFeature
        (reversalIntegralGraphOrbit observation nontrivial) =
      (graphFeature
        (quarterMellinL2Feature
          (reversalCoPoissonMuntzParameter observation))
        (quarterMellinL2Functional
          (reversalCoPoissonMuntzParameter observation))).comp
        (complexifiedLinearMap
          (reversalIntegralDilationTestOrbit observation nontrivial)) := by
  apply LinearMap.ext
  intro value
  induction value using TensorProduct.induction_on with
  | zero => simp
  | add left right left_ih right_ih =>
      simpa only [map_add] using congrArg₂ (· + ·) left_ih right_ih
  | tmul coefficient event =>
      rw [complexifiedFeature_tmul, LinearMap.comp_apply,
        complexifiedLinearMap_tmul, map_smul]
      have point := LinearMap.congr_fun
        (reversalIntegralGraphOrbit_factorization observation nontrivial) event
      rw [LinearMap.comp_apply] at point
      exact congrArg (fun target => coefficient • target) point

/-- Strong literal-event kernel compatibility for the selected actual
integral dilation orbit. -/
theorem selectedIntegralGraphOrbit_energy_zero_imp_measurement_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : IntegralScaleCarrier)
    (energyZero :
      (selectedIntegralGraphOrbit observation nontrivial event).fst = 0) :
    (selectedIntegralGraphOrbit observation nontrivial event).snd = 0 := by
  rw [selectedIntegralGraphOrbit_factorization, LinearMap.comp_apply] at energyZero ⊢
  exact quarterMellinL2Feature_eq_zero_imp_functional_eq_zero
    (selectedCoPoissonMuntzParameter observation)
    (selectedIntegralDilationTestOrbit observation nontrivial event)
    energyZero

/-- Strong literal-event kernel compatibility for the reversal actual
integral dilation orbit. -/
theorem reversalIntegralGraphOrbit_energy_zero_imp_measurement_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : IntegralScaleCarrier)
    (energyZero :
      (reversalIntegralGraphOrbit observation nontrivial event).fst = 0) :
    (reversalIntegralGraphOrbit observation nontrivial event).snd = 0 := by
  rw [reversalIntegralGraphOrbit_factorization, LinearMap.comp_apply] at energyZero ⊢
  exact quarterMellinL2Feature_eq_zero_imp_functional_eq_zero
    (reversalCoPoissonMuntzParameter observation)
    (reversalIntegralDilationTestOrbit observation nontrivial event)
    energyZero

/-- No finite complex scalar combination of selected integral orbit events is
measurement-only. -/
theorem selectedComplexifiedIntegralGraphOrbit_energy_zero_imp_measurement_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ComplexifiedCarrier IntegralScaleCarrier)
    (energyZero :
      (complexifiedFeature
        (selectedIntegralGraphOrbit observation nontrivial) source).fst = 0) :
    (complexifiedFeature
      (selectedIntegralGraphOrbit observation nontrivial) source).snd = 0 := by
  rw [selectedComplexifiedIntegralGraphOrbit_factorization,
    LinearMap.comp_apply] at energyZero ⊢
  exact quarterMellinL2Feature_eq_zero_imp_functional_eq_zero
    (selectedCoPoissonMuntzParameter observation)
    (complexifiedLinearMap
      (selectedIntegralDilationTestOrbit observation nontrivial) source)
    energyZero

theorem reversalComplexifiedIntegralGraphOrbit_energy_zero_imp_measurement_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ComplexifiedCarrier IntegralScaleCarrier)
    (energyZero :
      (complexifiedFeature
        (reversalIntegralGraphOrbit observation nontrivial) source).fst = 0) :
    (complexifiedFeature
      (reversalIntegralGraphOrbit observation nontrivial) source).snd = 0 := by
  rw [reversalComplexifiedIntegralGraphOrbit_factorization,
    LinearMap.comp_apply] at energyZero ⊢
  exact quarterMellinL2Feature_eq_zero_imp_functional_eq_zero
    (reversalCoPoissonMuntzParameter observation)
    (complexifiedLinearMap
      (reversalIntegralDilationTestOrbit observation nontrivial) source)
    energyZero

end

end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
