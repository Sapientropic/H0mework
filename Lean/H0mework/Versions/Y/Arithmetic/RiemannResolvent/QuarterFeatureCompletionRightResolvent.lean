import H0mework.Versions.Y.Arithmetic.RiemannDivision.QuarterFeatureCompletionTranslation
import H0mework.Versions.Y.Arithmetic.RiemannResolvent.QuarterEnergyRightResolventFaithful

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set Filter
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open ClozelGeneralizedDual
open SourceGeneratedComplexFeaturePerfectification

noncomputable section

def quarterFeatureCompletionRightResolventIntegrand
    (coordinate : ℂ)
    (value : HilbertAmbient (quarterMellinL2Feature coordinate))
    (shift : ℝ) : HilbertAmbient (quarterMellinL2Feature coordinate) :=
  positiveMellinQuarterRightResolventWeight coordinate shift •
    quarterFeatureCompletionTranslation coordinate shift value

theorem quarterFeatureCompletionTranslation_stronglyContinuous
    (coordinate : ℂ)
    (value : HilbertAmbient (quarterMellinL2Feature coordinate)) :
    Continuous fun shift : ℝ =>
      quarterFeatureCompletionTranslation coordinate shift value := by
  apply (hilbertAmbientRealization
    (quarterMellinL2Feature coordinate)).isometry.isUniformInducing.isInducing.continuous_iff.mpr
  change Continuous fun shift : ℝ =>
    hilbertAmbientRealization (quarterMellinL2Feature coordinate)
      (quarterFeatureCompletionTranslation coordinate shift value)
  rw [show (fun shift : ℝ =>
      hilbertAmbientRealization (quarterMellinL2Feature coordinate)
        (quarterFeatureCompletionTranslation coordinate shift value)) =
      fun shift : ℝ => positiveMellinQuarterEnergyTranslation shift
        (hilbertAmbientRealization (quarterMellinL2Feature coordinate) value) by
    funext shift
    exact quarterFeatureCompletionTranslation_realization
      coordinate shift value]
  exact positiveMellinQuarterEnergyTranslation_stronglyContinuous _

theorem quarterFeatureCompletionRightResolventIntegrand_continuous
    (coordinate : ℂ)
    (value : HilbertAmbient (quarterMellinL2Feature coordinate)) :
    Continuous
      (quarterFeatureCompletionRightResolventIntegrand coordinate value) := by
  unfold quarterFeatureCompletionRightResolventIntegrand
  exact (positiveMellinQuarterRightResolventWeight_continuous coordinate).smul
    (quarterFeatureCompletionTranslation_stronglyContinuous coordinate value)

theorem quarterFeatureCompletionRightResolventIntegrand_realization
    (coordinate : ℂ)
    (value : HilbertAmbient (quarterMellinL2Feature coordinate))
    (shift : ℝ) :
    hilbertAmbientRealization (quarterMellinL2Feature coordinate)
        (quarterFeatureCompletionRightResolventIntegrand
          coordinate value shift) =
      positiveMellinQuarterRightResolventIntegrand coordinate
        (hilbertAmbientRealization (quarterMellinL2Feature coordinate) value)
        shift := by
  unfold quarterFeatureCompletionRightResolventIntegrand
    positiveMellinQuarterRightResolventIntegrand
  rw [map_smul, quarterFeatureCompletionTranslation_realization]

theorem quarterFeatureCompletionRightResolventIntegrand_integrableOn
    (coordinate : ℂ) (rightQuarter : 1 / 4 < coordinate.re)
    (value : HilbertAmbient (quarterMellinL2Feature coordinate)) :
    IntegrableOn
      (quarterFeatureCompletionRightResolventIntegrand coordinate value)
      (Ioi (0 : ℝ)) := by
  have targetIntegrable :=
    positiveMellinQuarterRightResolventIntegrand_integrableOn
      coordinate rightQuarter
        (hilbertAmbientRealization (quarterMellinL2Feature coordinate) value)
  change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
  change Integrable _ (volume.restrict (Ioi (0 : ℝ))) at targetIntegrable
  apply Integrable.mono targetIntegrable
    ((quarterFeatureCompletionRightResolventIntegrand_continuous
      coordinate value).aestronglyMeasurable.restrict)
  filter_upwards with shift
  calc
    ‖quarterFeatureCompletionRightResolventIntegrand coordinate value shift‖ =
        ‖hilbertAmbientRealization (quarterMellinL2Feature coordinate)
          (quarterFeatureCompletionRightResolventIntegrand
            coordinate value shift)‖ :=
      ((hilbertAmbientRealization
        (quarterMellinL2Feature coordinate)).norm_map _).symm
    _ = ‖positiveMellinQuarterRightResolventIntegrand coordinate
        (hilbertAmbientRealization (quarterMellinL2Feature coordinate) value)
        shift‖ := by
      rw [quarterFeatureCompletionRightResolventIntegrand_realization]
    _ ≤ _ := le_rfl

/-- Right resolvent on the entire source-generated feature completion. -/
def quarterFeatureCompletionRightResolvent
    (coordinate : ℂ)
    (value : HilbertAmbient (quarterMellinL2Feature coordinate)) :
    HilbertAmbient (quarterMellinL2Feature coordinate) :=
  -∫ shift : ℝ in Ioi (0 : ℝ),
    quarterFeatureCompletionRightResolventIntegrand coordinate value shift

theorem quarterFeatureCompletionRightResolvent_realization
    (coordinate : ℂ)
    (value : HilbertAmbient (quarterMellinL2Feature coordinate)) :
    hilbertAmbientRealization (quarterMellinL2Feature coordinate)
        (quarterFeatureCompletionRightResolvent coordinate value) =
      positiveMellinQuarterRightResolvent coordinate
        (hilbertAmbientRealization (quarterMellinL2Feature coordinate) value) := by
  unfold quarterFeatureCompletionRightResolvent
    positiveMellinQuarterRightResolvent
  rw [map_neg, ← LinearIsometry.integral_comp_comm
    (hilbertAmbientRealization (quarterMellinL2Feature coordinate))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro shift _
  exact quarterFeatureCompletionRightResolventIntegrand_realization
    coordinate value shift

theorem quarterFeatureCompletionRightResolvent_eq_zero_iff
    (coordinate : ℂ) (rightQuarter : 1 / 4 < coordinate.re)
    (value : HilbertAmbient (quarterMellinL2Feature coordinate)) :
    quarterFeatureCompletionRightResolvent coordinate value = 0 ↔ value = 0 := by
  constructor
  · intro resolventZero
    apply (hilbertAmbientRealization
      (quarterMellinL2Feature coordinate)).injective
    have targetZero :
        positiveMellinQuarterRightResolvent coordinate
          (hilbertAmbientRealization
            (quarterMellinL2Feature coordinate) value) = 0 := by
      rw [← quarterFeatureCompletionRightResolvent_realization,
        resolventZero, map_zero]
    have sourceZero :=
      (positiveMellinQuarterRightResolvent_eq_zero_iff
        coordinate rightQuarter _).mp targetZero
    simpa using sourceZero
  · intro valueZero
    subst value
    unfold quarterFeatureCompletionRightResolvent
      quarterFeatureCompletionRightResolventIntegrand
    have integrandZero : (fun shift : ℝ =>
        positiveMellinQuarterRightResolventWeight coordinate shift •
          quarterFeatureCompletionTranslation coordinate shift 0) =
        fun _ => (0 : HilbertAmbient
          (quarterMellinL2Feature coordinate)) := by
      funext shift
      calc
        positiveMellinQuarterRightResolventWeight coordinate shift •
            quarterFeatureCompletionTranslation coordinate shift 0 =
          positiveMellinQuarterRightResolventWeight coordinate shift •
            (0 : HilbertAmbient (quarterMellinL2Feature coordinate)) := by
              rw [map_zero]
        _ = 0 := by
          exact @smul_zero ℂ
            (HilbertAmbient (quarterMellinL2Feature coordinate))
            inferInstance inferInstance
            (positiveMellinQuarterRightResolventWeight coordinate shift)
    rw [integrandZero]
    simp only [integral_zero, neg_zero]

def quarterFeatureCompletionRightResolventIterate
    (coordinate : ℂ) : Nat →
      HilbertAmbient (quarterMellinL2Feature coordinate) →
        HilbertAmbient (quarterMellinL2Feature coordinate)
  | 0, value => value
  | order + 1, value => quarterFeatureCompletionRightResolvent coordinate
      (quarterFeatureCompletionRightResolventIterate coordinate order value)

theorem quarterFeatureCompletionRightResolventIterate_ne_zero
    (coordinate : ℂ) (rightQuarter : 1 / 4 < coordinate.re)
    (order : Nat) {value : HilbertAmbient (quarterMellinL2Feature coordinate)}
    (valueNe : value ≠ 0) :
    quarterFeatureCompletionRightResolventIterate coordinate order value ≠ 0 := by
  induction order with
  | zero => exact valueNe
  | succ order ih =>
      exact (not_congr
        (quarterFeatureCompletionRightResolvent_eq_zero_iff coordinate
          rightQuarter _)).mpr ih

def selectedModifiedWeakFEPoleExactOrderCompletionResolvent
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    HilbertAmbient
      (quarterMellinL2Feature (selectedCoPoissonMuntzParameter observation)) :=
  quarterFeatureCompletionRightResolventIterate
    (selectedCoPoissonMuntzParameter observation)
    (generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate)
    (canonicalHilbertMap
      (quarterMellinL2Feature (selectedCoPoissonMuntzParameter observation))
      (selectedModifiedWeakFEPoleTraceTest observation nontrivial))

theorem selectedModifiedWeakFEPoleExactOrderCompletionResolvent_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    selectedModifiedWeakFEPoleExactOrderCompletionResolvent
      observation nontrivial ≠ 0 := by
  apply quarterFeatureCompletionRightResolventIterate_ne_zero
  · unfold selectedCoPoissonMuntzParameter
    rw [Complex.div_re]
    norm_num
    linarith
  · intro sourceZero
    have realizationZero := congrArg
      (hilbertAmbientRealization
        (quarterMellinL2Feature
          (selectedCoPoissonMuntzParameter observation))) sourceZero
    rw [hilbertAmbientRealization_source_readback, map_zero] at realizationZero
    exact selectedModifiedWeakFEPoleTraceTest_sourceEnergy_ne_zero
      observation nontrivial realizationZero

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
