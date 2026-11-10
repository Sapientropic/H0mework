import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedClockOperatorSource

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedClockWardPrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumSourcePreparedState
open PreparationVacuumPreparedCurrent CanonicalPreparationCreation ActualDressedFullCoulomb ActualDressedPreparationEnergy
open ActualDressedTemporalResidual ActualSourcePreparedClockOperatorSource
open ActualSourcePreparedProjectedClock ActualDressedUniformMaterialCoefficients
open PreparationVacuumPhysicalCharacteristic Filter Set Polynomial
open scoped BigOperators Topology

def sourceClockWardScale : ℝ := 2 * (2 * ‖sourceLeg true 1 0‖ + 1)

theorem source_clock_ward_scale_nonnegative : 0 ≤ sourceClockWardScale := by
  unfold sourceClockWardScale
  positivity

/-- This is the actual two-endpoint Ward residual read on the same full coefficient word. -/
def sourceClockWardCoefficient (event : DressedEvent) (epsilon : ℝ) (n : PhysicalMomentum)
    (branch : Fin 2) (sheet : ℝ) (r : ℕ) : ℂ :=
  preparationWardObserver event (sourceProjectedClockWord event epsilon n branch sheet r)

theorem source_clock_ward_coefficient_original (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (r : ℕ) :
    sourceClockCoefficient epsilon r
      (coefficientObserver (preparationWardObserver event).toLinearMap
        (sourceProjectedClockOperator event epsilon n branch sheet)) =
      sourceClockWardCoefficient event epsilon n branch sheet r := by
  exact source_clock_observer_word epsilon r (preparationWardObserver event).toLinearMap _

theorem source_clock_ward_coefficient_price (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (r : ℕ) :
    ‖sourceClockWardCoefficient event epsilon n branch sheet r‖ ≤
      sourceClockWardScale * event.epsilon *
        ‖sourceProjectedClockWord event epsilon n branch sheet r‖ := by
  exact ((preparationWardObserver event).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (preparation_ward_observer_price event) (norm_nonneg _))

theorem source_clock_ward_preparation_price (event : DressedEvent) (k : ℕ) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (r : ℕ) :
    ‖sourceClockWardCoefficient (preparationEventSequence event k) epsilon n branch sheet r‖ ≤
      sourceClockWardScale * preparationPrecision k *
        ‖sourceProjectedClockWord event epsilon n branch sheet r‖ := by
  have paid := source_clock_ward_coefficient_price (preparationEventSequence event k)
    epsilon n branch sheet r
  rw [source_clock_word_preparation] at paid
  simpa only [preparationEventSequence] using paid

theorem source_clock_ward_preparation_limit (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (r : ℕ) :
    Tendsto (fun k => sourceClockWardCoefficient (preparationEventSequence event k) epsilon n branch sheet r)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have precision : Tendsto preparationPrecision atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine squeeze_zero (fun k => norm_nonneg _) (fun k =>
    source_clock_ward_preparation_price event k epsilon n branch sheet r) ?_
  simpa only [mul_zero, zero_mul] using
    (tendsto_const_nhds.mul precision).mul
      (tendsto_const_nhds (x := ‖sourceProjectedClockWord event epsilon n branch sheet r‖))

/-- The lower-clock residual is kept separate from the complete physical numerator. -/
def sourceClockWardLowerRead (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) : ℂ :=
  (∑r ∈ Finset.range (sourceStaticClockOrder event epsilon n),
    sourceClockWardCoefficient event epsilon n branch sheet r * (sigma : ℂ)^r) /
      (sourceStaticClockClearing event epsilon n).eval (sigma : ℂ)

def sourceClockWardLowerBudget (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) : ℝ :=
  (∑r ∈ Finset.range (sourceStaticClockOrder event epsilon n),
    ‖sourceProjectedClockWord event epsilon n branch sheet r‖ * ‖(sigma : ℂ)^r‖) /
      ‖(sourceStaticClockClearing event epsilon n).eval (sigma : ℂ)‖

theorem source_clock_ward_lower_budget_nonnegative (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) :
    0 ≤ sourceClockWardLowerBudget event epsilon sigma n branch sheet := by
  unfold sourceClockWardLowerBudget
  positivity

theorem source_clock_ward_lower_price (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) :
    ‖sourceClockWardLowerRead event epsilon sigma n branch sheet‖ ≤
      sourceClockWardScale * event.epsilon * sourceClockWardLowerBudget event epsilon sigma n branch sheet := by
  unfold sourceClockWardLowerRead sourceClockWardLowerBudget
  rw [norm_div]
  calc
    _ ≤ (∑r ∈ Finset.range (sourceStaticClockOrder event epsilon n),
        ‖sourceClockWardCoefficient event epsilon n branch sheet r * (sigma : ℂ)^r‖) /
          ‖(sourceStaticClockClearing event epsilon n).eval (sigma : ℂ)‖ :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ (∑r ∈ Finset.range (sourceStaticClockOrder event epsilon n),
        (sourceClockWardScale * event.epsilon *
          ‖sourceProjectedClockWord event epsilon n branch sheet r‖) * ‖(sigma : ℂ)^r‖) /
          ‖(sourceStaticClockClearing event epsilon n).eval (sigma : ℂ)‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (source_clock_ward_coefficient_price event epsilon n branch sheet r) (norm_nonneg _)
    _ = _ := by
      have factor : (∑r ∈ Finset.range (sourceStaticClockOrder event epsilon n),
          (sourceClockWardScale * event.epsilon *
            ‖sourceProjectedClockWord event epsilon n branch sheet r‖) * ‖(sigma : ℂ)^r‖) =
        (sourceClockWardScale * event.epsilon) *
          (∑r ∈ Finset.range (sourceStaticClockOrder event epsilon n),
            ‖sourceProjectedClockWord event epsilon n branch sheet r‖ * ‖(sigma : ℂ)^r‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [factor]
      ring

end LowEnergy.GaussComposite.ActualSourcePreparedClockWardPrice
