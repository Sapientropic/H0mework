import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedClockWardPrice
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedPiPreparationReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalHalfResidual

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedClockJointReturn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumSourcePreparedState
open ActualDressedFullCoulomb ActualDressedPreparationEnergy ActualDressedTemporalResidual
open PreparationVacuumNoetherOrdinaryWard ActualDressedNoether ActualPreparedPiPreparationReturnProducer
open ActualSourcePreparedClockOperatorSource ActualSourcePreparedClockWardPrice ActualSourcePreparedProjectedClock
open PreparationVacuumPhysicalCharacteristic Filter Set
open scoped Topology BigOperators

/-- The source residual budget refines preparation accuracy; it does not select
or change the physical damping or spatial scale. -/
def sourceClockWardPrecision (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet tolerance : ℝ) : ℝ :=
  tolerance / (1 + sourceClockWardScale * sourceClockWardLowerBudget event epsilon sigma n branch sheet)

theorem source_clock_ward_precision_positive (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet tolerance : ℝ) (positive : 0 < tolerance) :
    0 < sourceClockWardPrecision event epsilon sigma n branch sheet tolerance := by
  apply div_pos positive
  have budget := source_clock_ward_lower_budget_nonnegative event epsilon sigma n branch sheet
  have product := mul_nonneg source_clock_ward_scale_nonnegative budget
  linarith

def sourceClockWardRefinedEvent (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet tolerance : ℝ) (positive : 0 < tolerance) : DressedEvent :=
  { event with
    epsilon := sourceClockWardPrecision event epsilon sigma n branch sheet tolerance
    precision := source_clock_ward_precision_positive event epsilon sigma n branch sheet tolerance positive }

def sourceClockWardRefinedPreparation (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet tolerance : ℝ) (positive : 0 < tolerance) :
    ActualPreparedPiPreparationReturn (sourceClockWardRefinedEvent event epsilon sigma n branch sheet tolerance positive) :=
  ActualPreparedPiPreparationReturn.of_source _

theorem source_clock_refined_budget (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet tolerance : ℝ) (positive : 0 < tolerance) :
    sourceClockWardLowerBudget
        (sourceClockWardRefinedEvent event epsilon sigma n branch sheet tolerance positive) epsilon sigma n branch sheet =
      sourceClockWardLowerBudget event epsilon sigma n branch sheet := rfl

/-- The original source constructor pays the normalized lower-clock Ward residual
at every positive damping. No numerator vanishing or matching scale is a premise. -/
theorem source_clock_refined_ward_price (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet tolerance : ℝ) (positive : 0 < tolerance) :
    ‖sourceClockWardLowerRead
        (sourceClockWardRefinedEvent event epsilon sigma n branch sheet tolerance positive) epsilon sigma n branch sheet‖ ≤
      tolerance := by
  have paid := source_clock_ward_lower_price
    (sourceClockWardRefinedEvent event epsilon sigma n branch sheet tolerance positive) epsilon sigma n branch sheet
  rw [source_clock_refined_budget] at paid
  apply paid.trans
  change sourceClockWardScale * sourceClockWardPrecision event epsilon sigma n branch sheet tolerance *
    sourceClockWardLowerBudget event epsilon sigma n branch sheet ≤ tolerance
  let cost := sourceClockWardScale * sourceClockWardLowerBudget event epsilon sigma n branch sheet
  have nonnegative : 0 ≤ cost := mul_nonneg source_clock_ward_scale_nonnegative
    (source_clock_ward_lower_budget_nonnegative event epsilon sigma n branch sheet)
  have bound : cost / (1 + cost) ≤ 1 := (div_le_one (by linarith : 0 < 1 + cost)).mpr (by linarith)
  calc
    _ = tolerance * (cost / (1 + cost)) := by unfold sourceClockWardPrecision cost; ring
    _ ≤ tolerance * 1 := mul_le_mul_of_nonneg_left bound positive.le
    _ = _ := mul_one _

theorem source_clock_ward_precision_le (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet tolerance : ℝ) (positive : 0 ≤ tolerance) :
    sourceClockWardPrecision event epsilon sigma n branch sheet tolerance ≤ tolerance := by
  unfold sourceClockWardPrecision
  have product := mul_nonneg source_clock_ward_scale_nonnegative
    (source_clock_ward_lower_budget_nonnegative event epsilon sigma n branch sheet)
  exact div_le_self positive (by linarith)

/-- Actual physical action endpoints, with the distinct preparation mismatch retained. -/
def sourcePhysicalClockWardLowerRead (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) : ℂ :=
  (∑r ∈ Finset.range (sourceStaticClockOrder event epsilon n),
    (dressedEulerObserver event
      (sourceHamiltonian (event.momentum - (epsilon^2 : ℝ) • n) event.frame *
          sourceProjectedClockWord event epsilon n branch sheet r -
        sourceProjectedClockWord event epsilon n branch sheet r * sourceHamiltonian event.momentum event.frame) -
      physicalPreparationMismatch event ((epsilon^2 : ℝ) • n)
        (sourceProjectedClockWord event epsilon n branch sheet r)) * (sigma : ℂ)^r) /
      (sourceStaticClockClearing event epsilon n).eval (sigma : ℂ)

theorem source_physical_clock_ward_lower_return (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) :
    sourcePhysicalClockWardLowerRead event epsilon sigma n branch sheet =
      sourceClockWardLowerRead event epsilon sigma n branch sheet := by
  unfold sourcePhysicalClockWardLowerRead sourceClockWardLowerRead sourceClockWardCoefficient
  simp_rw [physical_preparation_return, add_sub_cancel_left]

theorem source_clock_refined_physical_price (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet tolerance : ℝ) (positive : 0 < tolerance) :
    ‖sourcePhysicalClockWardLowerRead
        (sourceClockWardRefinedEvent event epsilon sigma n branch sheet tolerance positive) epsilon sigma n branch sheet‖ ≤
      tolerance := by
  rw [source_physical_clock_ward_lower_return]
  exact source_clock_refined_ward_price event epsilon sigma n branch sheet tolerance positive

/-- Any positive damping observation curve consumes the source-generated accuracy
budget and its actual clearing chart, without an independent product-filter limit. -/
theorem source_clock_joint_ward_return (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (damping : ℕ → ℝ)
    (positive : ∀k, 0 < damping k) :
    (∀k, (sourceStaticClockClearing
        (sourceClockWardRefinedEvent event epsilon (damping k) n branch sheet
          (preparationPrecision k) (preparationPrecision_positive k)) epsilon n).eval (damping k : ℂ) ≠ 0) ∧
    Tendsto (fun k => sourceClockWardLowerRead
      (sourceClockWardRefinedEvent event epsilon (damping k) n branch sheet
        (preparationPrecision k) (preparationPrecision_positive k))
      epsilon (damping k) n branch sheet) atTop (𝓝 0) := by
  constructor
  · intro k
    exact source_static_clock_clearing_positive _ epsilon (damping k) n (positive k)
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun k => norm_nonneg _) (fun k =>
      source_clock_refined_ward_price event epsilon (damping k) n branch sheet
        (preparationPrecision k) (preparationPrecision_positive k)) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem source_clock_joint_physical_return (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (damping : ℕ → ℝ)
    (positive : ∀k, 0 < damping k) :
    (∀k, (sourceStaticClockClearing
        (sourceClockWardRefinedEvent event epsilon (damping k) n branch sheet
          (preparationPrecision k) (preparationPrecision_positive k)) epsilon n).eval (damping k : ℂ) ≠ 0) ∧
    Tendsto (fun k => sourcePhysicalClockWardLowerRead
      (sourceClockWardRefinedEvent event epsilon (damping k) n branch sheet
        (preparationPrecision k) (preparationPrecision_positive k))
      epsilon (damping k) n branch sheet) atTop (𝓝 0) := by
  simp_rw [source_physical_clock_ward_lower_return]
  exact source_clock_joint_ward_return event epsilon n branch sheet damping positive

theorem source_clock_joint_preparation_cofinal (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (damping : ℕ → ℝ) :
    Tendsto (fun k => sourceClockWardPrecision event epsilon (damping k) n branch sheet
      (preparationPrecision k)) atTop (𝓝 0) := by
  refine squeeze_zero (fun k => (source_clock_ward_precision_positive event epsilon (damping k)
    n branch sheet (preparationPrecision k) (preparationPrecision_positive k)).le)
    (fun k => source_clock_ward_precision_le event epsilon (damping k) n branch sheet
      (preparationPrecision k) (preparationPrecision_positive k).le) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end LowEnergy.GaussComposite.ActualSourcePreparedClockJointReturn
