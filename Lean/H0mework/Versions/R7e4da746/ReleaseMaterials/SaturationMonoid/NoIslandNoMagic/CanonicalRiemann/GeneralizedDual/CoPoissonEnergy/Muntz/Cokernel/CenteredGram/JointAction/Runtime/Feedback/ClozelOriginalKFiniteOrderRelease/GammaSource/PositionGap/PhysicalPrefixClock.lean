import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalClockFaithfulness
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePointClock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalClock

open BurnolPhysicalState
open OriginalRSourceJointContact.OutsideHistory.FinitePowerWindow
open OriginalRSourceJointContact.OutsideHistory.FinitePointClock
open OriginalRSourceJointContact.OutsideHistory.ClockReconstruction
open HilbertInventory

open private literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private current from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients
open private quarter_budget from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePointClock

namespace Div
export OriginalKCombFirstFullSourceDynamics (raw input raw_successor)
end Div

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => Div.raw observation nontrivial half depth
local notation "input" => Div.input observation nontrivial half depth
local notation "R" => burnolDirectRightResolventCLM
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "D" => burnolMultiplicativeDilation
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate

private theorem raw_power (ordinal advance : Nat) :
    raw (ordinal+advance) = ((R c)^advance) (raw ordinal) := by
  induction advance with
  | zero => rw [Nat.add_zero, pow_zero, one_apply_eq_self]
  | succ k prior =>
    rw [Nat.add_succ, Div.raw_successor, OriginalKCombCofinalRAction.original_R_direct,
      prior, pow_succ', mul_apply_eq_comp]
    rfl

/-- The window reads only the physical slots actually emitted after this ordinal. -/
def physicalWindow (test : SchwartzMap ℝ ℂ) (W : ℝ) (N ordinal : Nat) : BurnolL2 :=
  ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k+1),
    coefficient test c W k j • (input (ordinal+(j+1))).1

theorem actual_physical_window_from_powers (test : SchwartzMap ℝ ℂ) (W : ℝ) (N ordinal : Nat) :
    physicalWindow observation nontrivial half depth test W N ordinal =
      finiteWindow P test c W N (raw ordinal) := by
  have projected (i : Nat) : P (raw i) = (input i).1 :=
    congrArg Prod.fst (literal_split observation nontrivial half depth i)
  simp only [physicalWindow, finiteWindow, ← raw_power, projected]

private def clockField (ordinal : Nat) : BurnolL2 := P (D (-clock 0) (raw ordinal))

local notation "point" => clockField observation nontrivial half depth

/-- The same finite clock budget prices the literal current and its literal successor. -/
theorem actual_physical_window_current_next (ordinal : Nat) (ε : ℝ) (positive : 0 < ε) :
    ∃ (radius : ℝ) (small : 0 < radius) (W N : Nat),
      let test := clockTest (clockBump 0 radius small);
      ‖physicalWindow observation nontrivial half depth test W N ordinal - point ordinal‖ ≤ ε ∧
      ‖physicalWindow observation nontrivial half depth test W N (ordinal+1) - point (ordinal+1)‖ ≤ ε := by
  let predecessor := OriginalKCofinalFullBranchFibre.OutsideHistory.clockPredecessor observation nontrivial half depth
  have oldRead (i : Nat) : R c (predecessor i) = raw i :=
    OriginalKCofinalFullBranchFibre.OutsideHistory.actual_clock_predecessor observation nontrivial half depth i
  let timeScale (i : Nat) := ‖P‖ * ‖generatorWrite c (predecessor i)‖
  let freqScale (i : Nat) := 8 * ‖P‖ * ‖raw i‖
  let timeBudget := max (timeScale ordinal) (timeScale (ordinal+1))
  let freqBudget := max (freqScale ordinal) (freqScale (ordinal+1))
  let radius := ε / (4 * (1 + timeBudget))
  let frequency := ε / (4 * (1 + freqBudget))
  have timeNonnegative : 0 ≤ timeBudget :=
    (show 0 ≤ timeScale ordinal by dsimp only [timeScale]; positivity).trans (le_max_left _ _)
  have freqNonnegative : 0 ≤ freqBudget :=
    (show 0 ≤ freqScale ordinal by dsimp only [freqScale]; positivity).trans (le_max_left _ _)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have frequencyPositive : 0 < frequency := by dsimp only [frequency]; positivity
  let bump := clockBump 0 radius radiusPositive
  let test := clockTest bump
  have support : bump.rOut ≤ 2 * clock 0 :=
    (min_le_left (clock 0) radius).trans (by linarith [clock_pos 0])
  have outer : bump.rOut ≤ radius := min_le_right _ _
  obtain ⟨W,N,paid⟩ := actual_finite_window_precise P test c frequency frequencyPositive
  have error (i : Nat) (time : timeScale i ≤ timeBudget) (freq : freqScale i ≤ freqBudget) :
      ‖physicalWindow observation nontrivial half depth test W N i - point i‖ ≤ ε := by
    have timeRead := actual_clock_window_time_error P c (predecessor i) bump support
    rw [oldRead i, show -(2*clock 0)/2 = -clock 0 by ring] at timeRead
    have timeScaleNonnegative : 0 ≤ timeScale i := by dsimp only [timeScale]; positivity
    have timeBound : ‖windowRead P test (raw i) - point i‖ ≤ ε/4 :=
      timeRead.trans ((mul_le_mul_of_nonneg_left outer timeScaleNonnegative).trans
        ((mul_le_mul_of_nonneg_right time radiusPositive.le).trans (quarter_budget positive timeNonnegative)))
    have freqBound : ‖finiteWindow P test c W N (raw i) - windowRead P test (raw i)‖ ≤ ε/4 := by
      rw [norm_sub_rev]
      exact (paid (raw i)).trans
        ((mul_le_mul_of_nonneg_right freq frequencyPositive.le).trans (quarter_budget positive freqNonnegative))
    rw [actual_physical_window_from_powers]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (windowRead P test (raw i)) _).trans (by linarith)
  exact ⟨radius, radiusPositive, W,N,
    error ordinal (le_max_left _ _) (le_max_left _ _),
    error (ordinal+1) (le_max_right _ _) (le_max_right _ _)⟩

private theorem actual_clock_field_ne (ordinal : Nat) : point ordinal ≠ 0 := by
  let field := current observation nontrivial half depth ordinal
  have even : reflectL2 (raw ordinal) = raw ordinal := mem_evenL2ClosedFace_iff.mp field.property.2
  intro erased
  have gone : raw ordinal = 0 := physical_inward_read_injective (clock 0) (clock_pos 0)
    field.property.1 ((locallyConstantFace (1/4 : ℝ)).zero_mem) even (map_zero reflectL2) (by
      rw [map_zero, map_zero]
      exact erased)
  have fieldZero : field = 0 := Subtype.ext gone
  have coeffZero : coefficientsAt observation nontrivial half depth ordinal = 0 := by
    change (basis c).repr field = _
    rw [fieldZero, map_zero]
  exact (actual_division_first_coefficient observation nontrivial half depth ordinal).2.2
    (by rw [coeffZero]; rfl)

/-- A finite prefix produced from the original R clock contains a nonzero literal physical slot. -/
theorem actual_division_finite_physical_visibility (ordinal : Nat) :
    ∃ (radius : ℝ) (small : 0 < radius) (W N : Nat) (j : Nat),
      let window := physicalWindow observation nontrivial half depth (clockTest (clockBump 0 radius small)) W N ordinal;
      0 < ‖window‖ ∧ 0 < j ∧ j ≤ N ∧ (input (ordinal+j)).1 ≠ 0 := by
  have live := norm_pos_iff.mpr (actual_clock_field_ne observation nontrivial half depth ordinal)
  obtain ⟨radius, small, W, N, approximation, _⟩ :=
    actual_physical_window_current_next observation nontrivial half depth ordinal (‖point ordinal‖/2) (half_pos live)
  let test := clockTest (clockBump 0 radius small)
  let window := physicalWindow observation nontrivial half depth test W N ordinal
  have windowLive : window ≠ 0 := by
    intro erased
    change ‖window - point ordinal‖ ≤ ‖point ordinal‖/2 at approximation
    rw [erased, zero_sub, norm_neg] at approximation
    linarith
  suffices witness : ∃ j : Nat, 0 < j ∧ j ≤ N ∧ (input (ordinal+j)).1 ≠ 0 by
    obtain ⟨j, positive, within, visible⟩ := witness
    exact ⟨radius, small, W, N, j, norm_pos_iff.mpr windowLive, positive, within, visible⟩
  by_contra! silent
  apply windowLive
  unfold window physicalWindow
  refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun j hj => ?_
  have kBound := Finset.mem_range.mp hk
  have jBound := Finset.mem_range.mp hj
  rw [silent (j+1) (by omega) (by omega), smul_zero]

end OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalClock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
