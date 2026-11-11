import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalConductorEnergy

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley

open BurnolPhysicalState Filter MeasureTheory Set
open scoped InnerProductSpace

namespace WidePositionGap

open private literal_raw from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionConductor
open private literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private current from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients

local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "R" => burnolDirectRightResolventCLM
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)

/-- The source-side quarter gap estimate preserves every positive position radius. -/
theorem original_R_preserves_position_radius (c : BurnolCompletedMellinCoordinate) {radius : ℝ}
    (positive : 0 < radius) (v : BurnolL2) (gap : v ∈ locallyConstantFace radius) :
    R c v ∈ locallyConstantFace radius := by
  have half : 1/4 < (c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  change burnolDirectRightResolvent (c.value/2) v ∈ _
  unfold burnolDirectRightResolvent
  apply (locallyConstantFace radius).neg_mem
  apply integral_mem_closedSubmodule
    {toSubmodule := locallyConstantFace radius, isClosed' := locallyConstantFace_isClosed radius}
  · exact burnolDirectRightResolventIntegrand_integrableOn _ half v
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with shift inside
    unfold burnolDirectRightResolventIntegrand
    exact (locallyConstantFace radius).smul_mem _
      (burnolMultiplicativeDilation_mem_locallyConstantFace_of_nonpositive radius positive (-shift / 2)
        (show -shift / 2 ≤ 0 by linarith [mem_Ioi.mp inside]) v gap)

/-- The actual counted comb has no positive integer channel inside its unit position interval. -/
theorem original_seed_unit_position_gap : seed ∈ locallyConstantFace 1 := by
  let mean : ℂ := -2*(Real.log (1 + burnolPaCombSourceWidth 0) : ℂ)
  have counted : (seed : ℝ → ℂ) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] fun _ => mean := by
    filter_upwards [ae_restrict_of_ae (s := Ioo (-1 : ℝ) 1) (burnolPaCombApproximation_coeFn 0),
      ae_restrict_mem measurableSet_Ioo] with x native hx
    have noChannel : burnolHarmonicStepChannels 1 (1 + burnolPaCombSourceWidth 0) x = ∅ := by
      unfold burnolHarmonicStepChannels
      rw [div_one, Nat.floor_eq_zero.mpr (abs_lt.mpr hx)]
      simp
    rw [native, burnolHarmonicStepWaveRaw, noChannel, Finset.sum_empty]
    simp [mean]
  refine mem_locallyConstantFace_iff_exists.mpr ⟨mean, ?_⟩
  apply Lp.ext
  have sameMeasure : volume.restrict (Ioo (-1 : ℝ) 1) = volume.restrict (symmetricInterval 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [sameMeasure] at counted
  filter_upwards [counted, Lp.coeFn_smul mean (intervalConstant 1), intervalConstant_coeFn 1,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval 1) seed] with x read scaled unit restricted
  rw [scaled, Pi.smul_apply, smul_eq_mul, unit, mul_one]
  exact read.symm.trans restricted.symm

/-- The original projection is faithful on differences of even source fields with the unit position gap. -/
theorem physical_read_eq_of_unit_gap {v w : BurnolL2}
    (left : v ∈ locallyConstantFace 1) (right : w ∈ locallyConstantFace 1)
    (leftEven : reflectL2 v = v) (rightEven : reflectL2 w = w) (same : P v = P w) :
    v = w := by
  apply sub_eq_zero.mp
  apply PhysicalClock.physical_read_faithful_on_wider_gap _ (by norm_num : (1/4 : ℝ) < 1)
    ((locallyConstantFace 1).sub_mem left right)
  · rw [map_sub, leftEven, rightEven]
  · rw [map_sub, same, sub_self]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "second" => DivisionConductor.branchSecondAt observation nontrivial half depth
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down

/-- Every literal Division state keeps the actual seed's unit position gap. -/
theorem actual_division_unit_position_gap (ordinal : Nat) : raw ordinal ∈ locallyConstantFace 1 := by
  have orbit (n : Nat) : ((R c)^n) seed ∈ locallyConstantFace 1 := by
    induction n with
    | zero => simpa only [pow_zero, one_apply_eq_self] using original_seed_unit_position_gap
    | succ n prior =>
      rw [pow_succ', mul_apply_eq_comp]
      exact original_R_preserves_position_radius c zero_lt_one _ prior
  rw [literal_raw observation nontrivial half depth]
  exact orbit _

/-- Each physical slot inherits a nonzero field from the exact Xi coefficient of its own source. -/
theorem actual_division_physical_ne_zero (ordinal : Nat) : (input ordinal).1 ≠ 0 := by
  intro erased
  have projected : P (raw ordinal) = (input ordinal).1 :=
    congrArg Prod.fst (literal_split observation nontrivial half depth ordinal)
  let field := current observation nontrivial half depth ordinal
  have even : reflectL2 (raw ordinal) = raw ordinal := mem_evenL2ClosedFace_iff.mp field.property.2
  have gone := physical_read_eq_of_unit_gap
    (actual_division_unit_position_gap observation nontrivial half depth ordinal)
    ((locallyConstantFace 1).zero_mem) even (map_zero reflectL2) ((projected.trans erased).trans (map_zero P).symm)
  have fieldZero : field = 0 := Subtype.ext gone
  have coefficientsZero : HilbertInventory.coefficientsAt observation nontrivial half depth ordinal = 0 := by
    change (HilbertInventory.basis c).repr field = 0
    rw [fieldZero, map_zero]
  exact (HilbertInventory.actual_division_first_coefficient observation nontrivial half depth ordinal).2.2
    (by rw [coefficientsZero]; rfl)

/-- Every literal physical slot pays the strict diagonal of the original Γ² Gram. -/
theorem actual_division_physical_energy_positive (ordinal : Nat) :
    0 < (inner ℂ (input ordinal).1 (second ordinal).1).re :=
  (ConductorFaithfulness.actual_physical_second_energy_iff observation nontrivial half depth ordinal).mpr
    (actual_division_physical_ne_zero observation nontrivial half depth ordinal)

end WidePositionGap
end OriginalKFiniteOrderRelease.PositionGapCayley
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
