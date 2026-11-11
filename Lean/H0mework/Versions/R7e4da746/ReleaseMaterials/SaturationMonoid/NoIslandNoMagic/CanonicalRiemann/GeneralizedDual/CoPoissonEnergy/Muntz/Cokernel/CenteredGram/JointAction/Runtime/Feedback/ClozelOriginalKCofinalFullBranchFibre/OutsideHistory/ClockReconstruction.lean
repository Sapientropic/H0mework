import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.Consumer

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.OutsideHistory.ClockReconstruction

open Filter MeasureTheory Set CenteredGram.IntegralGraphJointAction
open scoped Topology
open private interval_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.ExpandedGap

local notation "F" => fourierL2
local notation "D" => burnolMultiplicativeDilation
local notation "q" => (1/4 : ℝ)
local notation "P" => burnolEvenAmbientProjectionEndomorphism
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

private abbrev gapWindow (n : ℕ) : Submodule ℂ BurnolL2 :=
  locallyConstantFace ((n : ℝ) + 1)

local instance gapComplete (n : ℕ) : CompleteSpace (gapWindow n) :=
  (locallyConstantFace_isClosed _).isComplete.completeSpace_coe

private theorem gap_restrict {small large : ℝ} (radius : small ≤ large) :
    locallyConstantFace large ≤ locallyConstantFace small := by
  intro value member
  obtain ⟨coefficient, read⟩ := interval_read member
  refine mem_locallyConstantFace_iff_exists.mpr ⟨coefficient, Lp.ext ?_⟩
  filter_upwards [ae_restrict_of_ae (s := symmetricInterval small) read,
    ae_restrict_mem (measurableSet_symmetricInterval small),
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval small) value,
    Lp.coeFn_smul coefficient (intervalConstant small), intervalConstant_coeFn small]
    with x largeRead inside restricted scalar constant
  rw [scalar]
  change coefficient * intervalConstant small x = restrictToInterval small value x
  rw [constant, mul_one]
  change coefficient = LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (symmetricInterval small) value x
  rw [restricted]
  exact (largeRead (abs_le.mp ((abs_le.mpr inside).trans radius))).symm

private theorem gap_inf_zero : (⨅ n : ℕ, gapWindow n) = ⊥ := by
  refine le_antisymm (fun z inside => ?_) bot_le
  rw [Submodule.mem_bot]
  have all : ∀ n : ℕ, z ∈ gapWindow n := (Submodule.mem_iInf gapWindow).mp inside
  have zero : fourierL2.symm z = 0 := by
    apply ExpandedGap.zero_of_all_inward_frequency_gap
    intro h _
    rw [fourierL2_burnolMultiplicativeDilation, neg_div, neg_neg, fourierL2.apply_symm_apply]
    obtain ⟨n, large⟩ := exists_nat_gt (q * Real.exp (h/2))
    apply gap_restrict ?_ (burnolMultiplicativeDilation_mem_locallyConstantFace_scaled (h/2) (all n))
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos (h/2))]
    linarith
  simpa only [fourierL2.apply_symm_apply, map_zero] using congrArg F zero

private theorem gap_projection_tendsto_zero (z : BurnolL2) :
    Tendsto (fun n : ℕ => (gapWindow n).starProjection z) atTop (𝓝 0) := by
  let U (n : ℕ) := (gapWindow n)ᗮ
  have increasing : Monotone U := by
    intro i j before
    apply Submodule.orthogonal_le
    apply gap_restrict
    exact add_le_add (Nat.cast_le.mpr before) le_rfl
  have dense : ⊤ ≤ (⨆ n, U n).topologicalClosure := by
    apply le_of_eq
    symm
    rw [Submodule.topologicalClosure_eq_top_iff, ← Submodule.iInf_orthogonal]
    simpa only [U, Submodule.orthogonal_orthogonal] using gap_inf_zero
  have tends : Tendsto (fun n => z - (U n).starProjection z) atTop (𝓝 (z - z)) :=
    tendsto_const_nhds.sub (Submodule.starProjection_tendsto_self U increasing z dense)
  simpa only [U, Submodule.starProjection_orthogonal_val, sub_sub_cancel, sub_self] using tends

/-- The original inward dilation moves the Fourier gap to the window of radius n + 1. -/
def clock (n : ℕ) : ℝ := Real.log (4 * ((n : ℝ) + 1))

theorem clock_pos (n : ℕ) : 0 < clock n := by
  have nonnegative : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  apply Real.log_pos
  linarith

private theorem scale_radius (n : ℕ) : q * Real.exp (clock n) = (n : ℝ) + 1 := by
  have nonnegative : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [clock, Real.exp_log (by linarith)]
  ring

private theorem physical_loss_bound (n : ℕ) (v : BurnolL2) :
    ‖P (D (-clock n) v)‖ ≤ ‖(gapWindow n).starProjection (F v)‖ := by
  let S := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  let iso := fourierL2.trans (D (-clock n))
  let moved := S.map iso.toLinearEquiv.toLinearMap
  have contained : moved ≤ gapWindow n := by
    rintro _ ⟨w, inside, rfl⟩
    have frequency : F w ∈ locallyConstantFace q := (fourierL2_mem_evenBurnolClosedFace inside).1.1
    change D (-clock n) (F w) ∈ gapWindow n
    simpa only [neg_neg, scale_radius] using
      burnolMultiplicativeDilation_mem_locallyConstantFace_scaled (-clock n) frequency
  have translated : iso (D (-clock n) v) = F v := by
    change D (-clock n) (F (D (-clock n) v)) = _
    rw [fourierL2_burnolMultiplicativeDilation, neg_neg, burnolMultiplicativeDilation_neg_eq_symm,
      (D (clock n)).symm_apply_apply]
  have projected := Submodule.starProjection_map_apply iso S (F v)
  rw [← translated, iso.symm_apply_apply] at projected
  change moved.starProjection (iso (D (-clock n) v)) = iso (P (D (-clock n) v)) at projected
  rw [translated] at projected
  have comp := congrArg (fun L : BurnolL2 →L[ℂ] BurnolL2 => L (F v))
    (Submodule.starProjection_comp_starProjection_of_le contained)
  change moved.starProjection ((gapWindow n).starProjection (F v)) = moved.starProjection (F v) at comp
  calc
    ‖P (D (-clock n) v)‖ = ‖moved.starProjection (F v)‖ := by rw [projected, iso.norm_map]
    _ = ‖moved.starProjection ((gapWindow n).starProjection (F v))‖ := congrArg norm comp.symm
    _ ≤ _ := moved.norm_starProjection_apply_le _

/-- Pull the actual outside field back along its own dilation. -/
def readClock (n : ℕ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (D (clock n)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (OriginalKCombPhysicalAction.physicalRemainder.comp
      (D (-clock n)).toContinuousLinearEquiv.toContinuousLinearMap)

theorem actual_clock_error (n : ℕ) (v : BurnolL2) :
    ‖readClock n v - v‖ = ‖P (D (-clock n) v)‖ := by
  have outside : O (D (-clock n) v) = D (-clock n) v - P (D (-clock n) v) :=
    Submodule.starProjection_orthogonal_val _
  change ‖D (clock n) (O (D (-clock n) v)) - v‖ = _
  rw [outside, map_sub, burnolMultiplicativeDilation_neg_eq_symm, (D (clock n)).apply_symm_apply]
  rw [sub_right_comm, sub_self, zero_sub, norm_neg, (D (clock n)).norm_map]

/-- These pulled outside fields recover the full original L² value in norm. -/
theorem actual_clock_recovers (v : BurnolL2) :
    Tendsto (fun n => readClock n v) atTop (𝓝 v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => (actual_clock_error n v).le.trans (physical_loss_bound n v))
  simpa only [norm_zero] using (gap_projection_tendsto_zero (F v)).norm

/-- The actual outside observations recover the ambient norm along the same clock. -/
theorem actual_clock_outside_norm (v : BurnolL2) :
    Tendsto (fun n => ‖O (D (-clock n) v)‖) atTop (𝓝 ‖v‖) := by
  have norm_read (n : ℕ) : ‖readClock n v‖ = ‖O (D (-clock n) v)‖ :=
    (D (clock n)).norm_map _
  simpa only [norm_read] using (actual_clock_recovers v).norm

end OriginalRSourceJointContact.OutsideHistory.ClockReconstruction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.OutsideHistory

open Filter BurnolPhysicalState SourceGeneratedActionObservationHistory
open OriginalRSourceJointContact.OutsideHistory.ClockReconstruction
open OriginalRSourceJointContact.OutsideHistory.DilationFromPowers
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
open scoped Topology
open private successor_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.Kernel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "A" => sourceStep observation nontrivial half
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "R" => burnolDirectRightResolventCLM
local notation "Dilation" => burnolMultiplicativeDilation

private theorem clock_kernel (n : ℕ) :
    LinearMap.ker (sourceMap A outsideRead) ≤
      LinearMap.ker ((readClock n).toLinearMap.comp Inv.pairTotal) := by
  intro pair invisible
  have silent (i : ℕ) : O ((R c ^ (i+1)) (Inv.pairTotal pair)) = 0 := by
    rw [← successor_read observation nontrivial half pair i]
    exact (mem_kernel_iff A outsideRead pair).mp invisible (i+1)
  have actual := observed_inward_zero O c (Inv.pairTotal pair) silent
    (2 * clock n) (mul_pos (by norm_num) (clock_pos n))
  rw [show -(2 * clock n) / 2 = -clock n by ring] at actual
  change Dilation (clock n) (O (Dilation (-clock n) (Inv.pairTotal pair))) = 0
  rw [actual, map_zero]

/-- The clock factors through the original successor observations, and the head keeps its original slot. -/
def recoverPairAtClock (n : ℕ) : Model A outsideRead →ₗ[ℂ] SourcePair :=
  let total := (LinearMap.ker (sourceMap A outsideRead)).liftQ
    ((readClock n).toLinearMap.comp Inv.pairTotal) (clock_kernel observation nontrivial half n)
  (total - modelReadout A outsideRead).prod (modelReadout A outsideRead)

theorem clock_pair_head (n : ℕ) (pair : SourcePair) :
    (recoverPairAtClock observation nontrivial half n (projection A outsideRead pair)).2 = pair.2 :=
  rfl

theorem actual_model_clock_recovers (pair : SourcePair) :
    Tendsto (fun n => recoverPairAtClock observation nontrivial half n
      (projection A outsideRead pair)) atTop (𝓝 pair) := by
  have total := (actual_clock_recovers (Inv.pairTotal pair)).sub
    (tendsto_const_nhds (x := pair.2) (f := (atTop : Filter ℕ)))
  have pair_read : (Inv.pairTotal pair - pair.2, pair.2) = pair :=
    Prod.ext (add_sub_cancel_right _ _) rfl
  change Tendsto (fun n => (readClock n (Inv.pairTotal pair) - pair.2, pair.2)) atTop (𝓝 pair)
  have converges : Tendsto (fun n => (readClock n (Inv.pairTotal pair) - pair.2, pair.2)) atTop
      (𝓝 (Inv.pairTotal pair - pair.2, pair.2)) := total.prodMk_nhds tendsto_const_nhds
  rwa [pair_read] at converges

variable (depth ordinal : ℕ)
local notation "source" => D.input observation nontrivial half depth

/-- The same original Division supplies the old and next clock limits and the same-root whole. -/
theorem actual_division_clock_current_next :
    let model := projection A outsideRead (source ordinal)
    Tendsto (fun n => recoverPairAtClock observation nontrivial half n model) atTop (𝓝 (source ordinal)) ∧
    Tendsto (fun n => recoverPairAtClock observation nontrivial half n (modelAction A outsideRead model))
      atTop (𝓝 (source (ordinal+1))) ∧
    type_of% (actual_division_action_same_root observation nontrivial half depth ordinal) := by
  refine ⟨actual_model_clock_recovers observation nontrivial half _, ?_,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩
  rw [modelAction_source, actual_source_step]
  exact actual_model_clock_recovers observation nontrivial half _

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_division_clock_current_next"

end OriginalKCofinalFullBranchFibre.OutsideHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
