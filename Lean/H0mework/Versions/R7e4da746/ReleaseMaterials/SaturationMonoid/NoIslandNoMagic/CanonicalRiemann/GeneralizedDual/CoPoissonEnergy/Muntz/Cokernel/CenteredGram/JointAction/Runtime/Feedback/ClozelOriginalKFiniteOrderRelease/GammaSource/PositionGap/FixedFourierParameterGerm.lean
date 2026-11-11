import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierSeedParameterWrite
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideFeedbackHistory

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead

open BurnolPhysicalState Filter Set OriginalCofinalFourierJet SelfOrbit
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped InnerProductSpace Topology

open private full_outside_write from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideFeedbackHistory
open private scale_power_ne_one coordinate_ne_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierXiOutsideStart
open private bare_factor bare_analytic bare_nonzero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
open private observed_jet from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.DilationFromPowers

local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "V" => physicalOutsideColumn
local notation "K" => burnolCompletedMellinRieszVector
local notation "seed" => (burnolPaCombApproximation 0:BurnolL2)
local notation "bare" => generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner

/-- The fixed original Fourier–K reader on the actual variable-parameter first resolvent. -/
def fixedPrice (anchor : BurnolCompletedMellinCoordinate) (s : ℂ) : ℂ :=
  inner ℂ (fourierL2 (K anchor : BurnolL2)) (burnolDirectRightResolvent (s/2) seed)

def crossField (anchor : BurnolCompletedMellinCoordinate) (s : ℂ) : BurnolL2 :=
  (2:ℂ) • exteriorFamily s - (s-anchor.value) • selfAction anchor (exteriorFamily s)

def normalized (anchor : BurnolCompletedMellinCoordinate) (s : ℂ) : ℂ :=
  inner ℂ (V anchor) (crossField anchor s) / inner ℂ (V anchor) (V anchor)

private theorem right_quarter (parameter : BurnolCompletedMellinCoordinate) :
    1/4 < (parameter.value/2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [parameter.rightHalf]

private theorem column_nonzero (anchor : BurnolCompletedMellinCoordinate) : V anchor ≠ 0 := by
  simpa only [column, pow_zero, one_apply_eq_self] using
    (column_linearIndependent anchor).ne_zero 0

private theorem column_square_nonzero (anchor : BurnolCompletedMellinCoordinate) :
    inner ℂ (V anchor) (V anchor) ≠ 0 := fun zero => column_nonzero anchor (inner_self_eq_zero.mp zero)

/-- The original fixed action sends the variable first exterior through its own two terms. -/
theorem actual_cross_source (anchor parameter : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta anchor.value = 0) :
    ((parameter.value-anchor.value)*fixedPrice anchor parameter.value) • V anchor =
      arithmeticMoment parameter.value • crossField anchor parameter.value := by
  have silent : O (R anchor seed) = 0 := by
    rw [original_first_outside]
    simp [arithmeticMoment, zero]
  have identity := congrArg (fun v : BurnolL2 => O v)
    (burnolDirectRightResolvent_identity (anchor.value/2) (parameter.value/2)
      (right_quarter anchor) (right_quarter parameter) seed)
  change O (R anchor seed - R parameter seed) =
      (O (((anchor.value/2)-(parameter.value/2)) • R anchor (R parameter seed))) at identity
  rw [map_sub, map_smul, silent, original_first_outside parameter, zero_sub] at identity
  have action := full_outside_write anchor (R parameter seed)
  rw [original_first_outside parameter, map_smul] at action
  change O (R anchor (R parameter seed)) =
    (-2 * arithmeticMoment parameter.value) • selfAction anchor (V parameter) +
      (-2 * fixedPrice anchor parameter.value) • V anchor at action
  rw [action] at identity
  rw [crossField, exteriorFamily_actual]
  linear_combination (norm := module) -identity

/-- A fixed original Fourier–K price receives the arithmetic factor from the actual source write. -/
theorem actual_cross_factor (anchor parameter : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta anchor.value = 0) :
    (parameter.value-anchor.value)*fixedPrice anchor parameter.value =
      arithmeticMoment parameter.value * normalized anchor parameter.value := by
  unfold normalized
  rw [← mul_div_assoc]
  apply (eq_div_iff (column_square_nonzero anchor)).2
  simpa only [inner_smul_right] using
    congrArg (inner ℂ (V anchor)) (actual_cross_source anchor parameter zero)

theorem normalized_at_anchor (anchor : BurnolCompletedMellinCoordinate) :
    normalized anchor anchor.value = 2 := by
  simp only [normalized, crossField, exteriorFamily_actual, sub_self, zero_smul, sub_zero, inner_smul_right]
  exact mul_div_cancel_right₀ _ (column_square_nonzero anchor)

private theorem normalized_analytic (anchor parameter : BurnolCompletedMellinCoordinate) :
    AnalyticAt ℂ (normalized anchor) parameter.value := by
  have exterior := exteriorFamily_analytic parameter
  have acted := ((selfAction anchor).analyticAt _).comp exterior
  have two : AnalyticAt ℂ (fun _ : ℂ => (2:ℂ)) parameter.value := analyticAt_const
  have difference : AnalyticAt ℂ (fun s : ℂ => s-anchor.value) parameter.value :=
    analyticAt_id.sub analyticAt_const
  have cross : AnalyticAt ℂ (crossField anchor) parameter.value :=
    (two.smul exterior).sub (difference.smul acted)
  exact (((innerSL ℂ (V anchor)).analyticAt _).comp cross).div analyticAt_const
    (column_square_nonzero anchor)

private theorem fixed_analytic (anchor parameter : BurnolCompletedMellinCoordinate) :
    AnalyticAt ℂ (fixedPrice anchor) parameter.value :=
  ((innerSL ℂ (fourierL2 (K anchor:BurnolL2))).analyticAt _).comp
    (OriginalRResolventParameterJet.parameter_analytic parameter seed)

theorem actual_other_zero_price (anchor parameter : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta anchor.value = 0) (other : riemannZeta parameter.value = 0)
    (distinct : parameter.value ≠ anchor.value) : fixedPrice anchor parameter.value = 0 := by
  have source := actual_cross_factor anchor parameter zero
  rw [show arithmeticMoment parameter.value=0 by simp [arithmeticMoment, other], zero_mul] at source
  exact (mul_eq_zero.mp source).resolve_left (sub_ne_zero.mpr distinct)

private def momentFactor (s : ℂ) : ℂ := 2 * ((((3/2:ℝ):ℂ)^s-1)/s)

private theorem momentFactor_analytic (anchor : BurnolCompletedMellinCoordinate) :
    AnalyticAt ℂ momentFactor anchor.value := by
  have scale : AnalyticAt ℂ (fun s : ℂ => ((3/2:ℝ):ℂ)^s) anchor.value :=
    (differentiable_id.const_cpow (Or.inl (by norm_num : ((3/2:ℝ):ℂ) ≠ 0))).analyticAt _
  exact analyticAt_const.mul
    ((scale.sub analyticAt_const).div analyticAt_id (coordinate_ne_zero anchor))

private theorem momentFactor_nonzero (anchor : BurnolCompletedMellinCoordinate) :
    momentFactor anchor.value ≠ 0 :=
  mul_ne_zero (by norm_num)
    (div_ne_zero (sub_ne_zero.mpr (scale_power_ne_one anchor)) (coordinate_ne_zero anchor))

private theorem original_cross_order (anchor : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta anchor.value = 0) :
    1 + analyticOrderAt (fixedPrice anchor) anchor.value = (xiOrder anchor : ℕ∞) := by
  let leading (s : ℂ) := bare anchor.value s * (momentFactor s * normalized anchor s)
  have leadingAnalytic : AnalyticAt ℂ leading anchor.value :=
    (bare_analytic anchor).mul ((momentFactor_analytic anchor).mul (normalized_analytic anchor anchor))
  have leadingNonzero : leading anchor.value ≠ 0 := by
    unfold leading
    rw [normalized_at_anchor]
    exact mul_ne_zero (bare_nonzero anchor) (mul_ne_zero (momentFactor_nonzero anchor) (by norm_num))
  have near : ∀ᶠ s : ℂ in 𝓝 anchor.value, (1/2:ℝ)<s.re ∧ s.re<1 :=
    ((Complex.continuous_re.tendsto anchor.value).eventually (Ioi_mem_nhds anchor.rightHalf)).and
      ((Complex.continuous_re.tendsto anchor.value).eventually (Iio_mem_nhds anchor.belowOne))
  have germ : (fun s : ℂ => s-anchor.value) * fixedPrice anchor =ᶠ[𝓝 anchor.value]
      (fun s => (s-anchor.value)^(xiOrder anchor) • leading s) := by
    filter_upwards [near, bare_factor anchor] with s qualifies actual
    let parameter : BurnolCompletedMellinCoordinate := ⟨s, qualifies.1, qualifies.2⟩
    have written := actual_cross_factor anchor parameter zero
    change (s-anchor.value)*fixedPrice anchor s = arithmeticMoment s * normalized anchor s at written
    change (s-anchor.value)*fixedPrice anchor s = (s-anchor.value)^(xiOrder anchor) • leading s
    rw [written, arithmeticMoment, actual]
    simp only [smul_eq_mul, leading, momentFactor]
    ring
  have linear : AnalyticAt ℂ (fun s : ℂ => s-anchor.value) anchor.value :=
    analyticAt_id.sub analyticAt_const
  have actual := (linear.mul (fixed_analytic anchor anchor)).analyticOrderAt_eq_natCast.mpr
    ⟨leading, leadingAnalytic, leadingNonzero, germ⟩
  rw [analyticOrderAt_mul linear (fixed_analytic anchor anchor), analyticOrderAt_id_sub_const_self] at actual
  exact actual

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth

include nontrivial in
/-- The fixed original Fourier–K analytic germ opens one action before the exterior Xi order. -/
theorem actual_fixed_price_order :
    analyticOrderAt (fixedPrice c) (c).value = ((m-1 : Nat) : ℕ∞) := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have paid := original_cross_order c observation.mathlibZero
  have count : ((m-1 : Nat):ℕ∞)+1 = (m:ℕ∞) := by
    exact_mod_cast (Nat.sub_add_cancel (Nat.succ_le_of_lt positive))
  apply ENat.add_left_injective_of_ne_top (show (1:ℕ∞) ≠ ⊤ by simp)
  exact (add_comm _ _).trans (paid.trans count.symm)

include nontrivial in
/-- Every decoded price of the original exterior is a coefficient of the same fixed germ. -/
theorem actual_decoded_lag_jet (ordinal : Nat) (j : Fin (ordinal+2)) :
    let n := m+(ordinal+1-j.val)-1
    iteratedDeriv n (fixedPrice c) (c).value =
      ((n.factorial : ℂ) / (2:ℂ)^n) * FeedbackHistory.decodedLag c (ordinal+1) (input ordinal).2 j := by
  let n := m+(ordinal+1-j.val)-1
  change iteratedDeriv n (fixedPrice c) (c).value = _
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have index : n+1=m+(ordinal+1-j.val) := by dsimp [n]; omega
  let reader := innerSL ℂ (fourierL2 (K c : BurnolL2))
  have actual := observed_jet reader c seed n
  change iteratedDeriv n (fixedPrice c) (c).value =
    ((n.factorial : ℂ) / (2:ℂ)^n) •
      inner ℂ (fourierL2 (K c : BurnolL2)) (((R c)^(n+1)) seed) at actual
  rw [index] at actual
  rw [FeedbackHistory.actual_single_outside_history observation nontrivial half depth ordinal j]
  exact actual

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
