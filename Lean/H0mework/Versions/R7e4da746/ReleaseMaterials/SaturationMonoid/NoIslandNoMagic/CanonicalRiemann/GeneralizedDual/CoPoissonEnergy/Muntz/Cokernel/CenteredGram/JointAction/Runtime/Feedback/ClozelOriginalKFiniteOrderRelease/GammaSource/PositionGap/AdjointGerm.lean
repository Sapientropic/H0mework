import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ContinuitySource

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.AdjointGerm

open Complex Filter Set BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKFiniteOrderRelease.UnitMellin.ContinuitySource
open scoped Topology

open private right_quarter below_half damping_read denominator_ne adjoint_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private coordinate_eq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource
open private source_right_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource

local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "T" => sourceCayley
local notation "δ" => sourceDamping
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- All members of the vertical chart retain the original conjugate real part. -/
def probe (c : BurnolCompletedMellinCoordinate) (t : ℝ) : BurnolCompletedMellinCoordinate where
  value := star c.value + (t:ℂ)*Complex.I
  rightHalf := by simpa [Complex.star_def, Complex.mul_re] using c.rightHalf
  belowOne := by simpa [Complex.star_def, Complex.mul_re] using c.belowOne

theorem probe_zero (c : BurnolCompletedMellinCoordinate) : probe c 0 = d c := by
  apply coordinate_eq
  change star c.value + (↑(0:ℝ):ℂ)*Complex.I = star c.value
  simp

theorem probe_continuous (c : BurnolCompletedMellinCoordinate) : Continuous (fun t => (probe c t).value) := by
  change Continuous (fun t : ℝ => star c.value + (t:ℂ)*Complex.I)
  fun_prop

def denominator (c : BurnolCompletedMellinCoordinate) (t : ℝ) : ℂ := c.value/2+(probe c t).value/2-1/2

def factor (c : BurnolCompletedMellinCoordinate) (t : ℝ) : ℂ := gapMultiplier c ((probe c t).value/2)

theorem denominator_continuous (c : BurnolCompletedMellinCoordinate) : Continuous (denominator c) := by
  unfold denominator
  exact (continuous_const.add ((probe_continuous c).div_const (2:ℂ))).sub continuous_const

theorem denominator_nonzero (c : BurnolCompletedMellinCoordinate) (t : ℝ) : denominator c t ≠ 0 :=
  denominator_ne c ((probe c t).value/2) (right_quarter (probe c t))

theorem factor_read (c : BurnolCompletedMellinCoordinate) (t : ℝ) :
    factor c t = ((t:ℂ)*Complex.I/2) / denominator c t := by
  unfold factor gapMultiplier denominator
  congr 1
  change (star c.value+(t:ℂ)*Complex.I)/2-star c.value/2=(t:ℂ)*Complex.I/2
  ring

private theorem factor_zero (c : BurnolCompletedMellinCoordinate) : factor c 0 = 0 := by
  rw [factor_read]
  simp

private theorem factor_nonzero (c : BurnolCompletedMellinCoordinate) {t : ℝ} (away : t ≠ 0) : factor c t ≠ 0 := by
  rw [factor_read]
  exact div_ne_zero (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr away) Complex.I_ne_zero)
    (by norm_num)) (denominator_nonzero c t)

private theorem factor_continuous (c : BurnolCompletedMellinCoordinate) : Continuous (factor c) := by
  rw [show factor c = (fun t : ℝ => ((t:ℂ)*Complex.I/2) / denominator c t) from funext (factor_read c)]
  exact (((Complex.continuous_ofReal.mul continuous_const).div_const (2:ℂ)).div
    (denominator_continuous c) (denominator_nonzero c))

private theorem price_continuousAt (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    ContinuousAt (fun t => M (probe c t) v) 0 :=
  actual_ambient_mellin_tendsto (probe c 0) v (probe c) (probe_continuous c).continuousAt

private theorem extend_puncture {f g : ℝ → ℂ} (fAt : ContinuousAt f 0) (gAt : ContinuousAt g 0)
    (agree : f =ᶠ[𝓝[≠] (0:ℝ)] g) : f =ᶠ[𝓝 (0:ℝ)] g := by
  have lf : Tendsto f (𝓝[≠] (0:ℝ)) (𝓝 (f 0)) := fAt.mono_left nhdsWithin_le_nhds
  have lg : Tendsto g (𝓝[≠] (0:ℝ)) (𝓝 (g 0)) := gAt.mono_left nhdsWithin_le_nhds
  have center : f 0 = g 0 := tendsto_nhds_unique lf (lg.congr' agree.symm)
  filter_upwards [eventually_nhdsWithin_iff.mp agree] with t paid
  by_cases same : t = 0
  · simpa only [same] using center
  · exact paid same

private theorem remove_factor (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (gap : (T c).adjoint v ∈ G) (n : Nat) (coefficient : ℝ → ℂ) (continuous : ContinuousAt coefficient 0)
    (written : (fun t => M (probe c t) v) =ᶠ[𝓝 (0:ℝ)] fun t => (factor c t)^(n+1)*coefficient t) :
    (fun t => M (probe c t) ((T c).adjoint v)) =ᶠ[𝓝 (0:ℝ)] fun t => (factor c t)^n*coefficient t := by
  apply extend_puncture (price_continuousAt c _) (((factor_continuous c).continuousAt.pow n).mul continuous)
  have away : ∀ᶠ t : ℝ in 𝓝[≠] (0:ℝ), t ≠ 0 := self_mem_nhdsWithin
  filter_upwards [written.filter_mono nhdsWithin_le_nhds, away] with t source off
  let reader := probe c t
  let w := reader.value/2
  have chart : burnolDivisionCompletedMellinCoordinate w (right_quarter reader) (below_half reader) = reader := by
    apply coordinate_eq
    change 2*(reader.value/2)=reader.value
    ring
  have actual := actual_gap_cayley_scalar c ((T c).adjoint v) gap w (right_quarter reader) (below_half reader)
  rw [chart, source_right_inverse] at actual
  change M reader v = factor c t * M reader ((T c).adjoint v) at actual
  change M reader ((T c).adjoint v) = (factor c t)^n*coefficient t
  apply mul_left_cancel₀ (factor_nonzero c off)
  rw [← actual, source, pow_succ', mul_assoc]

/-- One true adjoint step removes one actual forward factor, and the last nonzero read pays the exit. -/
theorem actual_adjoint_germ_exit (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (gap : v ∈ G) (even : reflectL2 v = v) (m : Nat) (coefficient : ℝ → ℂ)
    (continuous : ContinuousAt coefficient 0) (nonzero : coefficient 0 ≠ 0)
    (written : (fun t => M (probe c t) v) =ᶠ[𝓝 (0:ℝ)] fun t => (factor c t)^m*coefficient t) :
    (∀ i < m, M (d c) ((((T c).adjoint)^i) v) = 0) ∧
      M (d c) ((((T c).adjoint)^m) v) = coefficient 0 ∧
      (((T c).adjoint)^m) v ∈ G ∧ ¬ (((T c).adjoint)^(m+1)) v ∈ G := by
  induction m generalizing v with
  | zero =>
    have price := written.eq_of_nhds
    rw [probe_zero, pow_zero, one_mul] at price
    refine ⟨fun i impossible => (Nat.not_lt_zero i impossible).elim, ?_, ?_, ?_⟩
    · simpa only [pow_zero, one_apply_eq_self] using price
    · simpa only [pow_zero, one_apply_eq_self] using gap
    · rw [zero_add, pow_one]
      exact fun stays => nonzero (price.symm.trans ((actual_gap_cayley_adjoint_iff c v gap even).1 stays))
  | succ n earlier =>
    have zero := written.eq_of_nhds
    rw [probe_zero, factor_zero, pow_succ', zero_mul, zero_mul] at zero
    let prior := (T c).adjoint v
    have before : prior ∈ G := (actual_gap_cayley_adjoint_iff c v gap even).2 zero
    have symmetric : reflectL2 prior = prior := adjoint_even c v even
    have paid := remove_factor c v before n coefficient continuous written
    obtain ⟨lower, head, last, outside⟩ := earlier prior before symmetric paid
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i within
      cases i with
      | zero => simpa only [pow_zero, one_apply_eq_self] using zero
      | succ i =>
        rw [pow_succ, mul_apply_eq_comp]
        exact lower i (Nat.lt_of_succ_lt_succ within)
    · rw [pow_succ, mul_apply_eq_comp]
      exact head
    · rw [pow_succ, mul_apply_eq_comp]
      exact last
    · rw [pow_succ, mul_apply_eq_comp]
      exact outside

end OriginalKFiniteOrderRelease.PositionGapCayley.AdjointGerm
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
