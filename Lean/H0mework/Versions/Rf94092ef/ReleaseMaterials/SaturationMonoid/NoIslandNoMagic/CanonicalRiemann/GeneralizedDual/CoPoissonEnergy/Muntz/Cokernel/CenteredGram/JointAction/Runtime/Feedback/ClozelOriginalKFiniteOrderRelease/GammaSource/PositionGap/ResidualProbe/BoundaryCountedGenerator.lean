import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.RelativeCell
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedInverse
import H0mework.Versions.R7e4da746.Arithmetic.RiemannFirstSource.GeneratorResolvent

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedGenerator

open BurnolPhysicalState MeasureTheory Set Filter OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology

open private headUnit remainder remainder_apply BoundaryCountedInverse.normalized normalized_strict mass
  from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedInverse

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "U" => burnolMultiplicativeDilation
local notation "smallCell" => BoundaryCountedInverse.normalized

private def clockTime (t : ℝ) : ℝ := 2 * Real.log (1 + t)

private def weight (t : ℝ) : ℂ :=
  positiveMellinQuarterRightResolventCharacter (1 / 2) (-clockTime t)

private def trajectory (value : BurnolL2) (t : ℝ) : BurnolL2 :=
  weight t • U (-clockTime t / 2) value

private def defect (value : BurnolL2) (t : ℝ) : BurnolL2 :=
  value - trajectory value t

private theorem clockTime_zero : clockTime 0 = 0 := by simp [clockTime]

private theorem weight_zero : weight 0 = 1 := by
  rw [weight, clockTime_zero, neg_zero, positiveMellinQuarterRightResolventCharacter_exp]
  simp

private theorem defect_zero (value : BurnolL2) : defect value 0 = 0 := by
  rw [defect, trajectory, weight_zero, clockTime_zero, neg_zero, zero_div,
    burnolMultiplicativeDilation_zero, one_smul, sub_self]

private theorem trajectory_continuous (value : BurnolL2) : ContinuousOn (trajectory value) (Icc 0 1) := by
  have localLog : ContinuousOn (fun t : ℝ => Real.log (1+t)) (Icc 0 1) :=
    Real.continuousOn_log.comp (continuous_const.add continuous_id).continuousOn
      (fun t member => by
        have pos : 0 < 1+t := by linarith [member.1]
        exact pos.ne')
  have clock : ContinuousOn clockTime (Icc 0 1) := localLog.const_mul _
  have factor : ContinuousOn weight (Icc 0 1) := by
    have regular : Continuous (positiveMellinQuarterRightResolventCharacter (1/2)) := by
      unfold positiveMellinQuarterRightResolventCharacter
      exact (positiveMellinQuarterRightResolventWeight_continuous _).comp continuous_neg
    exact regular.comp_continuousOn clock.neg
  exact factor.smul ((burnolMultiplicativeDilation_stronglyContinuous value).comp_continuousOn (clock.neg.div_const _))

private theorem scaled_weight (N r : ℝ) (nPositive : 0 < N) (rPositive : 0 < r) :
    (Real.sqrt N : ℂ) * (Real.sqrt r : ℂ)⁻¹ = weight ((r-N)/N) := by
  have ratio : 1 + (r-N)/N = r/N := by field_simp [nPositive.ne']; ring
  have real : Real.sqrt N * (Real.sqrt r)⁻¹ = Real.exp (-Real.log (r/N)/2) := by
    rw [← div_eq_mul_inv, ← inv_div, ← Real.sqrt_div rPositive.le,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos rPositive nPositive), ← Real.exp_neg]
    congr 1
    ring
  rw [weight, clockTime, ratio, positiveMellinQuarterRightResolventCharacter_exp]
  push_cast
  have exponent : ((1 / 2 : ℂ) - 1 / 4) * -(2 * (Real.log (r/N) : ℂ)) =
      ((-Real.log (r/N)/2 : ℝ) : ℂ) := by push_cast; ring
  rw [exponent, ← Complex.ofReal_exp, ← real, Complex.ofReal_mul, Complex.ofReal_inv]

private theorem normalized_read (N : Nat) (positive : 0 < N) (value : BurnolL2) :
    smallCell N positive value = ∫ t : ℝ in (0 : ℝ)..1, trajectory value (t/N) := by
  let lo : ℝ := N
  have loPositive : 0 < lo := by
    change (0 : ℝ) < (N : ℝ)
    exact_mod_cast positive
  have ordered : lo ≤ lo+1 := by linarith
  let undo : End := (↑(headUnit N positive)⁻¹ : End)
  have integrable := (ContinuousChannels.channel_integrable (-1) (lo+1) value).mono_set
    (Ioc_subset_Ioc loPositive.le le_rfl)
  have action : smallCell N positive value =
      ∫ r : ℝ in Ioc lo (lo+1), undo (ContinuousChannels.channel (-1) r value) := by
    change undo (remainder N value) = _
    rw [remainder_apply N positive]
    exact (undo.integral_comp_comm integrable).symm
  rw [action]
  have normalized : ∀ r ∈ Ioc lo (lo+1),
      undo (ContinuousChannels.channel (-1) r value) = trajectory value ((r-lo)/lo) := by
    intro r inside
    have rPositive := loPositive.trans inside.1
    have inverseDilation : (U (-Real.log lo)).symm = U (Real.log lo) := by
      simpa only [neg_neg] using (burnolMultiplicativeDilation_neg_eq_symm (-Real.log lo)).symm
    change (Real.sqrt lo : ℂ) • (U (-Real.log lo)).symm (ContinuousChannels.channel (-1) r value) = _
    rw [ContinuousChannels.channel, neg_one_mul, inverseDilation, map_smul, smul_smul,
      burnolMultiplicativeDilation_add, scaled_weight lo r loPositive rPositive, trajectory, clockTime]
    have ratio : 1 + (r-lo)/lo = r/lo := by field_simp [loPositive.ne']; ring
    rw [ratio, Real.log_div rPositive.ne' loPositive.ne']
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc normalized, ← intervalIntegral.integral_of_le ordered]
  have shifted := intervalIntegral.integral_comp_add_right (f := fun r : ℝ => trajectory value ((r-lo)/lo))
    (a := (0 : ℝ)) (b := 1) lo
  simpa only [zero_add, add_comm 1 lo, add_sub_cancel_right] using shifted.symm

/-- The shifted clock acts through the actual normalized counted cell. -/
def clock (coordinate : ℂ) (N : Nat) (positive : 0 < N) : End :=
  ((N : ℂ) + coordinate - 1/2) • (1 : End) - (N : ℂ) • smallCell N positive

theorem clock_source (coordinate : ℂ) (N : Nat) (positive : 0 < N) (value : BurnolL2) :
    clock coordinate N positive value =
      (∫ t : ℝ in (0 : ℝ)..1, (N : ℝ) • defect value (t/N)) + (coordinate-1/2) • value := by
  have nPositive : (0 : ℝ) < N := by exact_mod_cast positive
  have nLarge : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have continuous : ContinuousOn (fun t : ℝ => trajectory value (t/N)) (Icc 0 1) :=
    (trajectory_continuous value).comp (continuous_id.div_const _).continuousOn
      (fun t inside => ⟨div_nonneg inside.1 nPositive.le, (div_le_one nPositive).mpr (inside.2.trans nLarge)⟩)
  have integrable : IntervalIntegrable (fun t : ℝ => trajectory value (t/N)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact continuous
  have scaled : (∫ t : ℝ in (0 : ℝ)..1, (N : ℝ) • defect value (t/N)) =
      (N : ℂ) • ∫ t : ℝ in (0 : ℝ)..1, (value - trajectory value (t/N)) := by
    let A : End := (N : ℂ) • 1
    change (∫ t : ℝ in (0 : ℝ)..1, (N : ℝ) • (value - trajectory value (t/N))) = _
    exact A.intervalIntegral_comp_comm ((intervalIntegrable_const (c := value)).sub integrable)
  rw [scaled, intervalIntegral.integral_sub intervalIntegrable_const integrable,
    intervalIntegral.integral_const, sub_zero, one_smul, ← normalized_read N positive]
  change ((N : ℂ) + coordinate - 1/2) • value - (N : ℂ) • smallCell N positive value = _
  module

private theorem clockTime_derivative : HasDerivAt clockTime (2 : ℝ) 0 := by
  have shifted : HasDerivAt (fun t : ℝ => 1+t) 1 0 := (hasDerivAt_id 0).const_add 1
  have outer : HasDerivAt Real.log ((1+0 : ℝ)⁻¹) (1+0) := Real.hasDerivAt_log (by norm_num)
  have generated := (outer.comp 0 shifted).const_mul (2 : ℝ)
  convert! generated using 1
  norm_num

private theorem defect_derivative (coordinate : ℂ) (right : 1/4 < coordinate.re) (value : BurnolL2) :
    HasDerivAt (defect (-burnolDirectRightResolvent coordinate value))
      ((2 : ℝ) • (value - (coordinate - 1/2) • (-burnolDirectRightResolvent coordinate value))) 0 := by
  let old := burnolDirectRightResolvent coordinate value
  have factor : HasDerivAt weight ((-2 : ℝ) • ((1/2 : ℂ)-1/4)) 0 :=
    (positiveMellinQuarterRightResolventCharacter_hasDerivAt (1/2)).scomp_of_eq 0
      clockTime_derivative.neg (by rw [clockTime_zero, neg_zero])
  have orbit : HasDerivAt (fun t => U (-clockTime t/2) old)
      ((2 : ℝ) • ((coordinate-1/4) • old + value)) 0 :=
    (burnolDirectRightResolventOrbit_hasDerivAt coordinate right value).scomp_of_eq 0
      clockTime_derivative clockTime_zero.symm
  have generated := (factor.smul orbit).sub_const old
  have same : defect (-old) = fun t => weight t • U (-clockTime t/2) old - old := by
    funext t
    simp only [defect, trajectory, map_neg, smul_neg]
    abel
  have derivative :
      weight 0 • ((2 : ℝ) • ((coordinate-1/4) • old + value)) +
        ((-2 : ℝ) • ((1/2 : ℂ)-1/4)) • U (-clockTime 0/2) old =
        (2 : ℝ) • (value - (coordinate-1/2) • (-old)) := by
    rw [weight_zero, one_smul, clockTime_zero, neg_zero, zero_div, burnolMultiplicativeDilation_zero]
    simp only [Complex.real_smul, Complex.ofReal_ofNat, Complex.ofReal_neg, smul_add, smul_sub, smul_neg]
    module
  rw [derivative] at generated
  rw [same]
  exact generated

/-- On the true original resolvent image the actual finite clock converges to the source. -/
theorem clock_applied_tendsto (coordinate : ℂ) (right : 1/4 < coordinate.re) (value : BurnolL2) :
    Tendsto (fun n : Nat => clock coordinate (n+1) (Nat.succ_pos n)
      (-burnolDirectRightResolvent coordinate value)) atTop (𝓝 value) := by
  let old := -burnolDirectRightResolvent coordinate value
  have derivative := SourceGeneratedRelativeCell.integral_tendsto (defect_zero old)
    (defect_derivative coordinate right value) (continuousOn_const.sub (trajectory_continuous old))
  have generated := derivative.add_const ((coordinate-1/2) • old)
  have limit : (1/2 : ℝ) • ((2 : ℝ) • (value - (coordinate-1/2) • old)) +
      (coordinate-1/2) • old = value := by
    rw [smul_smul, show (1/2 : ℝ)*2=1 by norm_num, one_smul, sub_add_cancel]
  rw [limit] at generated
  refine generated.congr' (Eventually.of_forall (fun n => ?_))
  change (∫ t : ℝ in (0 : ℝ)..1, (n+1 : ℝ) • defect old (t/(n+1 : ℝ))) +
      (coordinate-1/2) • old = clock coordinate (n+1) (Nat.succ_pos n) old
  rw [clock_source, Nat.cast_add, Nat.cast_one]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedGenerator
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
