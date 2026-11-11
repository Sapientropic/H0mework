import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.BandSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward OriginalPaPhysicalGreen
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "K" => burnolCompletedMellinRieszVector
local notation "T" => burnolTateReciprocalL2
local notation "D" => burnolMultiplicativeDilation

def shiftedUnitTest (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  D (-Real.log 16) (unitTest c h)

/-- The actual shifted K difference has a smaller zero gap, before Tate is applied. -/
theorem actual_moved_gap (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h) :
    ∀ᵐ x : ℝ ∂volume, |x|≤q*Real.exp (-h) → movedTest c h x=0 := by
  have gap := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (burnolAmbientGap_ae (K c))
  have scaled := (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
    (r:=Real.exp h) (Real.exp_ne_zero h)).ae gap
  filter_upwards [gap,scaled,burnolMultiplicativeDilation_coeFn h (K c:BurnolL2),
    Lp.coeFn_sub (D h (K c:BurnolL2)) ((Real.exp (h/2):ℂ) • (K c:BurnolL2)),
    Lp.coeFn_smul (Real.exp (h/2):ℂ) (K c:BurnolL2)] with x direct shifted dilation difference scalar inside
  have small : |x|≤q := inside.trans (by
    have upper : Real.exp (-h)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)
    nlinarith)
  have moved : |Real.exp h*x|≤q := by
    rw [abs_mul,abs_of_pos (Real.exp_pos h)]
    calc
      _≤Real.exp h*(q*Real.exp (-h)) := mul_le_mul_of_nonneg_left inside (Real.exp_pos h).le
      _=q := by rw [mul_left_comm,←Real.exp_add];simp
  change (D h (K c:BurnolL2)-(Real.exp (h/2):ℂ) • (K c:BurnolL2)) x=0
  rw [difference,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul,dilation]
  change (Real.exp (h/2):ℂ)*(K c:BurnolL2) (Real.exp h*x)-
    (Real.exp (h/2):ℂ)*(K c:BurnolL2) x=0
  have actual : (K c:BurnolL2) (Real.exp h*x)=burnolConstantGapCoefficient burnolUnscaledCommonGapRadius (K c) := by
    simpa only [smul_eq_mul] using shifted (abs_le.mp moved)
  rw [direct (abs_le.mp small),actual,sub_self]

/-- The transformed test is the literal one used by the original fixed consumer. -/
theorem actual_radius_test (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    shiftedUnitTest c h=OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest c h := rfl

theorem actual_shifted_test_fourier (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    fourierL2 (shiftedUnitTest c h)=D (Real.log 16) (T (movedTest c h)) := by
  rw [shiftedUnitTest,fourierL2_burnolMultiplicativeDilation,neg_neg,unitTest,
    fourierL2.apply_symm_apply]

/-- Tate followed by the actual radius conversion exposes only the first Fourier cell. -/
theorem actual_transformed_outside (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h) :
    ∀ᵐ x : ℝ ∂volume, q*Real.exp h < |x| → fourierL2 (shiftedUnitTest c h) x=0 := by
  let v:=movedTest c h
  let r:=q*Real.exp (-h)
  have raw : (v:ℝ→ℂ)=ᵐ[volume] fun x=>if r < |x| then v x else 0 := by
    filter_upwards [actual_moved_gap c h nonnegative] with x zero
    by_cases outside:r < |x|
    · rw [if_pos outside]
    · rw [if_neg outside]
      exact zero (le_of_not_gt outside)
  have tate:=burnolTateReciprocalRaw_ae_congr (Lp.memLp v) ((Lp.memLp v).ae_eq raw) raw
  have full : (T v:ℝ→ℂ)=ᵐ[volume] burnolTateReciprocalRaw (fun x=>if r < |x| then v x else 0) :=
    (burnolTateReciprocalL2_coeFn v).trans tate
  have pull:=(Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
    (r:=Real.exp (Real.log 16)) (Real.exp_ne_zero _)).ae full
  rw [actual_shifted_test_fourier]
  filter_upwards [burnolMultiplicativeDilation_coeFn (Real.log 16) (T v),pull] with x dilation read outside
  rw [dilation]
  change (Real.exp (Real.log 16/2):ℂ)*(T v) (Real.exp (Real.log 16)*x)=0
  rw [show (T v) (Real.exp (Real.log 16)*x)=
    burnolTateReciprocalRaw (fun x=>if r < |x| then v x else 0) (Real.exp (Real.log 16)*x) from read]
  rw [Real.exp_log (by norm_num:(0:ℝ)<16)]
  have radiusPositive : 0<r := by dsimp only [r];positivity
  have absolutePositive : 0< |x| := (by positivity : 0<q*Real.exp h).trans outside
  have product : 1 < (16*|x|)*r := by
    calc
      1=(16*(q*Real.exp h))*r := by
        dsimp only [r]
        have cancel:Real.exp h*Real.exp (-h)=1 := by rw [←Real.exp_add];simp
        nlinarith [cancel]
      _<(16*|x|)*r := mul_lt_mul_of_pos_right (by linarith) radiusPositive
  have small : |(16*x)⁻¹|≤r := by
    rw [abs_inv,abs_mul,abs_of_pos (by norm_num:(0:ℝ)<16)]
    exact (inv_le_iff_one_le_mul₀' (by positivity : 0<16*|x|)).mpr product.le
  rw [burnolTateReciprocalRaw,if_neg (not_lt_of_ge small),mul_zero,mul_zero]

/-- This support is derived from the original K gap, not assumed for the transformed test. -/
theorem actual_transformed_support (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h) :
    originalPhysicalCutoff (q*Real.exp h) (fourierL2 (shiftedUnitTest c h))=
      fourierL2 (shiftedUnitTest c h) := by
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn (q*Real.exp h) (fourierL2 (shiftedUnitTest c h)),
    actual_transformed_outside c h nonnegative] with x cutoff outside
  rw [cutoff]
  by_cases inside:x∈symmetricInterval (q*Real.exp h)
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside]
    exact (outside (lt_of_not_ge (fun small=>inside (abs_le.mp small)))).symm

end OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
