import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz OriginalKElementaryArithmeticAction.FreeParameter.Family OriginalKElementaryArithmeticAction.FreeParameter.FixedConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Model OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Consumer
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "E" => burnolQuarterZeroExtension
open private fourier_gap from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedEvaluator

/-- Both original FK contacts vanish on the half-window together, before any source parameter is chosen. -/
theorem actual_fourier_test_half_gap (c:BurnolCompletedMellinCoordinate) (h:ℝ) (bounded:h≤Real.log 2) :
 ∀ᵐ x:ℝ ∂volume,x∈symmetricInterval (q/2)→fourierTest c h x=0 := by
 let value:=fourierL2 (K c:BurnolL2)
 have gap:∀ᵐ x:ℝ ∂volume,x∈symmetricInterval q→value x=fourierMean c:=
  (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (fourier_gap c)
 have scaled:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp h*x) volume volume:=by
  simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (Real.exp_ne_zero h)
 have bound:Real.exp h≤2:=by
  simpa only [Real.exp_log (by norm_num:(0:ℝ)<2)] using Real.exp_le_exp.mpr bounded
 filter_upwards [Lp.coeFn_sub (burnolMultiplicativeDilation h value) ((Real.exp (h/2):ℂ)•value),
  Lp.coeFn_smul (Real.exp (h/2):ℂ) value,burnolMultiplicativeDilation_coeFn h value,gap,scaled.ae gap]
  with x difference scalar dilated original moved
 intro inside
 have current:x∈symmetricInterval q:=by
  have small:=abs_le.mpr inside
  exact abs_le.mp (by linarith : |x|≤q)
 have stays:Real.exp h*x∈symmetricInterval q:=by
  apply abs_le.mp
  rw [abs_mul,abs_of_pos (Real.exp_pos h)]
  exact (mul_le_mul_of_nonneg_right bound (abs_nonneg x)).trans
   (by have small:=abs_le.mpr inside;nlinarith)
 change (burnolMultiplicativeDilation h value-(Real.exp (h/2):ℂ)•value:BurnolL2) x=0
 rw [difference,Pi.sub_apply,scalar,Pi.smul_apply,dilated]
 change (Real.exp (h/2):ℂ)*value (Real.exp h*x)-(Real.exp (h/2):ℂ)*value x=0
 rw [original current,moved stays,sub_self]

/-- The full independent dual correction is invisible to this fixed true cotest for every free d. -/
theorem actual_free_dual_contact (c d:BurnolCompletedMellinCoordinate) (h:ℝ) (bounded:h≤Real.log 2) :
 inner ℂ (fourierTest c h) (CountingDual.value d)=
  inner ℂ (burnolQuarterRestriction (fourierTest c h)) (bModel (star d.value):Hq) := by
 let delta:=CountingDual.value d-E (burnolRieszSingleFourierSource d:Hq)
 have support:OriginalPaPhysicalGreen.originalPhysicalCutoff (q/2) delta=delta:=DualShell.limit_difference_support d
 have cutoff:=OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn (q/2) delta
 rw [support] at cutoff
 have zero:inner ℂ (fourierTest c h) delta=0:=by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [actual_fourier_test_half_gap c h bounded,cutoff] with x gap read
  by_cases inside:x∈symmetricInterval (q/2)
  · simp only [RCLike.inner_apply,starRingEnd_apply,gap inside,star_zero,mul_zero,Pi.zero_apply]
  · rw [read,indicator_of_notMem inside]
    simp
 have source:inner ℂ (fourierTest c h) (CountingDual.value d)=
   inner ℂ (fourierTest c h) (E (burnolRieszSingleFourierSource d:Hq)):=by
  rw [show delta=CountingDual.value d-E (burnolRieszSingleFourierSource d:Hq) from rfl,inner_sub_right] at zero
  exact sub_eq_zero.mp zero
 rw [source]
 change inner ℂ (fourierTest c h) (burnolQuarterRestriction.adjoint (burnolRieszSingleFourierSource d:Hq))=_
 rw [ContinuousLinearMap.adjoint_inner_right,actual_original_B_model]

/-- One actual source family contains both complete PC and CD parameter readings. -/
def completeJointModel (c:BurnolCompletedMellinCoordinate) (h:ℝ) (s:ℂ) : ℂ :=
 inner ℂ (movedTest c h) (wholeModel s)+
  inner ℂ (burnolQuarterRestriction (fourierTest c h)) (bModel s:Hq)

theorem complete_joint_model_analytic (c parameter:BurnolCompletedMellinCoordinate) (h:ℝ) :
 AnalyticAt ℂ (completeJointModel c h) parameter.value := by
 have whole:=((innerSL ℂ (movedTest c h)).analyticAt _).comp (whole_model_analytic parameter)
 have b:AnalyticAt ℂ (fun s:ℂ=>(bModel s:Hq)) parameter.value:=
  (burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL.analyticAt _).comp (original_B_model_analytic parameter)
 exact whole.add (((innerSL ℂ (burnolQuarterRestriction (fourierTest c h))).analyticAt _).comp b)

/-- The same fixed action reads both legs at every free source parameter; no neighboring zero assumption occurs. -/
theorem actual_free_joint_read (c d:BurnolCompletedMellinCoordinate) (h:ℝ) (bounded:h≤Real.log 2) :
 inner ℂ (movedTest c h) (wholeModel (star d.value))+inner ℂ (fourierTest c h) (CountingDual.value d)=
  completeJointModel c h (star d.value) := by
 rw [actual_free_dual_contact c d h bounded]
 rfl

/-- All four original moved prices are recognized inside that same freely generated family. -/
theorem actual_native_joint_read (c:BurnolCompletedMellinCoordinate) (h:ℝ) (bounded:h≤Real.log 2) :
 nativeRead c h (star c.value)=completeJointModel c h (star c.value) := by
 have original:nativeRead c h (star c.value)=inner ℂ (movedTest c h) (wholeModel (star c.value))+
   inner ℂ (fourierTest c h) (CountingDual.value c):=by
  rw [movedTest,fourierTest,inner_sub_left,inner_sub_left,inner_smul_left,inner_smul_left,
   Complex.conj_ofReal]
  unfold nativeRead
  ring
 rw [original,actual_free_joint_read c c h bounded]

theorem actual_original_fixed_joint (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
 BurnolPaBoundaryCancellationAt c zero↔
  (pairedMellinTranslationCharacter c.value (Real.log stageZeroSonineQ)-
   pairedMellinTranslationCharacter (star c.value) (Real.log stageZeroSonineQ))*kernelSelfSource c+
    (1/2:ℂ)*completeJointModel c (Real.log stageZeroSonineQ) (star c.value)=0 := by
 have bound:Real.log stageZeroSonineQ≤Real.log 2:=by
  apply Real.log_le_log
  · change 0<Real.sqrt 3
    positivity
  · change Real.sqrt 3≤2
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
 rw [actual_original_fixed_model c zero]
 unfold completeModelNet
 rw [actual_native_joint_read c _ bound]

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
