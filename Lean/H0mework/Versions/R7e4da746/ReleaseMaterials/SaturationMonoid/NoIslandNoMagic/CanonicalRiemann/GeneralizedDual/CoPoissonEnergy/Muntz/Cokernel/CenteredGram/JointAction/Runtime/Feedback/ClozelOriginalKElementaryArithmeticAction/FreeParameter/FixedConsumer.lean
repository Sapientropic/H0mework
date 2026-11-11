import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.Family
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.FixedBill
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.FixedConsumer
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource.ResponseForcing.Source OriginalKPairedBEulerJunctionSource.ResponseForcing.Consumer OriginalKElementaryArithmeticAction.FreeParameter.FixedBill
open OriginalKElementaryArithmeticAction.FreeParameter.Family
open scoped InnerProductSpace Topology
local notation "K" => burnolCompletedMellinRieszVector

/-- All four original shifted prices are retained; the free parameter reads the actual PC source. -/
def nativeRead (c:BurnolCompletedMellinCoordinate) (h:ℝ) (s:ℂ) : ℂ :=
 inner ℂ (burnolMultiplicativeDilation h (K c:BurnolL2)) (wholeModel s)-
  (Real.exp (h/2):ℂ)*inner ℂ (K c:BurnolL2) (wholeModel s)+
 inner ℂ (burnolMultiplicativeDilation h (fourierL2 (K c:BurnolL2))) (CountingDual.value c)-
  (Real.exp (h/2):ℂ)*inner ℂ (fourierL2 (K c:BurnolL2)) (CountingDual.value c)

/-- The complete fixed price consumes the new same-field model, not a free target equality. -/
theorem actual_complete_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
 (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) :
 responseFinitePrice c h=star (nativeRead c h (star c.value)) := by
 rw [actual_fixed_bill c zero h nonnegative bounded,actual_original_position_model]
 unfold nativeRead
 simp only [star_add,star_sub,star_mul,star_def,conj_ofReal,inner_conj_symm]
 ring

/-- Only the freely varied original PC leg is differentiated here; the entire CD contact stays explicit. -/
theorem native_read_analytic (c parameter:BurnolCompletedMellinCoordinate) (h:ℝ) :
 AnalyticAt ℂ (nativeRead c h) parameter.value := by
 have moved:AnalyticAt ℂ (fun s=>inner ℂ (burnolMultiplicativeDilation h (K c:BurnolL2)) (wholeModel s)) parameter.value:=
  ((innerSL ℂ (burnolMultiplicativeDilation h (K c:BurnolL2))).analyticAt _).comp (whole_model_analytic parameter)
 have current:AnalyticAt ℂ (fun s=>inner ℂ (K c:BurnolL2) (wholeModel s)) parameter.value:=
  ((innerSL ℂ (K c:BurnolL2)).analyticAt _).comp (whole_model_analytic parameter)
 exact ((moved.sub (analyticAt_const.mul current)).add analyticAt_const).sub analyticAt_const

def completeModelNet (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
 (pairedMellinTranslationCharacter c.value h-pairedMellinTranslationCharacter (star c.value) h)*kernelSelfSource c+
  (1/2:ℂ)*nativeRead c h (star c.value)

/-- The original fixed RH consumer now contains this actual free source and both untouched Fourier contacts. -/
theorem actual_original_fixed_model (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
 BurnolPaBoundaryCancellationAt c zero↔completeModelNet c (Real.log stageZeroSonineQ)=0 := by
 have nonnegative:0≤Real.log stageZeroSonineQ:=by
  apply Real.log_nonneg
  change 1≤Real.sqrt 3
  exact Real.one_le_sqrt.mpr (by norm_num)
 have bounded:Real.log stageZeroSonineQ≤Real.log 2:=by
  apply Real.log_le_log
  · change 0<Real.sqrt 3
    positivity
  · change Real.sqrt 3≤2
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
 rw [actual_original_fixed_consumer c zero]
 unfold completeResponseNet completeModelNet
 rw [actual_complete_price c zero _ nonnegative bounded,star_star]

end OriginalKElementaryArithmeticAction.FreeParameter.FixedConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
