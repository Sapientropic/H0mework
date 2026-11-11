import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Read
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Model
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.CountReturn OriginalKElementaryArithmeticAction.FreeParameter.Riesz OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Read
open scoped InnerProductSpace Topology
local notation "Hq" => BurnolQuarterIntervalL2
local notation "T" => burnolTateReciprocalL2

theorem actual_return_even (c:BurnolCompletedMellinCoordinate) :
 reflectL2 (ReturnCounting.value c)=ReturnCounting.value c :=
 burnolReflectL2_eq_of_even_raw _ _ (ReturnCounting.value_coeFn c) (fun x=>by
  simp only [ReturnCounting.eventRaw,DualSourceRaw.channels,abs_neg])

/-- Both directions belong to the same original return programme, with the actual Tate ordering. -/
theorem actual_return_forward_fourier (c:BurnolCompletedMellinCoordinate) :
 ReturnCounting.forwardValue c=fourierL2 (T (ReturnCounting.value c)) := by
 have actual:=congrArg T (actual_return_tate_fourier c)
 rw [burnolTateReciprocalL2_involutive] at actual
 apply fourierL2.injective
 rw [fourierL2_fourierL2,←burnolTateReciprocal_reflect,actual_return_even]
 exact actual.symm

def forwardReader : Hq→L[ℂ]BurnolL2 :=
 fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp (burnolTateReciprocalL2.comp countReader)

def returnModel (s:ℂ) : BurnolL2 := countReader (bModel s:Hq)
def forwardModel (s:ℂ) : BurnolL2 := forwardReader (bModel s:Hq)

theorem actual_original_return_model (c:BurnolCompletedMellinCoordinate) :
 ReturnCounting.value c=returnModel (star c.value) := by
 rw [returnModel,←actual_original_B_model]
 exact (actual_original_return_count c).symm

theorem actual_original_forward_model (c:BurnolCompletedMellinCoordinate) :
 ReturnCounting.forwardValue c=forwardModel (star c.value) := by
 rw [actual_return_forward_fourier,actual_original_return_model]
 rfl

/-- The complete forward return has a free analytic source model; no neighboring zero law is used. -/
theorem forward_model_analytic (c:BurnolCompletedMellinCoordinate) :
 AnalyticAt ℂ forwardModel c.value := by
 have b:AnalyticAt ℂ (fun s:ℂ=>(bModel s:Hq)) c.value:=
  (burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL.analyticAt _).comp (original_B_model_analytic c)
 exact (forwardReader.analyticAt _).comp b

theorem return_model_analytic (c:BurnolCompletedMellinCoordinate) :
 AnalyticAt ℂ returnModel c.value := by
 have b:AnalyticAt ℂ (fun s:ℂ=>(bModel s:Hq)) c.value:=
  (burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL.analyticAt _).comp (original_B_model_analytic c)
 exact (countReader.analyticAt _).comp b

/-- The original complete return mean remains its actual logarithmic source price. -/
theorem actual_original_return_mean (c:BurnolCompletedMellinCoordinate) :
 burnolQuarterMeanCoefficient (burnolQuarterRestriction (returnModel (star c.value)))=
  2*inner ℂ SmallScaleLog.logL2 (Constructor.returnState c:Hq) := by
 rw [←actual_original_return_model]
 exact ReturnCounting.value_mean c

private theorem reader_jet (reader:Hq→L[ℂ]BurnolL2) {family:ℂ→Hq} {s:ℂ}
 (native:AnalyticAt ℂ family s) (j:ℕ) :
 iteratedDeriv j (fun z=>reader (family z)) s=reader (iteratedDeriv j family s) := by
 change (iteratedFDeriv ℂ j (reader ∘ family) s) (fun _=>1)=_
 rw [reader.iteratedFDeriv_comp_left (native.contDiffAt (n:=j)) le_rfl]
 rfl

/-- The original arithmetic count commutes with every legitimate parameter read of its actual B source. -/
theorem actual_return_jet (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
 iteratedDeriv j returnModel c.value=
  countReader (iteratedDeriv j (fun s:ℂ=>(bModel s:Hq)) c.value) := by
 have b:AnalyticAt ℂ (fun s:ℂ=>(bModel s:Hq)) c.value:=
  (burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL.analyticAt _).comp (original_B_model_analytic c)
 exact reader_jet countReader b j

/-- The same complete source also generates the forward read, with its Tate/Fourier ordering. -/
theorem actual_forward_jet (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
 iteratedDeriv j forwardModel c.value=
  forwardReader (iteratedDeriv j (fun s:ℂ=>(bModel s:Hq)) c.value) := by
 have b:AnalyticAt ℂ (fun s:ℂ=>(bModel s:Hq)) c.value:=
  (burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL.analyticAt _).comp (original_B_model_analytic c)
 exact reader_jet forwardReader b j

/-- The actual moved cotest may read the exact-m return jet without changing the source occurrence. -/
theorem actual_return_pair_jet (c:BurnolCompletedMellinCoordinate) (test:BurnolL2) (j:ℕ) :
 iteratedDeriv j (fun s:ℂ=>inner ℂ test (returnModel s)) c.value=
  inner ℂ test (countReader (iteratedDeriv j (fun s:ℂ=>(bModel s:Hq)) c.value)) := by
 have read:iteratedDeriv j (fun s:ℂ=>inner ℂ test (returnModel s)) c.value=
   inner ℂ test (iteratedDeriv j returnModel c.value):=by
  change (iteratedFDeriv ℂ j ((innerSL ℂ test) ∘ returnModel) c.value) (fun _=>1)=_
  rw [(innerSL ℂ test).iteratedFDeriv_comp_left ((return_model_analytic c).contDiffAt (n:=j)) le_rfl]
  rfl
 rw [read,actual_return_jet]

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Model
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
