import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Model
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Consumer
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKElementaryArithmeticAction
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz OriginalKElementaryArithmeticAction.FreeParameter.Family OriginalKElementaryArithmeticAction.FreeParameter.FixedConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Model
open scoped InnerProductSpace Topology
local notation "Hq" => BurnolQuarterIntervalL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "T" => burnolTateReciprocalL2
open private forward_fourier from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource

private theorem actual_counted_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
 KCountingGram.value c=unitResolventSource c ConstantForward.value-fourierL2 (CountingDual.value c)+ReturnCounting.forwardValue c := by
 have total:=((WholeGramSource.elementary_forward_tendsto c).sub
  ((fourierL2.continuous.tendsto _).comp (CountingDual.original_dual_tendsto c))).add (ReturnCounting.forward_tendsto c)
 have actual:Tendsto (fun N:ℕ=>FiniteForcing.source N (sourceKernel c)) atTop
   (𝓝 (unitResolventSource c ConstantForward.value-fourierL2 (CountingDual.value c)+ReturnCounting.forwardValue c)):=by
  apply total.congr'
  filter_upwards with N
  change _=CountingDual.sourceCLM N (sourceKernel c)
  rw [sourceKernel,map_sub,map_add]
  simp only [CountingDual.sourceCLM_apply,forward_fourier]
  change FiniteForcing.source N (elementarySource c)-fourierL2 (DualSource.source N
   (burnolQuarterZeroExtension (sourceB c:Hq)))+FiniteForcing.source N (burnolQuarterZeroExtension (sourceSB c:Hq))=
    FiniteForcing.source N (elementarySource c)+FiniteForcing.source N (burnolQuarterZeroExtension (sourceSB c:Hq))-
     fourierL2 (DualSource.source N (burnolQuarterZeroExtension (sourceB c:Hq)))
  module
 rw [sourceKernel_original] at actual
 exact tendsto_nhds_unique (KCountingGram.forward_tendsto c zero) actual

def fourierTest (c:BurnolCompletedMellinCoordinate) (h:ℝ) : BurnolL2 :=
 burnolMultiplicativeDilation h (fourierL2 (K c:BurnolL2))-(Real.exp (h/2):ℂ)•fourierL2 (K c:BurnolL2)

/-- The two true return contacts share this literal source test, with opposite time directions kept. -/
def jointReturnTest (c:BurnolCompletedMellinCoordinate) (h:ℝ) : BurnolL2 :=
 T (fourierTest c h)-movedTest c h

private theorem actual_fourier_contact (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) :
 fourierContacts c h=inner ℂ (T (fourierTest c h)) (returnModel (star c.value))+
  inner ℂ (fourierL2 (fourierTest c h)) (freeUnit (star c.value) ConstantForward.value)-
   inner ℂ (fourierL2 (fourierTest c h)) (KCountingGram.value c) := by
 have source:fourierL2 (CountingDual.value c)=ReturnCounting.forwardValue c+
    unitResolventSource c ConstantForward.value-KCountingGram.value c:=by
  have original:=actual_counted_source c zero
  rw [original]
  module
 have contact:fourierContacts c h=inner ℂ (fourierTest c h) (CountingDual.value c):=by
  rw [fourierTest,inner_sub_left,inner_smul_left,Complex.conj_ofReal]
  rfl
 rw [contact,←fourierL2.inner_map_map (fourierTest c h) (CountingDual.value c),source,
  actual_return_forward_fourier,actual_original_return_model,actual_free_unit,
  inner_sub_right,inner_add_right,fourierL2.inner_map_map,←OriginalRieszFiniteSynthesis.tate_pairing]

/-- The original four-slot read consumes both full return directions and the original counted K. -/
theorem actual_native_joint_return (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) :
 nativeRead c h (star c.value)=
  -inner ℂ (movedTest c h) (freeUnit (star c.value) ConstantDual.value)+
   inner ℂ (jointReturnTest c h) (returnModel (star c.value))+
    inner ℂ (fourierL2 (fourierTest c h)) (freeUnit (star c.value) ConstantForward.value)-
     inner ℂ (fourierL2 (fourierTest c h)) (KCountingGram.value c) := by
 have first:inner ℂ (movedTest c h) (wholeModel (star c.value))=
  -inner ℂ (movedTest c h) (freeUnit (star c.value) ConstantDual.value)-
   inner ℂ (movedTest c h) (returnModel (star c.value)):=by
  rw [wholeModel,inner_sub_right,inner_neg_right]
  rfl
 have native:nativeRead c h (star c.value)=
  inner ℂ (movedTest c h) (wholeModel (star c.value))+fourierContacts c h:=by
  rw [movedTest,inner_sub_left,inner_smul_left,Complex.conj_ofReal]
  unfold nativeRead fourierContacts
  ring
 rw [native,first,actual_fourier_contact c zero h,jointReturnTest,inner_sub_left]
 ring

/-- Exact-m reading uses the same actual joint test; its two time directions are never identified. -/
theorem actual_joint_return_jet (c parameter:BurnolCompletedMellinCoordinate) (h:ℝ) (j:ℕ) :
 iteratedDeriv j (fun s:ℂ=>inner ℂ (jointReturnTest c h) (returnModel s)) parameter.value=
  inner ℂ (jointReturnTest c h)
   (OriginalKElementaryArithmeticAction.FreeParameter.CountReturn.countReader (iteratedDeriv j
    (fun s:ℂ=>(bModel s:Hq)) parameter.value)) :=
 actual_return_pair_jet parameter (jointReturnTest c h) j

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Consumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
