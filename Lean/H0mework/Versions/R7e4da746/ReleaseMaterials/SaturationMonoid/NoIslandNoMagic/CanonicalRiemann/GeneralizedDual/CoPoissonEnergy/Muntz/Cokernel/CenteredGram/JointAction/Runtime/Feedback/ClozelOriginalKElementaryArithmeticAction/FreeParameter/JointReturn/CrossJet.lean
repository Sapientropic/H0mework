import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossJet
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz OriginalKElementaryArithmeticAction.FreeParameter.Family OriginalKElementaryArithmeticAction.FreeParameter.FixedConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Model OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Consumer
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact
open scoped InnerProductSpace Topology
local notation "Hq" => BurnolQuarterIntervalL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

def jointBRead (c:BurnolCompletedMellinCoordinate) (h:ℝ) : Hq→L[ℂ]ℂ :=
 innerSL ℂ (burnolQuarterRestriction (fourierTest c h))-
  (innerSL ℂ (movedTest c h)).comp OriginalKElementaryArithmeticAction.FreeParameter.CountReturn.countReader

/-- Both true contacts now read the same original B occurrence. -/
theorem actual_complete_joint_source (c:BurnolCompletedMellinCoordinate) (h:ℝ) (s:ℂ) :
 completeJointModel c h s= -inner ℂ (movedTest c h) (freeUnit s ConstantDual.value)+jointBRead c h (bModel s:Hq) := by
 unfold completeJointModel wholeModel jointBRead
 simp only [sub_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
  inner_sub_right,inner_neg_right]
 ring

private theorem scalar_read_jet {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
 (reader:E→L[ℂ]ℂ) {family:ℂ→E} {s:ℂ} (native:AnalyticAt ℂ family s) (j:ℕ) :
 iteratedDeriv j (fun z=>reader (family z)) s=reader (iteratedDeriv j family s) := by
 change (iteratedFDeriv ℂ j (reader ∘ family) s) (fun _=>1)=_
 rw [reader.iteratedFDeriv_comp_left (native.contDiffAt (n:=j)) le_rfl]
 rfl

/-- Every parameter read includes the two simultaneous original contacts. -/
theorem actual_complete_joint_jet (c parameter:BurnolCompletedMellinCoordinate) (h:ℝ) (j:ℕ) :
 iteratedDeriv j (completeJointModel c h) parameter.value=
  -inner ℂ (movedTest c h) (iteratedDeriv j (fun s:ℂ=>freeUnit s ConstantDual.value) parameter.value)+
   jointBRead c h (iteratedDeriv j (fun s:ℂ=>(bModel s:Hq)) parameter.value) := by
 have unit:=free_unit_analytic parameter ConstantDual.value
 have b:AnalyticAt ℂ (fun s:ℂ=>(bModel s:Hq)) parameter.value:=
  (burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL.analyticAt _).comp (original_B_model_analytic parameter)
 have unitRead:AnalyticAt ℂ (fun s:ℂ=>inner ℂ (movedTest c h) (freeUnit s ConstantDual.value)) parameter.value:=
  ((innerSL ℂ (movedTest c h)).analyticAt _).comp unit
 have bRead:AnalyticAt ℂ (fun s:ℂ=>jointBRead c h (bModel s:Hq)) parameter.value:=
  ((jointBRead c h).analyticAt _).comp b
 have source:completeJointModel c h=(fun s:ℂ=>-inner ℂ (movedTest c h) (freeUnit s ConstantDual.value))+
   (fun s:ℂ=>jointBRead c h (bModel s:Hq)):=funext (actual_complete_joint_source c h)
 have negative:ContDiffAt ℂ j (fun s:ℂ=>-inner ℂ (movedTest c h) (freeUnit s ConstantDual.value)) parameter.value:=
  unitRead.neg.contDiffAt
 rw [source,iteratedDeriv_add negative (bRead.contDiffAt (n:=j)),iteratedDeriv_fun_neg]
 have first:=scalar_read_jet (innerSL ℂ (movedTest c h)) unit j
 simp only [innerSL_apply_apply] at first
 rw [first,scalar_read_jet _ b]

/-- The multiplicity is the original theta--Mellin owner's order, and the conjugate read has that same order. -/
theorem actual_original_Xi_joint_jet (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
 let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner c.value
 generatedRiemannXiZeroOrder ActualAnalyticOwner (star c.value)=m ∧
  iteratedDeriv m (completeJointModel c h) (star c.value)=
   -inner ℂ (movedTest c h) (iteratedDeriv m (fun s:ℂ=>freeUnit s ConstantDual.value) (star c.value))+
    jointBRead c h (iteratedDeriv m (fun s:ℂ=>(bModel s:Hq)) (star c.value)) := by
 dsimp only
 constructor
 · exact NoIslandNoMagic.CanonicalRiemann.OriginalUnitXiConjugateOrderSource.actual_original_Xi_order_conjugate c
 · exact actual_complete_joint_jet c (barC c) h _

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
