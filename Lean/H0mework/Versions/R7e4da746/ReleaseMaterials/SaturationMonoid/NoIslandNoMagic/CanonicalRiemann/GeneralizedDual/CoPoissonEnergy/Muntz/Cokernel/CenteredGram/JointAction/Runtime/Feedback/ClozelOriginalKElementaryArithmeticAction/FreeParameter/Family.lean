import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.CountReturn
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.Family
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.Position OriginalKElementaryArithmeticAction.FreeParameter.CountReturn OriginalKElementaryArithmeticAction.FreeParameter.Riesz
open scoped InnerProductSpace Topology
local notation "Hq" => BurnolQuarterIntervalL2

def wholeModel (s:ℂ) : BurnolL2 :=
 -freeUnit s ConstantDual.value-countReader (bModel s:Hq)

/-- The original full position source, including its noncompact zeta tail, is this free family. -/
theorem actual_original_whole_model (c:BurnolCompletedMellinCoordinate) :
 wholeValue c=wholeModel (star c.value) := by
 rw [actual_whole_inverse_reader,actual_free_unit,actual_original_B_model]
 rfl

/-- Analyticity is produced by the original resolvent and two fixed source operators. -/
theorem whole_model_analytic (c:BurnolCompletedMellinCoordinate) :
 AnalyticAt ℂ wholeModel c.value := by
 have b:AnalyticAt ℂ (fun s:ℂ=>(bModel s:Hq)) c.value:=
  (burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL.analyticAt _).comp (original_B_model_analytic c)
 exact (free_unit_analytic c ConstantDual.value).neg.sub ((countReader.analyticAt _).comp b)

/-- The zero observation recognizes the original PC column; it is not differentiated in a neighborhood. -/
theorem actual_original_position_model (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
 PositionCounting.value c zero=wholeModel (star c.value) := by
 rw [←actual_original_whole_model,actual_original_zero_value]

/-- The very same joint source consumes the model with the original endpoint coefficients. -/
theorem actual_original_joint_model (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
 JointCounting.value c zero=
  Kernel.beta c • wholeModel (star c.value)+Kernel.A c • CountingDual.value c := by
 rw [←actual_original_zero_joint, jointValue,actual_original_whole_model]

end OriginalKElementaryArithmeticAction.FreeParameter.Family
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
