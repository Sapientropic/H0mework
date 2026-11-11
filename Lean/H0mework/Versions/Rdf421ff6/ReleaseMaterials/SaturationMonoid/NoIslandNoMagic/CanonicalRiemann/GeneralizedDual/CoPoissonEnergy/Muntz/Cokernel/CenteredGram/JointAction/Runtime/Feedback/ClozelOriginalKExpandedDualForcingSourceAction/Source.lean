import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedInverseSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedDualForcingSourceAction
open Complex BurnolPhysicalState OriginalKExpandedInverseSourceAction
open scoped InnerProductSpace
local instance forcingComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "B" => burnolMeanZeroBlockInverse

/-- This is the actual adjoint of the original two signed forcing operators. -/
def sourceDualPlusForcing : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 (1-T).adjoint

def sourceDualMinusForcing : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 (1+T).adjoint

private theorem original_signed_right_inverse :
 sourcePlusAction*(1-T)=1 ∧ sourceMinusAction*(1+T)=1 := by
 have inverse : B * burnolMeanZeroOneMinusSquare=1 := Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
 have oneMinus : (1-T)*(1+T)=burnolMeanZeroOneMinusSquare := by
  change (1-T)*(1+T)=1-T*T
  simp only [mul_add,sub_mul,one_mul,mul_one]
  module
 have onePlus : (1+T)*(1-T)=burnolMeanZeroOneMinusSquare := by
  change (1+T)*(1-T)=1-T*T
  simp only [mul_sub,add_mul,one_mul,mul_one]
  module
 have inverseCommutes : T*B=B*T := by
  have commute : T*burnolMeanZeroOneMinusSquare=burnolMeanZeroOneMinusSquare*T := by
   change T*(1-T*T)=(1-T*T)*T
   simp only [mul_sub,sub_mul,mul_one,one_mul,mul_assoc]
  calc
   T*B = (B*burnolMeanZeroOneMinusSquare)*(T*B) := by rw [inverse,one_mul]
   _ = B*(T*burnolMeanZeroOneMinusSquare)*B := by rw [commute]; simp only [mul_assoc]
   _ = B*T := by rw [mul_assoc B, mul_assoc T, burnolMeanZeroBlockInverse_right, mul_one]

 constructor
 · unfold sourcePlusAction
   calc
    ((1+T)*B)*(1-T)=B*((1+T)*(1-T)) := by
     have commutesPlus : (1+T)*B=B*(1+T) := by
      simp only [add_mul,mul_add,one_mul,mul_one,inverseCommutes]
     rw [commutesPlus,mul_assoc]
    _ = 1 := by rw [onePlus,inverse]
 · unfold sourceMinusAction
   calc
    ((1-T)*B)*(1+T)=B*((1-T)*(1+T)) := by
     have commutesMinus : (1-T)*B=B*(1-T) := by
      simp only [sub_mul,mul_sub,one_mul,mul_one,inverseCommutes]
     rw [commutesMinus,mul_assoc]
    _ = 1 := by rw [oneMinus,inverse]

/-- The source adjoint inverse generates its actual forcing before a quarter or eta read. -/
theorem source_dual_signed_forcing (source : BurnolQuarterMeanZeroCarrier) :
 sourceDualPlusForcing (sourcePlusAction.adjoint source)=source ∧
 sourceDualMinusForcing (sourceMinusAction.adjoint source)=source := by
 have plus := congrArg (fun op : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier => op.adjoint) original_signed_right_inverse.1
 have minus := congrArg (fun op : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier => op.adjoint) original_signed_right_inverse.2
 constructor
 · change ((1-T).adjoint.comp sourcePlusAction.adjoint) source=source
   have actual : (1-T).adjoint.comp sourcePlusAction.adjoint=1 := by
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_one] using plus
   rw [actual]; rfl
 · change ((1+T).adjoint.comp sourceMinusAction.adjoint) source=source
   have actual : (1+T).adjoint.comp sourceMinusAction.adjoint=1 := by
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_one] using minus
   rw [actual]; rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedDualForcingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
