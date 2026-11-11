import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedCompleteWindowSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedInverseSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource
local instance sourceComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "B" => burnolMeanZeroBlockInverse
local notation "q" => (1/4:ℝ)

def sourcePlusAction : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier := (1+T)*B

def sourceMinusAction : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier := (1-T)*B

/-- The same endpoint inverse generates both coupled fields before dilation or cotest. -/
theorem source_coupled_fields :
 sourcePlusAction Response.eta = Response.u+Response.v ∧
 sourceMinusAction Response.eta = Response.u-Response.v := by
 constructor <;> rfl

theorem source_coupled_equations (source : BurnolQuarterMeanZeroCarrier) :
 (1-T) (sourcePlusAction source)=source ∧
 (1+T) (sourceMinusAction source)=source := by
 have plus : (1-T)*(1+T)=burnolMeanZeroOneMinusSquare := by
  change (1-T)*(1+T)=1-T*T
  simp only [mul_add,sub_mul,one_mul,mul_one]
  module
 have minus : (1+T)*(1-T)=burnolMeanZeroOneMinusSquare := by
  change (1+T)*(1-T)=1-T*T
  simp only [mul_sub,add_mul,one_mul,mul_one]
  module
 constructor
 · change (((1-T)*(1+T))*B) source=source
   rw [plus,burnolMeanZeroBlockInverse_right]
   rfl
 · change (((1+T)*(1-T))*B) source=source
   rw [minus,burnolMeanZeroBlockInverse_right]
   rfl

def sourceExpandedAction (t : ℝ) :
 BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolRadiusIntervalL2 (q*Real.exp t) :=
 (burnolRadiusRestriction (q*Real.exp t)).comp
  ((burnolMultiplicativeDilation (-t)).toLinearIsometry.toContinuousLinearMap.comp
   (burnolQuarterZeroExtension.comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule)))

def sourceExpandedPlus (t : ℝ) := (sourceExpandedAction t).comp sourcePlusAction

def sourceExpandedMinus (t : ℝ) := (sourceExpandedAction t).comp sourceMinusAction

/-- These are actual source actions on the original endpoint, with the entire radius inventory retained. -/
theorem source_expanded_fields (t : ℝ) :
 sourceExpandedPlus t Response.eta =
  OriginalKExpandedCompleteWindowSourceAction.actualExpandedQuarterWeight
   OriginalKExpandedCompleteWindowSourceAction.actualCoupledQuarterPlus t ∧
 sourceExpandedMinus t Response.eta =
  OriginalKExpandedCompleteWindowSourceAction.actualExpandedQuarterWeight
   OriginalKExpandedCompleteWindowSourceAction.actualCoupledQuarterMinus t := by
 constructor
 · change burnolRadiusRestriction (q*Real.exp t)
     (burnolMultiplicativeDilation (-t) (burnolQuarterZeroExtension
       ((sourcePlusAction Response.eta) : BurnolQuarterIntervalL2))) = _
   rw [source_coupled_fields.1]
   rfl
 · change burnolRadiusRestriction (q*Real.exp t)
     (burnolMultiplicativeDilation (-t) (burnolQuarterZeroExtension
       ((sourceMinusAction Response.eta) : BurnolQuarterIntervalL2))) = _
   rw [source_coupled_fields.2]
   rfl

/-- The source inverse is consumed through its real adjoint, not an alignment witness. -/
theorem source_expanded_dual_action (value : BurnolL2) (t : ℝ) :
 inner ℂ (burnolRadiusRestriction (q*Real.exp t) value)
  (sourceExpandedPlus t Response.eta) =
  inner ℂ ((sourceExpandedPlus t).adjoint (burnolRadiusRestriction (q*Real.exp t) value)) Response.eta ∧
 inner ℂ (burnolRadiusRestriction (q*Real.exp t) value)
  (sourceExpandedMinus t Response.eta) =
  inner ℂ ((sourceExpandedMinus t).adjoint (burnolRadiusRestriction (q*Real.exp t) value)) Response.eta := by
 constructor
 · exact (ContinuousLinearMap.adjoint_inner_left (sourceExpandedPlus t) _ _).symm
 · exact (ContinuousLinearMap.adjoint_inner_left (sourceExpandedMinus t) _ _).symm
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedInverseSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
