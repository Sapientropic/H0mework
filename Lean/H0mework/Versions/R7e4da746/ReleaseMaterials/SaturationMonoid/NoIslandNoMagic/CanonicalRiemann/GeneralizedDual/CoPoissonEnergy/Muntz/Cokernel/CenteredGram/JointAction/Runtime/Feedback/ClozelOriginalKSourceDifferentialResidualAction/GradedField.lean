import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialResidualAction.Inventory
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory (collapseValue)
end CF
namespace OriginalR
export OriginalKFullSourceRAction (variableAction originalField)
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
end OriginalR
variable {W : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance gradedGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade

/-- This map is the existing graded source value collapse, retaining actual roles before any observer. -/
def sourceCollapseHom : (grade : Nat)→PairValue (L.Value W grade) ()→+PairValue W ()
 | 0=>AddMonoidHom.id _
 | grade+1=>(sourceCollapseHom grade).comp ((AddMonoidHom.fst _ _)+(AddMonoidHom.snd _ _))

theorem source_collapse_actual (grade : Nat) (value : PairValue (L.Value W grade) ()) :
 sourceCollapseHom grade value=CF.collapseValue grade value := by
 induction grade with
 | zero=>rfl
 | succ grade prior=>exact prior (value.1+value.2)


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
