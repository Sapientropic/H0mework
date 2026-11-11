import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialAction.MaterialEffect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export SourceFamilyActualCurrentMaterialEnvironmentUpdate.SF (Factory Seed cfg)
end SF
namespace L
export SourceFamilyActualCurrentMaterialEnvironmentUpdate.L (Value groups)
end L
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader)
end R
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance factoryGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
variable (mother : SF.Factory W X ())

def sourceDifferentialRaw (grade : Nat)
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=L.Value W grade) (Var:=X) (sort:=()))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : I.Occurrence frame (current:=current)) :
 O.Raw (Value:=PairValue (L.Value W grade)) (Var:=X) (sort:=()) :=
 ⟨sourceMaterialEnvironment frame supplied,sourceMaterialCode frame supplied⟩

/-- The source material projection supplies the actual reader for each supplied occurrence before native admission. -/
def sourceDifferentialFactory : SF.Factory W X () :=
 {mother with datum:=fun grade seed frame=>
  {mother.datum grade seed frame with calculationReader:=some (fun {_current} supplied=>sourceDifferentialRaw grade frame supplied)}}

/-- The original decoder and both inventory callbacks are retained; the current source action alone changes. -/
theorem source_differential_callbacks (grade : Nat) (seed : SF.Seed W X () grade)
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=L.Value W grade) (Var:=X) (sort:=())) :
 (sourceDifferentialFactory mother).nextInventory=mother.nextInventory ∧
 (sourceDifferentialFactory mother).nextPairInventory=mother.nextPairInventory ∧
 (sourceDifferentialFactory mother).extraScalar=mother.extraScalar ∧
 (sourceDifferentialFactory mother).extraPair=mother.extraPair ∧
 ((sourceDifferentialFactory mother).datum grade seed frame).nextEnvironmentReadAt=
 (mother.datum grade seed frame).nextEnvironmentReadAt := ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Source code and environment are read from the same original occurrence and material projection. -/
theorem source_differential_actual_reader (grade : Nat) (seed : SF.Seed W X () grade)
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=L.Value W grade) (Var:=X) (sort:=()))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : I.Occurrence frame (current:=current)) :
 R.actionReader frame (SF.cfg (sourceDifferentialFactory mother) grade seed) supplied=
 sourceDifferentialRaw grade (A.epoch frame) supplied := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
