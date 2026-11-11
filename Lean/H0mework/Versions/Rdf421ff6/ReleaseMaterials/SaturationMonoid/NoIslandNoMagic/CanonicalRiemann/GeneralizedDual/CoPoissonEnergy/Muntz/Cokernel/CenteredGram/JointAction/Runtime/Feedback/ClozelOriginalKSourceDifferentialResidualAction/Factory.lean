import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialResidualAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
 (effectFaces paidCoordinate actual_effect actual_inverse differential_effect relation_recovery sourceOccurrence whole_paid_trace)
end F
namespace Native
export ActualCofinalSourceAction (nativePacket nativeValue selected receipt sourceBorn born_environment)
end Native
namespace Prior
export OriginalKSourceDifferentialAction (sourceDifferentialPacket source_differential_native_two_fees)
end Prior
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance factoryGroups (grade : Nat) : ∀ target,AddCommGroup (OriginalKSourceDifferentialAction.L.Value W grade target) :=
 OriginalKSourceDifferentialAction.L.groups W grade
namespace SF
export OriginalKSourceDifferentialAction.SF (Factory Seed cfg)
end SF
namespace L
export OriginalKSourceDifferentialAction.L (Value groups)
end L
namespace A
export OriginalKSourceDifferentialAction.A (epoch)
end A
namespace S
export OriginalKSourceDifferentialAction.S (actualOccurrence)
end S
namespace R
export OriginalKSourceDifferentialAction.R (actionReader actualMaterial)
end R
namespace AS
export OriginalKSourceDifferentialAction.AS (AdmissionPacket)
end AS

variable (mother : SF.Factory W X ())
def sourceResidualReader (grade : Nat)
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=L.Value W grade) (Var:=X) (sort:=()))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : D.I.Occurrence frame (current:=current)) : D.O.Raw (Value:=PairValue (L.Value W grade)) (Var:=X) (sort:=()) :=
 ⟨sourceResidualEnvironment frame supplied,sourceResidualCode frame supplied⟩

/-- The actual supplied paid-state relation is installed before native admission; no residual value is an input. -/
def sourceResidualFactory : SF.Factory W X () :=
 {mother with datum:=fun grade seed frame=>
  {mother.datum grade seed frame with calculationReader:=some (fun {_current} supplied=>sourceResidualReader grade frame supplied)}}

variable (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))
/-- The original full packet supplies its frame and source seed to the new source action installation. -/
def sourceResidualPacket : AS.AdmissionPacket (W:=W) (X:=X) (s:=()) :=
 ⟨packet.1,packet.2.1,SF.cfg (sourceResidualFactory mother) packet.1 packet.2.1.2,⟨rfl⟩⟩

def sourceResidualNativeMaterial := R.actualMaterial packet.2.1.1
 (SF.cfg (sourceResidualFactory mother) packet.1 packet.2.1.2)

theorem source_residual_reader_actual :
 (sourceResidualNativeMaterial mother packet).raw=sourceResidualCode (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1) ∧
 (sourceResidualNativeMaterial mother packet).environment=sourceResidualEnvironment (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1) := ⟨rfl,rfl⟩

/-- The generated native action retains the original source relation boundary and both its environment and syntax fees. -/
theorem source_residual_material_coordinate :
 ((sourceResidualNativeMaterial mother packet).raw.eval (sourceResidualNativeMaterial mother packet).environment).1+
 ((sourceResidualNativeMaterial mother packet).raw.eval (sourceResidualNativeMaterial mother packet).environment).2=
 (F.effectFaces (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))).embedding
  (F.paidCoordinate (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))) := by
 have faces:=source_residual_literal_faces (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)
 have sum:=congrArg (fun value : PairValue (L.Value W packet.1) ()=>value.1+value.2) faces
 have coordinate:=F.actual_effect (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))
 exact sum.trans ((add_sub_cancel _ _).trans
  ((source_residual_generated_effect (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).trans coordinate.symm))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
