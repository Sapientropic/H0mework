import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.CofinalQuery.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.PostDecoderRead

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.WrittenCofinal
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open SourceGeneratedScalarDifferentialResidual
namespace B
export ActualNativeBornSourceEffect (born)
end B
namespace RM
export ActualCofinalResidualModelSplice (packetWordTransport)
end RM
namespace NT
export ActualCofinalNativeTower
 (updatedEnvironment updated_environment oldEnvironment actualIncrement nativeInventory component)
end NT
namespace PD
export ActualCofinalCommonAction.PostDecoder (updated_environment_current next_action_read)
end PD
attribute [local irreducible] AS.localNativeReceipt

section SourceProjections
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance projectionGroups (grade : Nat) : ∀ target,AddCommGroup (F.Value W grade target) := F.groups W grade

private theorem source_model_updated
 (factory : F.Factory W X ()) (initial : F.Frame (Value:=W) (Var:=X) (sort:=()))
 (cfg : F.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=())) (language : cfg.LowVar=X)
 (ordinal : Nat) (word : F.Words factory initial cfg language ordinal) :
 additionReadout (R:=ℤ)
  (CA.modelRead factory initial cfg language []
   (CA.modelAction factory initial cfg language
    (CA.projection factory initial cfg language (DFinsupp.single ordinal word))) (ordinal+1))=
 evaluation (R:=ℤ) (CA.site factory initial cfg language (ordinal+1)).2.1.1.activeEnvironment
  (CA.siteAction factory initial cfg language ordinal word) := by
 rw [source_model_future]
 change additionReadout (R:=ℤ)
  (NT.nativeInventory factory initial cfg language (ordinal+1)
   (NT.component factory initial cfg language (ordinal+1)
    (DFinsupp.single (ordinal+1) (CA.siteAction factory initial cfg language ordinal word))))= _
 simp only [NT.component,DFinsupp.lapply_apply,DFinsupp.single_eq_same]
 exact (LinearMap.congr_fun (evaluation_update
  (NT.oldEnvironment factory initial cfg language (ordinal+1))
  (NT.actualIncrement factory initial cfg language (ordinal+1)))
  (CA.siteAction factory initial cfg language ordinal word)).symm.trans
   (congrArg (fun environment=>evaluation (R:=ℤ) environment
     (CA.siteAction factory initial cfg language ordinal word))
    ((NT.updated_environment factory initial cfg language (ordinal+1)).symm.trans
     (PD.updated_environment_current factory initial cfg language (ordinal+1))))

private theorem packet_decoded_read
 {first second : AS.AdmissionPacket (W:=W) (X:=X) (s:=())} (same : first=second)
 (word : Formal ℤ (F.Value W first.1) X ()) :
 HEq (evaluation (R:=ℤ) first.2.1.1.activeEnvironment word)
  (evaluation (R:=ℤ) second.2.1.1.activeEnvironment (RM.packetWordTransport same word)) := by
 cases same
 rfl

private theorem selected_born
 (frame : F.Frame (Value:=W) (Var:=X) (sort:=()))
 (cfg : F.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=())) :
 S.next (S.Complete.atReceipt cfg frame 0) cfg=
 S.nextBorn (S.Complete.atReceipt cfg frame 0) cfg := by
 unfold S.next
 rw [(S.Complete.receipt cfg frame 0).2.2.2]
end SourceProjections
local instance consumerGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- Every future native observer reads the entire actual transported query boundary after its real source action. -/
theorem actual_boundary_future (history : List PUnit.{1}) (target : Nat) :
 type_of% (source_model_future (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
  (queryBoundary observation nontrivial half depth ordinal) history target) :=
 source_model_future _ _ _ _ _ _ _ _

/-- The full future-invariant inverse fibre retains all actual histories and sites. -/
theorem actual_boundary_future_fibre
 (candidate : F.CommonWords (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl) :
 type_of% (source_model_fibre (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
  (queryBoundary observation nontrivial half depth ordinal) candidate) :=
 source_model_fibre _ _ _ _ _ _ _

theorem actual_boundary_receiver : type_of% (source_receiver_inventory (D.factory observation nontrivial half)
 (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
 (queryBoundary observation nontrivial half depth ordinal)) := source_receiver_inventory _ _ _ _ _ _

/-- This local inverse retains both old value and actual source effect before any addition readout. -/
theorem actual_boundary_inverse_fibre
 (candidate : F.Words (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)) :
 type_of% (source_inventory_fibre (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
  (queryBoundary observation nontrivial half depth ordinal) candidate) := source_inventory_fibre _ _ _ _ _ _ _

theorem actual_boundary_cochain : type_of% (source_cochain_boundary (D.factory observation nontrivial half)
 (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
 (queryBoundary observation nontrivial half depth ordinal)) := source_cochain_boundary _ _ _ _ _ _

/-- The original native decoder's actual packet, recognized by the source genealogy. -/
theorem decoder_packet :
 CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+3)=
 AS.bornAfterNative (originalNative observation nontrivial half depth (ordinal+2)) :=
 original_next_packet observation nontrivial half depth (ordinal+2)

theorem decoder_born :
 B.born (writerSelected observation nontrivial half depth (ordinal+2))
  (originalNative observation nontrivial half depth (ordinal+2)).2.2.1=
 writerBorn observation nontrivial half depth (ordinal+2) :=
 (selected_born (originalNative observation nontrivial half depth (ordinal+2)).2.1.1
  (writerCfg observation nontrivial half depth (ordinal+2))).symm.trans
 (original_writer_next observation nontrivial half depth (ordinal+2))

abbrev decodedQueryWord := RM.packetWordTransport
 (decoder_packet observation nontrivial half depth ordinal)
 (CA.siteAction (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)
  (queryBoundary observation nontrivial half depth ordinal))
/-- The actual Model's updated observer reads this same literal post-decoder word. -/
theorem actual_boundary_model_decoder :
 HEq (additionReadout (R:=ℤ)
  (CA.modelRead (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
   (D.firstCfg observation nontrivial half depth) rfl []
   (CA.modelAction (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
    (D.firstCfg observation nontrivial half depth) rfl
    (CA.projection (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
     (D.firstCfg observation nontrivial half depth) rfl
     (DFinsupp.single (ordinal+2) (queryBoundary observation nontrivial half depth ordinal)))) (ordinal+3)))
  (evaluation (R:=ℤ) (writerBorn observation nontrivial half depth (ordinal+2)).activeEnvironment
   (decodedQueryWord observation nontrivial half depth ordinal)) :=
 (heq_of_eq (source_model_updated _ _ _ _ _ _)).trans
  (packet_decoded_read (decoder_packet observation nontrivial half depth ordinal) _)


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.WrittenCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
