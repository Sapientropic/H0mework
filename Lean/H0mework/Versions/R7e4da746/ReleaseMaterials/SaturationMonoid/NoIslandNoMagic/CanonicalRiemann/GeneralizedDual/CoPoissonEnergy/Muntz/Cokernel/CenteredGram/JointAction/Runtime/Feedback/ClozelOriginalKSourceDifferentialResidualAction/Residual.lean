import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialResidualAction.WholePrice
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
 (actualRelation complex boundary wholeFaces generated_relation generated_cochain generated_differential completion_zero whole_recovery native_zero_iff)
end F
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local instance residualCanonicalBaseGroups (initial : Nat) : ∀ target,AddCommGroup (L.Value (PairValue OriginalR.C.Value) initial target) :=
 L.groups (PairValue OriginalR.C.Value) initial
local instance residualCanonicalOriginGroups (initial origin : Nat) : ∀ target,AddCommGroup
 (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin target) :=
 L.groups (L.Value (PairValue OriginalR.C.Value) initial) origin
local instance residualCanonicalRuntimeGroups (initial origin grade : Nat) : ∀ target,AddCommGroup
 (L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) grade target) :=
 L.groups (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) grade
variable (initial origin : Nat)
variable (mother : SF.Factory (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) OriginalR.C.Var ())
variable (packet : AS.AdmissionPacket (W:=L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) (X:=OriginalR.C.Var) (s:=()))

/-- This coordinate is read after the actual paid-state relation effect was generated. -/
def completeResidualSourceCoordinate :=
 (F.effectFaces (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))).embedding
 (F.paidCoordinate (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)))

/-- The received relation action recovers the canonical residual before the original R reads its field. -/
theorem complete_residual_total_coordinate :
 completeResidualTotalRole initial origin packet.1
  ((sourceResidualCode (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).eval
   (sourceResidualEnvironment (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)))=
 (completeResidualSourceCoordinate initial origin packet,0) := by
 apply Prod.ext
 · have roles:=source_residual_literal_faces (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)
   have sum:=congrArg (fun value : PairValue (L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) packet.1) ()=>value.1+value.2) roles
   exact sum.trans ((add_sub_cancel _ _).trans
    ((source_residual_generated_effect (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).trans
     (F.actual_effect (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))).symm))
 · rfl

/-- The original R quartet is a restriction of this same paid relation residual, through the real init/source-born/runtime grades. -/
theorem complete_received_R_canonical_source :
 completeReceivedRQuartet observation nontrivial half initial origin mother packet=
 OriginalR.variableAction observation nontrivial half
  (completeRSourceRead initial origin packet.1 (completeResidualSourceCoordinate initial origin packet,0)) := by
 exact (complete_received_R_four_feet observation nontrivial half initial origin mother packet).trans
  (congrArg (fun value=>OriginalR.variableAction observation nontrivial half
   (completeRSourceRead initial origin packet.1 value))
   (complete_residual_total_coordinate initial origin packet))

/-- Complete inverse, full relation-word recovery and its generated cochain share the exact paid source. -/
def CompleteResidualRelationAcceptance : Prop :=
 (type_of% (source_residual_boundary (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))) ∧
 (type_of% (source_residual_generated_effect (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))) ∧
 (type_of% (source_residual_canonical_read (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))) ∧
 (type_of% (F.actual_inverse (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)))) ∧
 (type_of% (F.relation_recovery (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)))) ∧
 (type_of% (F.generated_relation (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)))) ∧
 (type_of% (F.generated_cochain (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)))) ∧
 (type_of% (F.generated_differential (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)))) ∧
 (type_of% (F.differential_effect (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)))) ∧
 (type_of% (F.whole_paid_trace (sourceResidualMaterial (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))))
attribute [local irreducible] CompleteResidualRelationAcceptance

theorem complete_residual_relation_acceptance : CompleteResidualRelationAcceptance initial origin packet := by
 unfold CompleteResidualRelationAcceptance
 exact ⟨source_residual_boundary _ _,source_residual_generated_effect _ _,source_residual_canonical_read _ _,
  F.actual_inverse _,F.relation_recovery _,F.generated_relation _,F.generated_cochain _,F.generated_differential _,
  F.differential_effect _,F.whole_paid_trace _⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
