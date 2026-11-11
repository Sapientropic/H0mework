import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Source
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RelationFeedback"

/-! Literal original-packet transport retains the complete inventory through the
actual born successor and into its same-packet Joint consumer. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback.RelationFeedback
open CenteredGram.IntegralGraphJointAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open private transportRelation transportRelation_source from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Source
attribute [local instance] baseGroups levelGroups
open private jointHistoryAt jointInventoryAt from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Transport
local notation "slot" => CompletedSourceRCalculation.Slot.branches
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "factory" => A.fixedRFactory observation nontrivial half
local notation "initial" => H.receiver observation nontrivial half depth ordinal
local notation "programme" => H.methodProgramme observation nontrivial half depth ordinal



theorem currentPacket_actual (update cutoff : Nat) :
 currentPacket observation nontrivial half depth ordinal update cutoff =
 D.packetAt factory initial programme rfl (update + 2) := by
 unfold currentPacket
 exact actual_born_packet observation nontrivial half depth ordinal update cutoff

/-- The generated full packet successor, with the original inventory and root identity. -/
theorem nextPacket_actual (update cutoff : Nat) :
 AS.bornAfterNative (AS.nativeAfterAdmission factory
  (currentPacket observation nontrivial half depth ordinal update cutoff)) =
 D.packetAt factory initial programme rfl ((update + 2) + 1) :=
 (congrArg (fun packet => AS.bornAfterNative (AS.nativeAfterAdmission factory packet))
  (currentPacket_actual observation nontrivial half depth ordinal update cutoff)).trans
 (D.packetAt_successor factory initial programme rfl (update + 2)).symm

noncomputable def actualRelation (update cutoff : Nat) :
 RelationAt (D.packetAt factory initial programme rfl (update + 2)) :=
 transportRelation (currentPacket_actual observation nontrivial half depth ordinal update cutoff)
  (currentRelation observation nontrivial half depth ordinal update cutoff)

noncomputable def actualNextRelation (update cutoff : Nat) :
 RelationAt (D.packetAt factory initial programme rfl ((update + 2) + 1)) :=
 transportRelation (nextPacket_actual observation nontrivial half depth ordinal update cutoff)
  (actionNextRelation factory (currentPacket observation nontrivial half depth ordinal update cutoff)
   (currentRelation observation nontrivial half depth ordinal update cutoff))

theorem actualNextRelation_source (update cutoff : Nat) :
 HEq (actualNextRelation observation nontrivial half depth ordinal update cutoff).val
  (currentAction observation nontrivial half depth ordinal update cutoff).val := by
 unfold actualNextRelation currentAction
 exact (transportRelation_source
  (nextPacket_actual observation nontrivial half depth ordinal update cutoff)
  (actionNextRelation factory (currentPacket observation nontrivial half depth ordinal update cutoff)
   (currentRelation observation nontrivial half depth ordinal update cutoff))).trans
  (actionNextRelation_source factory
   (currentPacket observation nontrivial half depth ordinal update cutoff)
   (currentRelation observation nontrivial half depth ordinal update cutoff))

theorem actualRelation_source (update cutoff : Nat) :
 HEq (actualRelation observation nontrivial half depth ordinal update cutoff).val
  (actualGamma observation nontrivial half depth ordinal update cutoff) := by
 unfold actualRelation
 exact (transportRelation_source
  (currentPacket_actual observation nontrivial half depth ordinal update cutoff)
  (currentRelation observation nontrivial half depth ordinal update cutoff)).trans
  (currentRelation_source observation nontrivial half depth ordinal update cutoff)

private theorem transportAction_source
 {before after : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot)}
 (same : before = after) (relation : RelationAt before) :
 HEq (Cfa.sourceWordAction after (transportRelation same relation).val)
  (Cfa.sourceWordAction before relation.val) := by
 cases same
 exact HEq.rfl

theorem actualAction_source (update cutoff : Nat) :
 HEq (Cfa.sourceWordAction (D.packetAt factory initial programme rfl (update + 2))
   (actualRelation observation nontrivial half depth ordinal update cutoff).val)
  (Cfa.sourceWordAction (currentPacket observation nontrivial half depth ordinal update cutoff)
   (currentRelation observation nontrivial half depth ordinal update cutoff).val) := by
 unfold actualRelation
 exact transportAction_source
  (currentPacket_actual observation nontrivial half depth ordinal update cutoff)
  (currentRelation observation nontrivial half depth ordinal update cutoff)

/-- The same-packet Joint directly consumes the retained full inventory. -/
theorem jointRelation_member
 (packet : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (relation : RelationAt packet) :
 liftMap (R := ℤ) relation.val ∈ SourceInventoryExecutionFeed.relationSpace (jointInventoryAt packet) :=
 PairTransport.relation_next packet.2.1.1 relation.inventory relation.installed relation.val relation.member

/-- The equation is written to this actual next Joint inventory. -/
noncomputable def actualNextJointRelation (update cutoff : Nat) :
 (jointHistoryAt (D.packetAt factory initial programme rfl ((update + 2) + 1))).relationClosure :=
 ⟨liftMap (R := ℤ) (actualNextRelation observation nontrivial half depth ordinal update cutoff).val, by
  simpa only [jointHistoryAt, Feed.history_relation_space] using
   jointRelation_member (D.packetAt factory initial programme rfl ((update + 2) + 1))
    (actualNextRelation observation nontrivial half depth ordinal update cutoff)⟩

end CountedPaInitial.BornRWordPaWriteback.RelationFeedback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
