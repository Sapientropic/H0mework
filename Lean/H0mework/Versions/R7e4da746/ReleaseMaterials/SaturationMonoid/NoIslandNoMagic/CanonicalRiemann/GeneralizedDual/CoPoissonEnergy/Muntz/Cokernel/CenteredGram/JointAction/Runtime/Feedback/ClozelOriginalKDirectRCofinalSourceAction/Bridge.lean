import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalSourceAction.Action

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKDirectRCofinalSourceAction"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState CategoryTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open scoped InnerProductSpace Topology
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket nativeAfterAdmission bornAfterNative)
end AS
namespace D
export OriginalKCombFirstFullSourceDynamics (factory)
end D
namespace Window
export OriginalKPaWindowCofinalSourceCompletion (sourceCompletion)
end Window
local instance bridgeGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

abbrev SourcePacket := AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())
abbrev packetMaterial (packet : SourcePacket) := R.actualMaterial packet.2.1.1 packet.2.2.1
def packetHistory (packet : SourcePacket) :=
 (SourceOperationPaidRelations.exposure (packetMaterial packet).state.2).map
  (fun event => (R.occurrence packet.2.1.1 packet.2.2.1,event))

/-- These projections retain the dependent material, actual AST, full paid proof and responsibility owner. -/
def PacketSourceProjectionAt (before after : SourcePacket) : Prop :=
 HEq (packetMaterial before) (packetMaterial after) ∧
 HEq (packetMaterial before).raw (packetMaterial after).raw ∧
 HEq (packetMaterial before).state.2 (packetMaterial after).state.2 ∧
 HEq (packetMaterial before).owner (packetMaterial after).owner ∧
 HEq (packetHistory before) (packetHistory after) ∧
 HEq (packetHistory before).root (packetHistory after).root ∧
 HEq (packetHistory before).trace (packetHistory after).trace

private theorem packet_source_projection {before after : SourcePacket} (same : before=after) :
 PacketSourceProjectionAt before after := by
 cases same
 exact ⟨HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def canonicalBornPacket : SourcePacket :=
 AS.bornAfterNative (AS.nativeAfterAdmission (D.factory observation nontrivial half)
  (D.packet observation nontrivial half depth ordinal))

def CanonicalBornSourceAt : Prop :=
 PacketSourceProjectionAt (D.packet observation nontrivial half depth (ordinal+1))
  (canonicalBornPacket observation nontrivial half depth ordinal) ∧
 HEq (actualCofinalFace observation nontrivial half depth (ordinal+1)).root
  (packetHistory (canonicalBornPacket observation nontrivial half depth ordinal))

/-- Full packet equality, rather than equality of Pa values, identifies this source occurrence. -/
theorem source_born_projection
 (successor : type_of% (Parent.actual_successor observation nontrivial half depth ordinal)) :
 CanonicalBornSourceAt observation nontrivial half depth ordinal := by
 have packet := packet_source_projection successor
 exact ⟨packet,(heq_of_eq (actual_cofinal_preserves_history observation nontrivial half depth (ordinal+1))).trans packet.2.2.2.2.1⟩

theorem actual_born_source_projection : CanonicalBornSourceAt observation nontrivial half depth ordinal :=
 source_born_projection observation nontrivial half depth ordinal
  (Parent.actual_successor observation nontrivial half depth ordinal)

/-- Transport is controlled by the generated face's Data identity and compatibility proof. -/
def completionToWindow (data : type_of% Window.sourceData) (compatible : data.Compatible)
 (identity : data=Window.sourceData) :
 data.Completion compatible →ₗ[ℂ] Window.sourceCompletion := by
 cases identity
 exact LinearMap.id

theorem completion_to_window_map (data : type_of% Window.sourceData) (compatible : data.Compatible)
 (identity : data=Window.sourceData) (point : Window.PaSourceCarrier) :
 completionToWindow data compatible identity (data.completionMap compatible point)=Window.sourceCompletionMap point := by
 cases identity
 rfl

/-- The input here is the actual dependent cofinal value, not a parallel completedSource value. -/
def actualWindowValue : Window.sourceCompletion :=
 completionToWindow (actualCofinalFace observation nontrivial half depth ordinal).data
  (actualCofinalCalculation observation nontrivial half depth ordinal).laws
  (actual_cofinal_data observation nontrivial half depth ordinal)
  (actualCofinalValue observation nontrivial half depth ordinal)

theorem actual_window_value_source :
 actualWindowValue observation nontrivial half depth ordinal=
 Window.sourceCompletionMap (actualPaSource observation nontrivial half depth ordinal) :=
 completion_to_window_map _ _ _ _

def completionImage (point : Window.PaSourceCarrier) (value : Window.sourceCompletion)
 (generated : value=Window.sourceCompletionMap point) : LinearMap.range Window.sourceCompletionMap.hom :=
 ⟨value,⟨point,generated.symm⟩⟩

theorem completion_image_value (point : Window.PaSourceCarrier) (value : Window.sourceCompletion)
 (generated : value=Window.sourceCompletionMap point) : (completionImage point value generated).val=value := rfl

theorem completion_image_generated (point : Window.PaSourceCarrier) (value : Window.sourceCompletion)
 (generated : value=Window.sourceCompletionMap point) :
 completionImage point value generated=Window.completedSource point := Subtype.ext generated

/-- Its range witness is generated by this exact source point and actual completion map. -/
def actualFaceImage :=
 completionImage (actualPaSource observation nontrivial half depth ordinal)
  (actualWindowValue observation nontrivial half depth ordinal)
  (actual_window_value_source observation nontrivial half depth ordinal)

theorem actual_face_image_value :
 (actualFaceImage observation nontrivial half depth ordinal).val=
 actualWindowValue observation nontrivial half depth ordinal := completion_image_value _ _ _

theorem actual_face_image_source :
 actualFaceImage observation nontrivial half depth ordinal=actualCompletedSource observation nontrivial half depth ordinal :=
 completion_image_generated _ _ _

theorem actual_face_decoder :
 Window.sourceDecoder (actualFaceImage observation nontrivial half depth ordinal)=
 actualPaSource observation nontrivial half depth ordinal :=
 (congrArg Window.sourceDecoder (actual_face_image_source observation nontrivial half depth ordinal)).trans
  (actual_completed_decoder observation nontrivial half depth ordinal)

theorem actual_face_inverse_decoder :
 Window.inverseSourceDecoder (actualFaceImage observation nontrivial half depth ordinal)=
 burnolMobiusSourceL2 (PA.actualPa observation nontrivial half depth ordinal) :=
 (congrArg Window.inverseSourceDecoder (actual_face_image_source observation nontrivial half depth ordinal)).trans
  (actual_inverse_source_decoder observation nontrivial half depth ordinal)

theorem actual_face_decoder_successor :
 Window.sourceDecoder (actualFaceImage observation nontrivial half depth (ordinal+1))=
 correctionSource observation nontrivial half depth ordinal+
 Division.sourceCoefficient observation nontrivial half depth ordinal • wholeUnitSource observation nontrivial half+
 reentrySource observation nontrivial half depth ordinal :=
 (actual_face_decoder observation nontrivial half depth (ordinal+1)).trans
  (actual_source_successor observation nontrivial half depth ordinal)

theorem actual_face_inverse_decoder_successor :
 Window.inverseSourceDecoder (actualFaceImage observation nontrivial half depth (ordinal+1))=
 Window.sourceNu (correctionSource observation nontrivial half depth ordinal)+
 Division.sourceCoefficient observation nontrivial half depth ordinal • Window.sourceNu (wholeUnitSource observation nontrivial half)+
 Window.sourceNu (reentrySource observation nontrivial half depth ordinal) :=
 (actual_face_inverse_decoder observation nontrivial half depth (ordinal+1)).trans
  (actual_source_nu_successor observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
