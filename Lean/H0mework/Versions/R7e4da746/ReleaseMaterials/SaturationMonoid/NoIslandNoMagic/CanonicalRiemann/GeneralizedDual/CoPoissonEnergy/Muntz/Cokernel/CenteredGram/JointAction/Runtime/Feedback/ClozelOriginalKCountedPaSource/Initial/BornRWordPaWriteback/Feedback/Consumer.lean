import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Transport
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "RelationFeedback"

/-! The original runtime whole/next and the independent common-action, receiver
and completed-cochain consumers read the same generated R relation. -/

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

namespace Model
export ActualCofinalCommonAction
 (modelAction projection action nativeRestriction model_action_source model_action_native
 actual_receiver_square)
end Model
namespace Tower
export ActualCofinalNativeTower (CommonWords sourceMap)
end Tower
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
 (actual_whole)
end SF
namespace Admissions
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (index)
end Admissions

/-- The original source occurrence enters the already generated common action model. -/
noncomputable def actualCommonWord (update cutoff : Nat) :
 Tower.CommonWords factory initial programme rfl :=
 DFinsupp.single (update + 2)
  (actualRelation observation nontrivial half depth ordinal update cutoff).val

/-- The same born equation has an independent completed-cochain consumer. -/
theorem actualNextJoint_consumed (update cutoff : Nat) : type_of%
 (Cx.completion_kills_generated_differential
  (jointHistoryAt (D.packetAt factory initial programme rfl ((update + 2) + 1)))
  (actualNextJointRelation observation nontrivial half depth ordinal update cutoff)) :=
 Cx.completion_kills_generated_differential _
  (actualNextJointRelation observation nontrivial half depth ordinal update cutoff)

/-- Source action, full affine write, exact whole/next and independent consumers share this occurrence. -/
theorem actual_R_relation_action_feedback (update cutoff : Nat) :
 HEq (actualRelation observation nontrivial half depth ordinal update cutoff).val
  (actualGamma observation nontrivial half depth ordinal update cutoff) ∧
 HEq (actualNextRelation observation nontrivial half depth ordinal update cutoff).val
  (currentAction observation nontrivial half depth ordinal update cutoff).val ∧
 type_of% (Model.model_action_source factory initial programme rfl
  (actualCommonWord observation nontrivial half depth ordinal update cutoff)) ∧
 type_of% (Model.model_action_native factory initial programme rfl
  (actualCommonWord observation nontrivial half depth ordinal update cutoff)) ∧
 type_of% (Model.actual_receiver_square factory initial programme rfl (update + 2)
  (actualRelation observation nontrivial half depth ordinal update cutoff).val) ∧
 type_of% (actualNextJoint_consumed observation nontrivial half depth ordinal update cutoff) ∧
 type_of% (SF.actual_whole factory initial programme rfl
  (Admissions.index factory initial programme rfl ((update + 2) + 1) - 1)) ∧
 type_of% (BornRSealedSourceWriteback.actual_written_born_next
  observation nontrivial half depth ordinal (update + 2)) :=
 ⟨actualRelation_source observation nontrivial half depth ordinal update cutoff,
  actualNextRelation_source observation nontrivial half depth ordinal update cutoff,
  Model.model_action_source factory initial programme rfl
   (actualCommonWord observation nontrivial half depth ordinal update cutoff),
  Model.model_action_native factory initial programme rfl
   (actualCommonWord observation nontrivial half depth ordinal update cutoff),
  Model.actual_receiver_square factory initial programme rfl (update + 2)
   (actualRelation observation nontrivial half depth ordinal update cutoff).val,
  actualNextJoint_consumed observation nontrivial half depth ordinal update cutoff,
  SF.actual_whole factory initial programme rfl
   (Admissions.index factory initial programme rfl ((update + 2) + 1) - 1),
  BornRSealedSourceWriteback.actual_written_born_next
   observation nontrivial half depth ordinal (update + 2)⟩

end CountedPaInitial.BornRWordPaWriteback.RelationFeedback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
