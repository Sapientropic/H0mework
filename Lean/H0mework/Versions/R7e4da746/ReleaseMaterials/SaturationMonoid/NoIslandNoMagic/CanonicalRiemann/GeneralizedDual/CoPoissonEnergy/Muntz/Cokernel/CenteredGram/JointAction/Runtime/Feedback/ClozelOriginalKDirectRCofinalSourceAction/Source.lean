import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalPaUpdate.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMaterial.Whole
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaWindowCofinalSourceCompletion.Decoder
import H0mework.Realization.ScalarCofinal.RootOccurrence

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open CategoryTheory
open scoped InnerProductSpace Topology

namespace Window
export OriginalKPaWindowCofinalSourceCompletion
 (PaSourceCarrier sourceNu windowRead windowTransition sourceData source_data_compatible
  sourceCompletionMap source_completion_window_readback sourceCompletionEquiv completedSource sourceDecoder inverseSourceDecoder
  source_data_kernel_separated
  source_window_read source_literal_window_read source_decoder_generated inverse_source_decoder_generated
  completed_source_window_read)
end Window
namespace Update
export OriginalKDirectRCofinalPaUpdate
 (sourceWholeUnit sourceCorrection source_correction_memPa actual_Pa_source_successor)
end Update
namespace PA
export OriginalKCombCofinalPaAction (actualPa actualPa_mem E invisible)
end PA
namespace D
export OriginalKCombFirstFullSourceDynamics (packet raw)
end D
namespace P
export OriginalKCombPhysicalAction (R)
end P
namespace C
export OriginalKCombReceiptFeedback (Value Var)
end C
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
 (Value groups)
end L
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
 (collapseValue)
end CF
namespace FR
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation
 (completeInput)
end FR
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
 (sourceOccurrence source_root source_trace whole_paid_trace)
end F
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial occurrence)
end R
namespace Parent
export OriginalKDirectRCofinalMaterial
 (actual_material_input actual_old_paid_code actual_old_paid_branches actual_successor
  actual_born_old_paid actual_successor_paid_value actual_successor_branches)
end Parent
local instance originalGroups (grade : Nat) :
 ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
local instance sourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def actualPaSource : Window.PaSourceCarrier :=
 ⟨PA.actualPa observation nontrivial half depth ordinal,
  PA.actualPa_mem observation nontrivial half depth ordinal⟩

/-- The point is projected from this original packet, independently of the constant cofinal Data label. -/
theorem actual_source_point_from_packet :
 let packet:=D.packet observation nontrivial half depth ordinal
 let point:=FR.completeInput (fun target name =>
  CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment target name,0)) () ()
 (actualPaSource observation nontrivial half depth ordinal).val=PA.E (point.1+point.2) := rfl

def correctionSource : Window.PaSourceCarrier :=
 ⟨Update.sourceCorrection observation nontrivial half depth ordinal,
  Update.source_correction_memPa observation nontrivial half depth ordinal⟩

def wholeUnitSource : Window.PaSourceCarrier :=
 ⟨PA.E (Update.sourceWholeUnit observation nontrivial half : BurnolL2),
  Submodule.starProjection_apply_mem _ _⟩

def reentrySource : Window.PaSourceCarrier :=
 ⟨PA.E (P.R observation nontrivial half
   (PA.invisible (D.raw observation nontrivial half depth ordinal))),
  Submodule.starProjection_apply_mem _ _⟩

theorem actual_source_successor :
 actualPaSource observation nontrivial half depth (ordinal+1)=
 correctionSource observation nontrivial half depth ordinal+
 OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal •
  wholeUnitSource observation nontrivial half+
 reentrySource observation nontrivial half depth ordinal :=
 Subtype.ext (Update.actual_Pa_source_successor observation nontrivial half depth ordinal)

/-- This is the original query's actual action material, retaining its paid trace and responsibility owner. -/
def actualMaterial :=
 let packet:=D.packet observation nontrivial half depth ordinal
 R.actualMaterial packet.2.1.1 packet.2.2.1

def actualSourceHistory := F.sourceOccurrence (actualMaterial observation nontrivial half depth ordinal)

def actualCofinalOccurrence :=
 (actualSourceHistory observation nontrivial half depth ordinal).map
  (fun event => (event,Window.sourceData))

def actualCofinalFace :=
 SourceGeneratedScalarCofinalRootOccurrence.Face.generate
  (occurrence:=actualCofinalOccurrence observation nontrivial half depth ordinal)

theorem actualCofinalCalculation :
 SourceGeneratedScalarCofinalRootOccurrence.Face.GeneratedCompatibilityCalculationAt
  (actualCofinalFace observation nontrivial half depth ordinal) :=
 (actualCofinalFace observation nontrivial half depth ordinal).generateCompatibility (by
  change (actualCofinalFace observation nontrivial half depth ordinal).data.Compatible
  rw [show (actualCofinalFace observation nontrivial half depth ordinal).data=Window.sourceData from by
   exact ((actualCofinalFace observation nontrivial half depth ordinal).data_root).trans (by
    rw [actualCofinalOccurrence,RootedAccountedUnfolding.root_map])]
  exact Window.source_data_compatible)

theorem actual_cofinal_data :
 (actualCofinalFace observation nontrivial half depth ordinal).data=Window.sourceData := by
 exact ((actualCofinalFace observation nontrivial half depth ordinal).data_root).trans (by
  rw [actualCofinalOccurrence,RootedAccountedUnfolding.root_map])

theorem actual_cofinal_preserves_history :
 (actualCofinalFace observation nontrivial half depth ordinal).root=
 actualSourceHistory observation nontrivial half depth ordinal := by
 change ((actualSourceHistory observation nontrivial half depth ordinal).map
  (fun event => (event,Window.sourceData))).map Prod.fst=_
 rw [RootedAccountedUnfolding.map_map]
 exact RootedAccountedUnfolding.map_id _

theorem actual_source_root :
 let packet:=D.packet observation nontrivial half depth ordinal
 (actualSourceHistory observation nontrivial half depth ordinal).root=
 (R.occurrence packet.2.1.1 packet.2.2.1,
  PresentedRelationEventAt.generator
   (actualMaterial observation nontrivial half depth ordinal).raw) := F.source_root _

theorem actual_source_trace : type_of%
 (F.source_trace (actualMaterial observation nontrivial half depth ordinal)) := F.source_trace _

theorem actual_whole_paid_trace : type_of%
 (F.whole_paid_trace (actualMaterial observation nontrivial half depth ordinal)) := F.whole_paid_trace _

theorem actual_source_input : type_of%
 (Parent.actual_material_input observation nontrivial half depth ordinal) := Parent.actual_material_input _ _ _ _ _

def actualCofinalValue :=
 (actualCofinalFace observation nontrivial half depth ordinal).completionMap
  (actualCofinalCalculation observation nontrivial half depth ordinal)
  (actualPaSource observation nontrivial half depth ordinal)

theorem actual_cofinal_injective : Function.Injective
 ((actualCofinalFace observation nontrivial half depth ordinal).completionMap
  (actualCofinalCalculation observation nontrivial half depth ordinal)) :=
 (actualCofinalFace observation nontrivial half depth ordinal).completionMap_injective
  (actualCofinalCalculation observation nontrivial half depth ordinal) (by
   rw [actual_cofinal_data]
   exact Window.source_data_kernel_separated)

theorem actual_cofinal_window_read (stage : Nat) :
 (actualCofinalFace observation nontrivial half depth ordinal).data.stageRealization stage
  ((actualCofinalFace observation nontrivial half depth ordinal).restriction
   (actualCofinalCalculation observation nontrivial half depth ordinal) stage
   (actualCofinalValue observation nontrivial half depth ordinal))=
 Window.windowRead stage (actualPaSource observation nontrivial half depth ordinal) := by
 have readPoint (data : type_of% Window.sourceData) (compatible : data.Compatible)
  (identity : data=Window.sourceData) :
  data.stageRealization stage
   (data.restriction compatible stage
    (data.completionMap compatible (actualPaSource observation nontrivial half depth ordinal)))=
  Window.windowRead stage (actualPaSource observation nontrivial half depth ordinal) := by
  cases identity
  exact ConcreteCategory.congr_hom (Window.source_completion_window_readback stage)
   (actualPaSource observation nontrivial half depth ordinal)
 exact readPoint _ _ (actual_cofinal_data observation nontrivial half depth ordinal)

theorem actual_cofinal_completion_source :
 HEq (actualCofinalValue observation nontrivial half depth ordinal)
  (Window.sourceCompletionMap (actualPaSource observation nontrivial half depth ordinal)) := by
 change HEq
  ((actualCofinalFace observation nontrivial half depth ordinal).data.completionMap
   (actualCofinalCalculation observation nontrivial half depth ordinal).laws
   (actualPaSource observation nontrivial half depth ordinal))
  (Window.sourceCompletionMap (actualPaSource observation nontrivial half depth ordinal))
 have transport (data : type_of% Window.sourceData) (compatible : data.Compatible)
  (identity : data=Window.sourceData) :
  HEq (data.completionMap compatible (actualPaSource observation nontrivial half depth ordinal))
   (Window.sourceCompletionMap (actualPaSource observation nontrivial half depth ordinal)) := by
  cases identity
  rfl
 exact transport _ _ (actual_cofinal_data observation nontrivial half depth ordinal)

def actualCompletedSource :=
 Window.completedSource (actualPaSource observation nontrivial half depth ordinal)

theorem actual_completed_decoder :
 Window.sourceDecoder (actualCompletedSource observation nontrivial half depth ordinal)=
 actualPaSource observation nontrivial half depth ordinal :=
 Window.source_decoder_generated _

theorem actual_inverse_source_decoder :
 Window.inverseSourceDecoder (actualCompletedSource observation nontrivial half depth ordinal)=
 burnolMobiusSourceL2 (PA.actualPa observation nontrivial half depth ordinal) :=
 Window.inverse_source_decoder_generated _

theorem actual_literal_source_window (stage : Nat) : type_of%
 (Window.source_literal_window_read stage
  (actualPaSource observation nontrivial half depth ordinal)) :=
 Window.source_literal_window_read _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
