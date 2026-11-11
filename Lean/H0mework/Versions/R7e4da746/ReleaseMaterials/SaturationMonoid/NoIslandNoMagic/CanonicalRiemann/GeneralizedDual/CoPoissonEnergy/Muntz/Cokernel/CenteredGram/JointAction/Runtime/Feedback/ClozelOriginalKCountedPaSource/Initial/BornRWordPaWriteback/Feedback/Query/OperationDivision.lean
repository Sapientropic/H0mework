import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Query.OperationEffect
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.RStepIndexedPaSplitSource.Division

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback.RelationFeedback.FullActionQuery.OperationDivision
open CenteredGram.IntegralGraphJointAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open private source from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Readback
namespace Op
export OperationEffect
 (nativeInput nativeDecoder bornQueryValue born_operation_effect actual_R_query_operation_effect)
end Op
namespace Div
export RStepIndexedPaSplitSource.Division
 (qualified pa nonPa pa_gap pa_unit_rank sum outside)
end Div
attribute [local instance] baseGroups levelGroups
local notation "slot" => CompletedSourceRCalculation.Slot.branches
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (packet : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))

def oldInput : CompletedSourceRCalculation.Value slot :=
 M.wholeProjection (packet.1+1) ((Op.nativeInput packet.1 packet.2.1.1).eval
  (fun target name => (Op.nativeDecoder observation nontrivial half packet target name).1))

def effectInput : CompletedSourceRCalculation.Value slot :=
 M.wholeProjection (packet.1+1) ((Op.nativeInput packet.1 packet.2.1.1).effect
  (fun target name => (Op.nativeDecoder observation nontrivial half packet target name).1)
  (fun target name => (Op.nativeDecoder observation nontrivial half packet target name).2))

def historicalValue : CompletedSourceRCalculation.Value slot :=
 M.wholeProjection (packet.1+1)
  (ScalarRelationPresentation.freeEvaluation (R := ℤ) (Lower.Value A.W (packet.1+1) slot)
   (A.nativeWordData observation nontrivial half packet.1 packet.2.1.1).nu)

variable (relation : (actualBornHistory observation nontrivial half packet).relationClosure)

def oldUpdated : CompletedSourceRCalculation.Value slot :=
 oldInput observation nontrivial half packet +
  M.wholeProjection (packet.1+1) (Op.bornQueryValue observation nontrivial half packet relation).1 +
  historicalValue observation nontrivial half packet

def effectUpdated : CompletedSourceRCalculation.Value slot :=
 effectInput observation nontrivial half packet +
  M.wholeProjection (packet.1+1) (Op.bornQueryValue observation nontrivial half packet relation).2

local notation "a" => oldInput observation nontrivial half packet
local notation "d" => effectInput observation nontrivial half packet
local notation "oldNext" => oldUpdated observation nontrivial half packet relation
local notation "effectNext" => effectUpdated observation nontrivial half packet relation

/-- Both actual query channels enter the existing source-generated Division, with Q and outside retained. -/
theorem born_division
 (generated : HEq relation.val
  (A.nativeWordData observation nontrivial half packet.1 packet.2.1.1).gamma) :
 oldNext = Div.pa observation nontrivial half a + Div.nonPa observation nontrivial half a ∧
 effectNext = Div.pa observation nontrivial half d + Div.nonPa observation nontrivial half d ∧
 type_of% (Div.qualified a) ∧
 type_of% (Div.pa_gap observation nontrivial half a) ∧
 type_of% (Div.pa_unit_rank observation nontrivial half a) ∧
 type_of% (Div.qualified d) ∧
 type_of% (Div.pa_gap observation nontrivial half d) ∧
 type_of% (Div.pa_unit_rank observation nontrivial half d) ∧
 oldNext.1.1 - (burnolEvenAmbientProjection oldNext.1.1 : BurnolL2) =
  (Div.nonPa observation nontrivial half a).1.1 -
   (burnolEvenAmbientProjection (Div.nonPa observation nontrivial half a).1.1 : BurnolL2) ∧
 effectNext.1.1 - (burnolEvenAmbientProjection effectNext.1.1 : BurnolL2) =
  (Div.nonPa observation nontrivial half d).1.1 -
   (burnolEvenAmbientProjection (Div.nonPa observation nontrivial half d).1.1 : BurnolL2) := by
 have action := Op.born_operation_effect observation nontrivial half packet relation generated
 change oldNext = OriginalKFullSourceRAction.variableAction observation nontrivial half a ∧
  effectNext = OriginalKFullSourceRAction.variableAction observation nontrivial half d at action
 have oldOutside : oldNext.1.1 - (burnolEvenAmbientProjection oldNext.1.1 : BurnolL2) =
   (Div.nonPa observation nontrivial half a).1.1 -
    (burnolEvenAmbientProjection (Div.nonPa observation nontrivial half a).1.1 : BurnolL2) := by
  rw [action.1]
  exact Div.outside observation nontrivial half a
 have effectOutside : effectNext.1.1 - (burnolEvenAmbientProjection effectNext.1.1 : BurnolL2) =
   (Div.nonPa observation nontrivial half d).1.1 -
    (burnolEvenAmbientProjection (Div.nonPa observation nontrivial half d).1.1 : BurnolL2) := by
  rw [action.2]
  exact Div.outside observation nontrivial half d
 exact ⟨action.1.trans (Div.sum observation nontrivial half a),
  action.2.trans (Div.sum observation nontrivial half d),
  Div.qualified a, Div.pa_gap observation nontrivial half a, Div.pa_unit_rank observation nontrivial half a,
  Div.qualified d, Div.pa_gap observation nontrivial half d, Div.pa_unit_rank observation nontrivial half d,
  oldOutside, effectOutside⟩

variable (depth ordinal update cutoff : Nat)

/-- The source's whole/next writeback and both independent Division consumers share all original parameters. -/
theorem actual_R_query_operation_division :
 type_of% (actual_R_full_action_query_writeback observation nontrivial half depth ordinal update cutoff) ∧
 type_of% (Op.actual_R_query_operation_effect observation nontrivial half depth ordinal update cutoff) ∧
 type_of% (born_division observation nontrivial half
  (source observation nontrivial half depth ordinal update cutoff)
  (actualBornRelation observation nontrivial half depth ordinal update cutoff).1
  ((actualBornRelation observation nontrivial half depth ordinal update cutoff).2.trans
   (heq_of_eq (actual_gamma_source observation nontrivial half depth ordinal update cutoff)))) :=
 ⟨actual_R_full_action_query_writeback observation nontrivial half depth ordinal update cutoff,
  Op.actual_R_query_operation_effect observation nontrivial half depth ordinal update cutoff,
  born_division observation nontrivial half
   (source observation nontrivial half depth ordinal update cutoff)
   (actualBornRelation observation nontrivial half depth ordinal update cutoff).1
   ((actualBornRelation observation nontrivial half depth ordinal update cutoff).2.trans
    (heq_of_eq (actual_gamma_source observation nontrivial half depth ordinal update cutoff)))⟩

end CountedPaInitial.BornRWordPaWriteback.RelationFeedback.FullActionQuery.OperationDivision
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
