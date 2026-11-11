import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block.StepInterval.Whole
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptStepJointBlock

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptStepJointWhole
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
open PhysicalGammaNextReceiptStepJointBlock (actualStepJointCochain)
open ActualCofinalSourceAction.SourceReceiptOccurrence.Batch (requests groupedRequestLists grouped_request_boundary)
open SourceInventoryExecutionFeed.ReceiptOccurrence (requestWord)
open ActualCofinalResidualModelSplice (packetWordTransport packetLanguageWord)
open private following_literal from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt
open private jointHistoryAt from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Transport
open private reindexed_word_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptStepJointBlock

namespace A
export BornRCanonicalMethodRuntime (W X fixedRFactory)
end A
namespace Cfa
export ActualCofinalSourceAction (sourceBorn nativePacket selected packetTransport)
export ActualCofinalSourceAction.AS (AdmissionPacket)
export ActualCofinalSourceAction.D (packetAt)
export ActualCofinalSourceAction.L (Value groups)
export ActualNativeRelationTransport.AS (stockDecodedEnvironment)
end Cfa
local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance wholeGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value A.W grade t) := Cfa.groups A.W grade

section Packets
variable {Y Z : CompletedSourceRCalculation.Slot → Type}
variable (native : Cfa.AdmissionPacket (W := A.W) (X := Y) (s := slot))
variable (target : Cfa.AdmissionPacket (W := A.W) (X := Z) (s := slot))
variable (language : Y = Z) (same : Cfa.packetTransport language native = target)

private def wordToJoint :
    Formal ℤ (Cfa.Value A.W native.1) Y slot →ₗ[ℤ]
      Formal ℤ (PairValue (Cfa.Value A.W target.1)) Z slot :=
  (liftMap (R := ℤ)).comp
    ((packetWordTransport same).toLinearMap.comp (packetLanguageWord language native).toLinearMap)

private theorem sum_reads_boundary
    (pieces : List (Formal ℤ (Cfa.Value A.W native.1) Y slot))
    (total : Formal ℤ (Cfa.Value A.W native.1) Y slot) (folded : pieces.sum = total)
    (boundary : Formal ℤ (Cfa.Value A.W target.1) Z slot) (actual : HEq boundary total) :
    (pieces.map (wordToJoint native target language same)).sum = liftMap (R := ℤ) boundary := by
  have recognized : packetWordTransport same (packetLanguageWord language native total) = boundary :=
    eq_of_heq ((reindexed_word_source native target language same total).trans actual.symm)
  calc
    _ = wordToJoint native target language same pieces.sum := (map_list_sum _ _).symm
    _ = wordToJoint native target language same total := congrArg (wordToJoint native target language same) folded
    _ = _ := congrArg (liftMap (R := ℤ)) recognized
end Packets

open PhysicalGammaBoundaryFeedback (nextBoundary nextJointBoundary)
open PhysicalGammaNextReceiptBlock (actual_batch_boundary)
open PhysicalGammaNextReceipt (actualBirth)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : BornRSourcePrice.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
  (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff)

local notation "factory" => A.fixedRFactory observation nontrivial half
local notation "initial" => BornRSourceMethodHistory.receiver observation nontrivial half depth ordinal
local notation "programme" => BornRSourceMethodHistory.methodProgramme observation nontrivial half depth ordinal
local notation "site" => Cfa.packetAt factory initial programme rfl
local notation "current" => site (update+2)
local notation "nextSite" => site ((update+2)+1)
local notation "born" => actualBirth observation nontrivial half depth ordinal method
local notation "native" => Cfa.sourceBorn factory current
set_option quotPrecheck false in
local notation "language" => (current).2.2.2.down
local notation "recognition" => following_literal observation nontrivial half depth ordinal (update := update)
set_option quotPrecheck false in
local notation "decoder" =>
  Cfa.stockDecodedEnvironment (Cfa.selected factory current) (Cfa.nativePacket factory current).2.2.1
local notation "stepCochain" => actualStepJointCochain observation nontrivial half depth ordinal method
local notation "oldBoundary" => nextBoundary observation nontrivial half depth ordinal method
local notation "oldJoint" => nextJointBoundary observation nontrivial half depth ordinal method

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
/-- All actual source Step cochains fold in order to the original whole Joint boundary. -/
theorem actual_grouped_joint_boundary : (List.ofFn stepCochain).sum = oldJoint := by
  let pieces := (groupedRequestLists factory current born).map (fun items => (items.map (requestWord decoder)).sum)
  let total := ((requests factory current born).map (requestWord decoder)).sum
  let mapWord := wordToJoint native nextSite language recognition
  let space := (jointHistoryAt nextSite).relationClosure
  apply Subtype.ext
  have asList : ((List.ofFn stepCochain).map space.subtype) = pieces.map mapWord := by
    simp only [pieces, groupedRequestLists, List.map_ofFn]
    rfl
  exact (map_list_sum space.subtype (List.ofFn stepCochain)).trans
    ((congrArg List.sum asList).trans
      (sum_reads_boundary native nextSite language recognition pieces total
        (grouped_request_boundary factory current born) (oldBoundary).val
        (actual_batch_boundary observation nontrivial half depth ordinal method)))

end CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptStepJointWhole
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
