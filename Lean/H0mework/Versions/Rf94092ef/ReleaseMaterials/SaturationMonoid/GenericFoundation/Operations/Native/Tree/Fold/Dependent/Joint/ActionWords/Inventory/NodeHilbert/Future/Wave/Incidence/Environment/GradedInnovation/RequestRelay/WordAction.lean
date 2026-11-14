import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.RequestRelay.Effect
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Action
import H0mework.Versions.Red5c4028.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection.DualColumn.Insert

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation.Integrated

open SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationInquiry.Context.Installation (executedEnvironmentIncrement)
open SourceInventoryExecutionFeed.AdmissionReceipt (formalItems update_inventory_formal_items)
open SourceGeneratedFiniteGram (Coordinates)
open SourceGeneratedFiniteGram.Projection (synthesis)
open scoped InnerProductSpace

open private synthesis_single from H0mework.Versions.Red5c4028.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection.DualColumn.Insert

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (packet next : RelayPacket (K := K) X)
variable (literal : next = Action.packetTransport packet.2.2.2.down (Action.sourceBorn (factory read) packet))
variable (prior : SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) packet.1) (X := X) (s := .joint))
variable (present : packet.2.1.1.inventory = some prior)
variable (event : Fin prior.trace.length)

set_option quotPrecheck false in
local notation "frame" => A.epoch next.2.1.1
set_option quotPrecheck false in
local notation "occurrence" => S.actualOccurrence next.2.1.1
local notation "items" => Feed.eventItems (relayedEvent read packet next literal prior present event)
local notation "address" => relayedRequest read packet next literal prior present event

/-- Evaluate the complete signed word of the carried event in the actual next material. -/
def relayedWordValue : PairValue (L.Value (W K) next.1) .joint :=
  let material := I.materialAt (frame) (occurrence)
  updateInventory (R := ℤ) material.raw.environment
    (executedEnvironmentIncrement (frame) (occurrence)) (formalItems (items))

theorem relayed_word_value :
    (∑ i : Fin (items).length,
      ((items).get i).2 • columnActionValue next.1 (frame) (occurrence) ((address) i)) =
      relayedWordValue read packet next literal prior present event := by
  let material := I.materialAt (frame) (occurrence)
  let increment := executedEnvironmentIncrement (frame) (occurrence)
  let environment := pairEnvironment material.raw.environment increment
  calc
    _ = ∑ i : Fin (items).length,
        ((items).get i).2 • (liftExpr ((items).get i).1).eval environment := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [columnActionValue, relayed_request_read, environment, material, increment]
    _ = _ := update_inventory_formal_items material.raw.environment increment (items)

/-- Every actual signed item contributes its own generated request coordinate. -/
def relayedWordCoordinates : Coordinates (Index next.1 (frame)) :=
  ∑ i : Fin (items).length, PiLp.single 2 ((address) i) (1 : ℂ)

theorem relayed_word_synthesis :
    synthesis (columns read next.1 (frame) (occurrence))
        (relayedWordCoordinates read packet next literal prior present event) =
      columnRead read next.1 (relayedWordValue read packet next literal prior present event) := by
  let source := columns read next.1 (frame) (occurrence)
  let measure := columnRead read next.1
  let actual := columnActionValue next.1 (frame) (occurrence)
  let positions := address
  let entries := items
  calc
    _ = ∑ i : Fin entries.length, source (positions i) := by
      simp only [relayedWordCoordinates, map_sum, synthesis_single, source, positions, entries]
    _ = ∑ i : Fin entries.length, measure ((entries.get i).2 • actual (positions i)) := by
      apply Finset.sum_congr rfl
      intro i _
      let pair := actual (positions i)
      have split : (pair.1,0)+(0,pair.2) = pair := by
        rw [Prod.mk_add_mk,add_zero,zero_add]
      rw [map_zsmul, show source (positions i) = _ from actual_column_from_action read next.1 (frame) (occurrence) (positions i)]
      dsimp only [columnAction,positions,entries]
      rw [relayed_request_read]
      change (entries.get i).2 • measure (pair.1,0) + (entries.get i).2 • measure (0,pair.2) = _
      rw [← smul_add, ← map_add, split]
    _ = measure (∑ i : Fin entries.length, (entries.get i).2 • actual (positions i)) := (map_sum _ _ _).symm
    _ = _ := congrArg measure (relayed_word_value read packet next literal prior present event)

/-- The original word supplies an exact right-hand side in the next action's Gram equation. -/
theorem relayed_word_action_equation :
    SourceGeneratedFiniteGram.action (columnActionGram read next.1 (frame) (occurrence))
        (relayedWordCoordinates read packet next literal prior present event) =
      columnActionRhs read next.1 (frame) (occurrence)
        (columnRead read next.1 (relayedWordValue read packet next literal prior present event)) := by
  rw [← actual_gram_from_column_actions, ← actual_gram_rhs_from_column_actions, ← relayed_word_synthesis]
  ext i
  exact SourceGeneratedFiniteGram.Projection.action_read _ _ i

/-- The existing inverse fibre pays the actual word by translating its coefficient class. -/
theorem relayed_word_coefficient_change (value : K) :
    let response := columnRead read next.1 (relayedWordValue read packet next literal prior present event)
    let carried := relayedWordCoordinates read packet next literal prior present event
    columnActionCoefficients read next.1 (frame) (occurrence) value + carried -
      columnActionCoefficients read next.1 (frame) (occurrence) (value+response) ∈
        SourceGeneratedFiniteGram.Kernel (columnActionGram read next.1 (frame) (occurrence)) := by
  let response := columnRead read next.1 (relayedWordValue read packet next literal prior present event)
  let carried := relayedWordCoordinates read packet next literal prior present event
  let coeff := columnActionCoefficients read next.1 (frame) (occurrence)
  let matrix := columnActionGram read next.1 (frame) (occurrence)
  let rhs := columnActionRhs read next.1 (frame) (occurrence)
  change coeff value+carried-coeff (value+response) ∈ SourceGeneratedFiniteGram.Kernel matrix
  apply (actual_column_action_fibre read next.1 (frame) (occurrence) (value+response)
    (coeff value+carried)).mp
  have rhsAdd : rhs (value+response) = rhs value+rhs response := by
    dsimp only [rhs]
    simp only [← actual_gram_rhs_from_column_actions]
    ext i
    exact inner_add_right _ _ _
  change SourceGeneratedFiniteGram.action matrix (coeff value+carried) = rhs (value+response)
  rw [map_add, rhsAdd]
  exact congrArg₂ (· + ·) (column_action_equation read next.1 (frame) (occurrence) value)
    (relayed_word_action_equation read packet next literal prior present event)

/-- The actual source word is paid in the existing Gram image and preserves the innovation. -/
theorem relayed_word_innovation (value : K) :
    columnActionInnovation read next.1 (frame) (occurrence)
      (value + columnRead read next.1 (relayedWordValue read packet next literal prior present event)) =
    columnActionInnovation read next.1 (frame) (occurrence) value := by
  let source := columns read next.1 (frame) (occurrence)
  let response := columnRead read next.1 (relayedWordValue read packet next literal prior present event)
  have paid : response ∈ SourceGeneratedFiniteGram.Projection.sourceSpan source :=
    ⟨relayedWordCoordinates read packet next literal prior present event,
      relayed_word_synthesis read packet next literal prior present event⟩
  have vanishes : FG.innovationCLM source response = 0 := by
    rw [SourceGeneratedFiniteGram.Projection.innovation_value,
      SourceGeneratedFiniteGram.Projection.predictable_readback,
      Submodule.starProjection_eq_self_iff.mpr paid, sub_self]
  change columnActionInnovation read next.1 (frame) (occurrence) (value+response) =
    columnActionInnovation read next.1 (frame) (occurrence) value
  rw [← actual_innovation_from_column_actions read next.1 (frame) (occurrence) (value+response),
    ← actual_innovation_from_column_actions read next.1 (frame) (occurrence) value]
  change FG.innovationCLM source (value+response) = FG.innovationCLM source value
  rw [map_add, vanishes, add_zero]

end PaidSourceContentEnvironment.GradedInnovation.Integrated
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
