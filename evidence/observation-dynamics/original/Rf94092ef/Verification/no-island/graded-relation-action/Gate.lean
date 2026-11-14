import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.RequestRelay.WordAction.Born

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation.Integrated.CP778Independent

open SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceInventoryExecutionFeed.AdmissionReceipt (formalItems formal_source_items)
open SourceGeneratedFiniteGram (Coordinates)
open SourceOperationInquiry.Context.Installation (executedEnvironmentIncrement)
open scoped InnerProductSpace

section AtPacket
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (packet next : RelayPacket (K := K) X)
variable (literal : next = Action.packetTransport packet.2.2.2.down (Action.sourceBorn (factory read) packet))

private structure InstalledItem where
  prior : SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) packet.1) (X := X) (s := .joint)
  present : packet.2.1.1.inventory = some prior
  event : Fin prior.trace.length
  item : Fin (Feed.eventItems (relayedEvent read packet next literal prior present event)).length

variable (carried : InstalledItem read packet next literal)

set_option cleanup.letToHave false in
private def paidWordAt :=
  let index := relayedRequest read packet next literal carried.prior carried.present carried.event carried.item
  have available : Nonempty (Index (K := K) next.1 (A.epoch next.2.1.1)) := ⟨index⟩
  And.intro available <|
  And.intro (relayed_event_lift read packet next literal carried.prior carried.present carried.event) <|
  And.intro (relayed_request_read read packet next literal carried.prior carried.present carried.event carried.item) <|
  And.intro (relayed_column_action read packet next literal carried.prior carried.present carried.event carried.item)
    (relayed_word_value read packet next literal carried.prior carried.present carried.event)

set_option cleanup.letToHave false in
private def paidSynthesisAt :=
  And.intro (relayed_word_synthesis read packet next literal carried.prior carried.present carried.event)
    (relayed_word_action_equation read packet next literal carried.prior carried.present carried.event)

set_option cleanup.letToHave false in
private def paidFibreAt (value : K) :=
  let frame := A.epoch next.2.1.1
  let occurrence := S.actualOccurrence next.2.1.1
  let response := columnRead read next.1
    (relayedWordValue read packet next literal carried.prior carried.present carried.event)
  let vector := relayedWordCoordinates read packet next literal carried.prior carried.present carried.event
  let matrix := columnActionGram read next.1 frame occurrence
  let rhs := columnActionRhs read next.1 frame occurrence
  have rhsAdd : rhs (value+response) = rhs value+rhs response := by
    dsimp only [rhs]
    simp only [← actual_gram_rhs_from_column_actions]
    ext i
    exact inner_add_right _ _ _
  have translated (a : Coordinates (Index next.1 frame)) :
      SourceGeneratedFiniteGram.action matrix (a+vector) = rhs (value+response) ↔
      SourceGeneratedFiniteGram.action matrix a = rhs value := by
    have bill : SourceGeneratedFiniteGram.action matrix vector = rhs response :=
      relayed_word_action_equation read packet next literal carried.prior carried.present carried.event
    rw [map_add, rhsAdd, bill]
    exact ⟨add_right_cancel, fun same => congrArg (· + rhs response) same⟩
  have fullFibre (a : Coordinates (Index next.1 frame)) :=
    (translated a).trans (actual_column_action_fibre read next.1 frame occurrence value a)
  And.intro fullFibre <|
  And.intro (relayed_word_coefficient_change read packet next literal carried.prior carried.present carried.event value)
    (relayed_word_innovation read packet next literal carried.prior carried.present carried.event value)
end AtPacket

section Actual
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (sourceFrame : JointMeasured.Frame (K := K)) (ordinal : ℕ)

local notation "oldPacket" => site read sourceFrame ordinal
local notation "nextPacket" => site read sourceFrame (ordinal+1)
local notation "actualNext" => next_packet_is_actual read sourceFrame ordinal

private abbrev InstalledItemAt := InstalledItem read oldPacket nextPacket actualNext
variable (carried : InstalledItemAt read sourceFrame ordinal)

set_option cleanup.letToHave false in
private def the_lifted_word_uses_the_actual_signed_addresses_and_both_raw_legs :=
  paidWordAt read oldPacket nextPacket actualNext carried

set_option cleanup.letToHave false in
private def the_same_word_generates_the_actual_Gram_rhs :=
  paidSynthesisAt read oldPacket nextPacket actualNext carried

set_option cleanup.letToHave false in
private def all_coefficients_translate_in_the_original_fibre (value : K) :=
  paidFibreAt read oldPacket nextPacket actualNext carried value

set_option cleanup.letToHave false in
private def the_literal_second_born_consumes_the_word_and_keeps_whole_and_next :=
  And.intro (actual_born_consumes_relayed_word read sourceFrame ordinal carried.prior carried.present carried.event) <|
  And.intro (next_joint_is_actual read sourceFrame (ordinal+1)) <|
  And.intro (next_inventory_is_actual read sourceFrame (ordinal+1)) <|
  And.intro (next_pair_inventory_is_actual read sourceFrame (ordinal+1)) <|
  And.intro (completed_whole read sourceFrame (ordinal+1))
    (completed_next read sourceFrame (ordinal+1))
end Actual

private abbrev IntegerExpr := Expr (fun _ : Unit => ℤ) (fun _ : Unit => Unit) ()
private def negativeWord : Formal ℤ (fun _ : Unit => ℤ) (fun _ : Unit => Unit) () :=
  Finsupp.single (.var ()) (-1)

private def oldValue : Env (fun _ : Unit => ℤ) (fun _ : Unit => Unit) := fun _ _ => 1
private def signedDelta : Env (fun _ : Unit => ℤ) (fun _ : Unit => Unit) := fun _ _ => -1
private def negativeEvent : SourceInventoryExecutionFeed.Event
    (V := fun _ : Unit => ℤ) (X := fun _ : Unit => Unit) (s := ()) := .relation negativeWord

private theorem the_signed_word_has_a_nonzero_pair_even_when_its_total_is_zero :
    let paid := updateInventory (R := ℤ) oldValue signedDelta (formalItems (Feed.eventItems negativeEvent))
    paid = (-1, 1) ∧ paid ≠ 0 ∧ paid.1+paid.2 = 0 := by
  dsimp only
  have word : formalItems (Feed.eventItems negativeEvent) = negativeWord := formal_source_items negativeWord
  have paid : updateInventory (R := ℤ) oldValue signedDelta negativeWord = (-1, 1) := by
    simp [negativeWord, updateInventory, evaluation, effectEvaluator, Expr.eval, Expr.effect, oldValue, signedDelta]
  rw [word, paid]
  exact ⟨rfl, by decide, by decide⟩

run_cmd do
  IO.println "CP778_CONTROL + the_lifted_word_uses_the_actual_signed_addresses_and_both_raw_legs\nCP778_CONTROL + the_same_word_generates_the_actual_Gram_rhs\nCP778_CONTROL + all_coefficients_translate_in_the_original_fibre\nCP778_CONTROL + the_literal_second_born_consumes_the_word_and_keeps_whole_and_next\nCP778_CONTROL - the_signed_word_has_a_nonzero_pair_even_when_its_total_is_zero\nCP778_GATE_PASS positive=4 negative=1"

end PaidSourceContentEnvironment.GradedInnovation.Integrated.CP778Independent
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
