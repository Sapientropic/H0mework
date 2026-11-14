import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.RequestRelay.BirthAction

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation.Integrated.CP779Independent

open SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationExecution
open SourceOperationInquiry.Context.Installation (born_math_action_paid)
open SourceOperationInquiry.Context.Installation (executedEnvironmentIncrement)
open scoped InnerProductSpace

namespace SourceBirth
export ActualCofinalSourceAction
  (birthIncrement birth_registered_environment birth_decoded_environment birth_word_reads_written)
export ActualCofinalSourceAction.BirthReceipt (birth_request_read)
export ActualCofinalSourceAction.SourceReceiptOccurrence (ExecutionAt)
end SourceBirth

section AtPacket
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (packet next : RelayPacket (K := K) X)
variable (literal : next = Action.packetTransport packet.2.2.2.down (Action.sourceBorn (factory read) packet))

private structure InstalledItem where
  prior : SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) packet.1) (X := X) (s := .joint)
  present : packet.2.1.1.inventory = some prior
  event : Fin prior.trace.length
  item : Fin (Feed.eventItems ((prior.trace.map (Action.sourceLiftEvent packet)).get
    (Fin.cast (List.length_map _).symm event))).length

variable (carried : InstalledItem packet)

set_option cleanup.letToHave false in
private def paidMicroAt :=
  let frame := ActualCofinalSourceAction.selected (factory read) packet
  let configuration := (ActualCofinalSourceAction.nativePacket (factory read) packet).2.2.1
  And.intro (born_math_action_paid frame (ActualCofinalSourceAction.AS.stockCfg configuration))
    (BirthAction.first_birth_local_increment (factory read) packet)

set_option cleanup.letToHave false in
private def paidWordAt (word : Formal ℤ (L.Value (W K) packet.1) X .joint) :=
  And.intro (SourceBirth.birth_registered_environment (factory read) packet) <|
  And.intro (SourceBirth.birth_decoded_environment (factory read) packet)
    (SourceBirth.birth_word_reads_written (factory read) packet word)

omit [InnerProductSpace ℂ K] in
set_option cleanup.letToHave false in
private def paidReceipt {Y : J.Slot → Type u}
    (target : RelayPacket (K := K) Y) (execution : SourceBirth.ExecutionAt target) :=
  have typed : Nonempty (Trace execution.decoder execution.request.expression
    (.const (execution.request.expression.eval execution.decoder))) := ⟨execution.paid⟩
  have positions : ∀ i, (execution.step i).before.length = execution.segment.before.length + (1 + i.val) :=
    fun i => execution.step_position i
  And.intro execution.installed <| And.intro execution.decoder_source <| And.intro typed <|
  And.intro execution.segment.trace_eq <| And.intro execution.boundary_written positions

set_option cleanup.letToHave false in
private def paidExecutionAt :=
  let source := Action.sourceBorn (factory read) packet
  let execution := BirthAction.birthRequest (factory read) packet carried.prior carried.present carried.event carried.item
  let target := execution.reindex source next packet.2.2.2.down literal.symm
  And.intro (SourceBirth.birth_request_read (factory read) packet carried.prior carried.present carried.event carried.item) <|
  And.intro (execution.reindex_positions source next packet.2.2.2.down literal.symm)
    (paidReceipt next target)
end AtPacket

section Actual
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (sourceFrame : JointMeasured.Frame (K := K)) (ordinal : ℕ)

local notation "oldPacket" => site read sourceFrame ordinal
local notation "nextPacket" => site read sourceFrame (ordinal+1)
local notation "actualNext" => next_packet_is_actual read sourceFrame ordinal

set_option cleanup.letToHave false in
private def the_newborn_first_local_action_uses_the_registered_raw :=
  And.intro (paidMicroAt read oldPacket)
    (actual_first_born_local_increment read sourceFrame ordinal)

set_option cleanup.letToHave false in
private def the_prior_decoder_writes_the_birth_environment_and_whole_word
    (word : Formal ℤ (L.Value (W K) oldPacket.1) X .joint) :=
  paidWordAt read oldPacket word

set_option cleanup.letToHave false in
private def the_original_signed_request_has_its_typed_trace_and_installed_segment :=
  paidExecutionAt read oldPacket nextPacket actualNext

set_option cleanup.letToHave false in
private def the_literal_next_reads_the_same_signed_birth_and_whole :=
  And.intro (actual_birth_receipt_action read sourceFrame ordinal) <|
  And.intro (next_inventory_is_actual read sourceFrame ordinal) <|
  And.intro (next_pair_inventory_is_actual read sourceFrame ordinal) <|
  And.intro (next_stock_from_actual_born read sourceFrame ordinal) <|
  And.intro (completed_whole read sourceFrame ordinal)
    (completed_next read sourceFrame ordinal)
end Actual

private abbrev TestEnvironment := Env (fun _ : Unit => ℤ) (fun _ : Unit => Unit)
private def registeredOld : TestEnvironment := fun _ _ => 3
private def writtenDecoder : TestEnvironment := fun _ _ => 8
private def nativeVariable : Expr (fun _ : Unit => ℤ) (fun _ : Unit => Unit) () := .var ()

private theorem a_zero_local_delta_cannot_replace_a_legal_decoder_write :
    let signed := (-2 : ℤ)
    let written := signed • (liftExpr nativeVariable).eval (pairEnvironment registeredOld (writtenDecoder-registeredOld))
    let retained := signed • (liftExpr nativeVariable).eval (pairEnvironment registeredOld (0 : TestEnvironment))
    written = (-6,-10) ∧ retained = (-6,0) ∧ written ≠ retained ∧
      signed • nativeVariable.eval writtenDecoder = written.1 + written.2 := by
  change (-2 : ℤ) • ((3 : ℤ),(8-3 : ℤ)) = (-6,-10) ∧
    (-2 : ℤ) • ((3 : ℤ),(0 : ℤ)) = (-6,0) ∧
    (-2 : ℤ) • ((3 : ℤ),(8-3 : ℤ)) ≠ (-2 : ℤ) • ((3 : ℤ),(0 : ℤ)) ∧
    (-2 : ℤ) • (8 : ℤ) = ((-2 : ℤ) • ((3 : ℤ),(8-3 : ℤ))).1 + ((-2 : ℤ) • ((3 : ℤ),(8-3 : ℤ))).2
  exact ⟨by decide,by decide,by decide,by decide⟩

run_cmd do
  IO.println "CP779_CONTROL + the_newborn_first_local_action_uses_the_registered_raw\nCP779_CONTROL + the_prior_decoder_writes_the_birth_environment_and_whole_word\nCP779_CONTROL + the_original_signed_request_has_its_typed_trace_and_installed_segment\nCP779_CONTROL + the_literal_next_reads_the_same_signed_birth_and_whole\nCP779_CONTROL - a_zero_local_delta_cannot_replace_a_legal_decoder_write\nCP779_GATE_PASS positive=4 negative=1"

end PaidSourceContentEnvironment.GradedInnovation.Integrated.CP779Independent
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
