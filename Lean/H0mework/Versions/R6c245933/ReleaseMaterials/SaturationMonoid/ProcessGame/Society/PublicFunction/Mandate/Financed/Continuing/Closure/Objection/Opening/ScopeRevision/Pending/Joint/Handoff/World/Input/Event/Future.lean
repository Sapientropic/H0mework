import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Iteration
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Standing

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def ownActual := OutstandingSource.History.actualExecution epoch.source inventory.inputs (inventory.inputs.length + 1)
def ownWord := (ownActual inventory).submitted

theorem own_event_starts_at_the_saved_current :
    (ownActual inventory).before = current epoch inventory.inputs := rfl

theorem own_word_is_generated_by_the_actual_residual :
    ownWord inventory = (epoch.source.decideAt (current epoch inventory.inputs)
      (OutstandingSource.History.trailAt epoch.source inventory.inputs (inventory.inputs.length+2)).frame.payments).word :=
  OutstandingSource.History.residual_is_actually_emitted epoch.source inventory.inputs inventory.inputs.length (le_refl _)

theorem submitting_the_own_event_preserves_its_actual_after :
    (World.actual inventory (ownWord inventory)).after = (ownActual inventory).after := by
  rw [(World.actual inventory (ownWord inventory)).after_exact,(ownActual inventory).after_exact]
  change (Mandate.law base epoch.scope).next (World.actual inventory (ownWord inventory)).before
    (World.actual inventory (ownWord inventory)).submitted =
    (Mandate.law base epoch.scope).next (ownActual inventory).before (ownActual inventory).submitted
  rw [(World.actual_word_and_cut inventory (ownWord inventory)).1,
    (World.actual_word_and_cut inventory (ownWord inventory)).2,own_event_starts_at_the_saved_current]
  rfl

variable {inventory}

theorem standing_transport {first last : Packet} (path : Evolution first last)
    (actor : Bool) (standing : actor ∈ Delegation.members first.1.scope.task) :
    actor ∈ Delegation.members last.1.scope.task := by
  induction path with
  | same packet => exact standing
  | submit inventory word => exact standing
  | handoff inventory fresh =>
    exact Handoff.actual_handoff_retains_every_task_member fresh actor standing
  | handoffAt inventory fresh actualInputs =>
    exact Handoff.actual_handoff_retains_every_task_member fresh actor standing
  | append earlier later ihFirst ihLast => exact ihLast (ihFirst standing)

structure Opened {initial : Inventory epoch} {execution : Programme.Execution initial}
    (next : Programme.Completion.PaidNext execution) where
  private mk ::
  four : Handoff.PaidOpening next.fresh (Handoff.actual next.fresh 1).before (Handoff.actual next.fresh 1).submitted
  standing : Handoff.BothMembers next.fresh.scope
  homology : ∀ index : epoch.source.Slot,
    (Handoff.source next.fresh).seed.slot (Handoff.homologous next.fresh index) = epoch.source.seed.slot index
  service : ∀ index : epoch.source.Slot,
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (Handoff.law next.fresh)
      (Handoff.actual next.fresh 1).before (Handoff.actual next.fresh 1).submitted
      (epoch.source.seed.slot index).bearer (epoch.source.seed.slot index).goods (epoch.source.seed.slot index).purpose
  healthy : ExitCapacity.Nonnegative (current next.packet.1 next.packet.2.inputs)
  exitMaterial : ExitCapacity.Envelope (current next.packet.1 next.packet.2.inputs)
  ownInitial : (Handoff.I next.fresh).initial = current epoch execution.finalInventory.inputs

def opened {initial : Inventory epoch} {execution : Programme.Execution initial}
    (next : Programme.Completion.PaidNext execution) : Opened next :=
  ⟨next.opening,Handoff.paid_origin_generates_both_task_members next.fresh _ next.payment,
    fun index => Handoff.original_slot_content_is_preserved next.fresh index,
    next.all_original_service_slots_are_paid,
    (Handoff.selected_actual_service_and_response_preserve_exit_material next.fresh next.payment next.selected).1,
    (Handoff.selected_actual_service_and_response_preserve_exit_material next.fresh next.payment next.selected).2,
    next.initial_is_the_actual_complete_after⟩

inductive Openness {initial : Inventory epoch} {execution : Programme.Execution initial}
    (decision : Programme.Completion.Decision execution) where
  | private paid (next : Programme.Completion.PaidNext execution)
      (kind : decision.kind = .paid) (packet : decision.packet = next.packet) (facts : Opened next)
  | private reviewBlocked (kind : decision.kind = .reviewBlocked)
      (absent : Handoff.choose epoch.bound execution.finalInventory.inputs = none)
      (reason : Handoff.Blocked epoch.bound execution.finalInventory.inputs)
      (packet : decision.packet = ⟨epoch,execution.finalInventory⟩)
  | private replacementBlocked (kind : decision.kind = .replacementBlocked)
      (fresh : Handoff.Ready epoch.bound execution.finalInventory.inputs)
      (chosen : Handoff.choose epoch.bound execution.finalInventory.inputs = some fresh)
      (absent : Handoff.select fresh (Handoff.start fresh) = none)
      (actual : Handoff.Failure fresh (Handoff.actual fresh 1).before (Handoff.actual fresh 1).submitted)
      (methods : ∀ method ∈ Handoff.methods, Handoff.Failure fresh (Handoff.start fresh) (Handoff.candidate fresh (Handoff.start fresh) method))
      (packet : decision.packet = ⟨Epoch.ofFresh fresh,World.handoff execution.finalInventory fresh⟩)

def opening {initial : Inventory epoch} {execution : Programme.Execution initial}
    (decision : Programme.Completion.Decision execution) : Openness decision := by
  cases decision
  next next => exact .paid next rfl rfl (opened next)
  next absent reason => exact .reviewBlocked rfl absent reason rfl
  next fresh chosen absent actual methods => exact .replacementBlocked rfl fresh chosen absent actual methods rfl

structure Result (inventory : Inventory epoch) (word : List Action) where
  private mk ::
  event : Event.Disposition inventory word
  event_exact : event = Runtime.fromRoot inventory word
  openness : Openness event.original.original.decision

def produce (inventory : Inventory epoch) (word : List Action) : Result inventory word :=
  let actual := Runtime.fromRoot inventory word
  ⟨actual,rfl,opening actual.original.original.decision⟩

def Result.packet {word : List Action} (result : Result inventory word) := result.event.packet

def Result.nextSourceEvent {word : List Action} (result : Result inventory word) := ownActual result.packet.2

theorem Result.blocking_keeps_a_consumable_source_event {word : List Action} (result : Result inventory word)
    (_blocked : result.event.original.original.decision.kind ≠ .paid) :
    (result.nextSourceEvent).before = current result.packet.1 result.packet.2.inputs ∧
    (World.actual result.packet.2 (ownWord result.packet.2)).after = result.nextSourceEvent.after :=
  ⟨own_event_starts_at_the_saved_current _,submitting_the_own_event_preserves_its_actual_after _⟩

def Openness.kind {initial : Inventory epoch} {execution : Programme.Execution initial}
    {decision : Programme.Completion.Decision execution} : Openness decision → World.ContinuationKind
  | .paid .. => .paid
  | .reviewBlocked .. => .reviewBlocked
  | .replacementBlocked .. => .replacementBlocked

theorem Openness.classifies_the_actual_decision {initial : Inventory epoch} {execution : Programme.Execution initial}
    {decision : Programme.Completion.Decision execution} (outlook : Openness decision) : outlook.kind = decision.kind := by
  cases outlook
  next next kind packet facts => exact kind.symm
  next kind absent reason packet => exact kind.symm
  next kind fresh chosen absent actual methods packet => exact kind.symm

theorem Opened.every_actual_holder_has_a_paid_exit {initial : Inventory epoch} {execution : Programme.Execution initial}
    {next : Programme.Completion.PaidNext execution} (facts : Opened next) (actor : Bool)
    (holder : (current next.packet.1 next.packet.2.inputs).technology.holder = some actor) :
    (Input.choose next.packet.1 .exit (current next.packet.1 next.packet.2.inputs)).isSome = true :=
  ExitCapacity.source_material_envelope_generates_a_real_exit _ _ actor holder (facts.healthy actor .service) facts.exitMaterial


inductive FinitePublicContinuationClosure : Packet → Nat → Type where
  | private observed (packet : Packet) : FinitePublicContinuationClosure packet 0
  | private advanced (packet : Packet) {depth : Nat}
      (actual : Result packet.2 (ownWord packet.2)) (exact : actual = produce packet.2 (ownWord packet.2))
      (tail : FinitePublicContinuationClosure actual.packet depth) : FinitePublicContinuationClosure packet (depth+1)

def generate (packet : Packet) : (depth : Nat) → FinitePublicContinuationClosure packet depth
  | 0 => .observed packet
  | depth+1 =>
      let actual := produce packet.2 (ownWord packet.2)
      .advanced packet actual rfl (generate actual.packet depth)

def FinitePublicContinuationClosure.packet {initial : Packet} {depth : Nat} :
    FinitePublicContinuationClosure initial depth → Packet
  | .observed packet => packet
  | .advanced _ _ _ tail => tail.packet

def FinitePublicContinuationClosure.native {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) : Evolution initial chain.packet := by
  induction chain
  next packet => exact .same _
  next packet depth actual exact tail path => exact .append actual.event.native path

def FinitePublicContinuationClosure.finance {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) :
    (Financial.Family.process sources).Run initial.2.finance.current chain.packet.2.finance.current := by
  induction chain
  next packet => exact .nil
  next packet depth actual exact tail path => exact actual.event.finance.concatRuns _ path

abbrev Visit := Sigma fun packet : Packet => Result packet.2 (ownWord packet.2)

def FinitePublicContinuationClosure.visits {initial : Packet} {depth : Nat} :
    FinitePublicContinuationClosure initial depth → List Visit
  | .observed _ => []
  | .advanced packet actual _ tail => ⟨packet,actual⟩ :: tail.visits

theorem FinitePublicContinuationClosure.exact_observation_depth {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) : chain.visits.length = depth := by
  induction chain
  next packet => rfl
  next packet depth actual exact tail ih => exact congrArg Nat.succ ih

def FinitePublicContinuationClosure.visit {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) : Fin depth → Visit := by
  induction chain
  next packet => exact Fin.elim0
  next packet depth actual exact tail ih => exact Fin.cases ⟨packet,actual⟩ ih
theorem FinitePublicContinuationClosure.every_visit_is_generated {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) (index : Fin depth) :
    (chain.visit index).2 = produce (chain.visit index).1.2 (ownWord (chain.visit index).1.2) := by
  induction chain
  next packet => exact Fin.elim0 index
  next packet depth actual same tail ih =>
    refine Fin.cases ?_ (fun later => ?_) index
    · exact same
    · exact ih later


def FinitePublicContinuationClosure.beforeVisit {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) (index : Fin depth) :
    Evolution initial (chain.visit index).1 := by
  induction chain
  next packet => exact Fin.elim0 index
  next packet depth actual exact tail ih =>
    refine Fin.cases ?_ (fun later => ?_) index
    · exact .same _
    · exact .append actual.event.native (ih later)

def FinitePublicContinuationClosure.afterVisit {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) (index : Fin depth) :
    Evolution (chain.visit index).2.packet chain.packet := by
  induction chain
  next packet => exact Fin.elim0 index
  next packet depth actual exact tail ih =>
    refine Fin.cases ?_ (fun later => ?_) index
    · exact tail.native
    · exact ih later

theorem FinitePublicContinuationClosure.standing {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) (actor : Bool)
    (member : actor ∈ Delegation.members initial.1.scope.task) :
    actor ∈ Delegation.members chain.packet.1.scope.task := standing_transport chain.native actor member


def reopen {initial : Packet} {depth : Nat} (chain : FinitePublicContinuationClosure initial depth)
    (word : List Action) (laterDepth : Nat) :=
  generate (produce chain.packet.2 word).packet laterDepth

def reopenNative {initial : Packet} {depth : Nat} (chain : FinitePublicContinuationClosure initial depth)
    (word : List Action) (laterDepth : Nat) : Evolution initial (reopen chain word laterDepth).packet :=
  .append chain.native (.append (produce chain.packet.2 word).event.native (reopen chain word laterDepth).native)

def reopenFinance {initial : Packet} {depth : Nat} (chain : FinitePublicContinuationClosure initial depth)
    (word : List Action) (laterDepth : Nat) :
    (Financial.Family.process sources).Run initial.2.finance.current (reopen chain word laterDepth).packet.2.finance.current :=
  chain.finance.concatRuns _ ((produce chain.packet.2 word).event.finance.concatRuns _ (reopen chain word laterDepth).finance)

/-- In particular a blocked response is the next generator's input, with no terminal coercion. -/
def Result.continue {word : List Action} (result : Result inventory word) (depth : Nat) := generate result.packet depth

def Result.continueNative {word : List Action} (result : Result inventory word) (depth : Nat) :
    Evolution ⟨epoch,inventory⟩ (result.continue depth).packet :=
  .append result.event.native (result.continue depth).native

def Result.continueFinance {word : List Action} (result : Result inventory word) (depth : Nat) :
    (Financial.Family.process sources).Run inventory.finance.current (result.continue depth).packet.2.finance.current :=
  result.event.finance.concatRuns _ (result.continue depth).finance

def FinitePublicContinuationClosure.beforeVisitFinance {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) (index : Fin depth) :
    (Financial.Family.process sources).Run initial.2.finance.current (chain.visit index).1.2.finance.current := by
  induction chain
  next packet => exact Fin.elim0 index
  next packet depth actual exact tail ih =>
    refine Fin.cases ?_ (fun later => ?_) index
    · exact .nil
    · exact actual.event.finance.concatRuns _ (ih later)

def FinitePublicContinuationClosure.afterVisitFinance {initial : Packet} {depth : Nat}
    (chain : FinitePublicContinuationClosure initial depth) (index : Fin depth) :
    (Financial.Family.process sources).Run (chain.visit index).2.packet.2.finance.current chain.packet.2.finance.current := by
  induction chain
  next packet => exact Fin.elim0 index
  next packet depth actual exact tail ih =>
    refine Fin.cases ?_ (fun later => ?_) index
    · exact tail.finance
    · exact ih later

/-- An observed external prefix feeds the same generator, including its newborn rows. -/
def afterEvents (inventory : Inventory epoch) (history : List (List Action)) (depth : Nat) :=
  generate (Iteration.after inventory history) depth

structure Response (inventory : Inventory epoch) (word : List Action) (depth : Nat) where
  private mk ::
  result : Result inventory word
  result_exact : result = produce inventory word
  continuation : FinitePublicContinuationClosure result.packet depth
  continuation_exact : continuation = generate result.packet depth

def respond (inventory : Inventory epoch) (word : List Action) (depth : Nat) : Response inventory word depth :=
  let actual := produce inventory word
  ⟨actual,rfl,generate actual.packet depth,rfl⟩

def autonomous (inventory : Inventory epoch) (depth : Nat) := respond inventory (ownWord inventory) depth

def Response.native {word : List Action} {depth : Nat} (answer : Response inventory word depth) :
    Evolution ⟨epoch,inventory⟩ answer.continuation.packet :=
  .append answer.result.event.native answer.continuation.native

def Response.finance {word : List Action} {depth : Nat} (answer : Response inventory word depth) :
    (Financial.Family.process sources).Run inventory.finance.current answer.continuation.packet.2.finance.current :=
  answer.result.event.finance.concatRuns _ answer.continuation.finance


end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future


namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future
universe v
variable {epoch : Epoch} {initial : Inventory epoch} {execution : Programme.Execution initial}

/-- The original openness witness is eliminated without reconstructing a decision. -/
def Openness.fold {decision : Programme.Completion.Decision execution}
    (motive : Openness decision → Sort v)
    (paid : (next : Programme.Completion.PaidNext execution) →
      (kind : decision.kind = .paid) → (packet : decision.packet = next.packet) →
      (facts : Opened next) → motive (.paid next kind packet facts))
    (reviewBlocked : (kind : decision.kind = .reviewBlocked) →
      (absent : Handoff.choose epoch.bound execution.finalInventory.inputs = none) →
      (reason : Handoff.Blocked epoch.bound execution.finalInventory.inputs) →
      (packet : decision.packet = ⟨epoch,execution.finalInventory⟩) →
      motive (.reviewBlocked kind absent reason packet))
    (replacementBlocked : (kind : decision.kind = .replacementBlocked) →
      (fresh : Handoff.Ready epoch.bound execution.finalInventory.inputs) →
      (chosen : Handoff.choose epoch.bound execution.finalInventory.inputs = some fresh) →
      (absent : Handoff.select fresh (Handoff.start fresh) = none) →
      (actual : Handoff.Failure fresh (Handoff.actual fresh 1).before (Handoff.actual fresh 1).submitted) →
      (methods : ∀ method ∈ Handoff.methods,
        Handoff.Failure fresh (Handoff.start fresh) (Handoff.candidate fresh (Handoff.start fresh) method)) →
      (packet : decision.packet = ⟨Epoch.ofFresh fresh,World.handoff execution.finalInventory fresh⟩) →
      motive (.replacementBlocked kind fresh chosen absent actual methods packet)) :
    (outlook : Openness decision) → motive outlook
  | .paid next kind packet facts => paid next kind packet facts
  | .reviewBlocked kind absent reason packet => reviewBlocked kind absent reason packet
  | .replacementBlocked kind fresh chosen absent actual methods packet =>
      replacementBlocked kind fresh chosen absent actual methods packet

namespace Native

def opening (decision : Programme.Completion.Decision execution) : Openness decision :=
  decision.fold (fun decision => Openness decision)
    (fun next => .paid next rfl rfl (opened next))
    (fun absent reason => .reviewBlocked rfl absent reason rfl)
    (fun fresh chosen absent actual methods => .replacementBlocked rfl fresh chosen absent actual methods rfl)

theorem opening_exact (decision : Programme.Completion.Decision execution) :
    opening decision = Future.opening decision := by
  cases decision <;> rfl

@[csimp] theorem opening_codegen : @Future.opening = @opening := by
  funext epoch initial execution decision
  exact (opening_exact decision).symm

def produce (inventory : Inventory epoch) (word : List Action) : Result inventory word :=
  let actual := Event.produce inventory word
  ⟨actual,rfl,opening actual.original.original.decision⟩

theorem produce_exact (inventory : Inventory epoch) (word : List Action) :
    produce inventory word = Future.produce inventory word := by
  simp only [produce,Future.produce,Event.Runtime.consumes_the_actual_incoming_event_and_response,opening_exact]

@[csimp] theorem produce_codegen : @Future.produce = @produce := by
  funext epoch inventory word
  exact (produce_exact inventory word).symm

end Native
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future
