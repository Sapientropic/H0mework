import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.DelayedFinancing
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting.Visit

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.DelayedFinancing.Cash
open ResponsibilityLifecycle Source.Program Source.ProgrammeControl
open LivingLawEvolution ConstructiveRoot
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

structure Issued where
  private mk ::
  record : InstructionRecord sources
  claim : IssuedClaim (sources record.origin.1)
  exactOrigin : claim.origin = record.origin.2
  emitted : record.result = .issued claim exactOrigin

def readIssue (record : InstructionRecord sources) : Option (Issued sources) :=
  match actual : record.result with
  | .issued claim exactOrigin => some ⟨record,claim,exactOrigin,actual⟩
  | _ => none

theorem readIssue_preserves_record (record : InstructionRecord sources) (issue : Issued sources)
    (generated : readIssue sources record = some issue) : issue.record = record := by
  unfold readIssue at generated
  split at generated
  · cases Option.some.inj generated; rfl
  · cases generated

namespace Issued
variable {sources} (issue : Issued sources)
def slot := issue.record.before.current.slots.length
def original : Claim sources := ⟨issue.record.origin.1,issue.claim⟩
def admitted := (NativeResponsibilityProcess.Edge.admit (P := process sources) issue.original :
  (process sources).Edge issue.record.before.current).lifecycleEvent
end Issued

variable (originals : List (Origin sources)) (state : (process sources).GeneratedState)

theorem trace_origins : (instructionTrace sources originals state).map InstructionRecord.origin = originals := by
  induction originals generalizing state with
  | nil => rfl
  | cons origin rest ih => simpa only [instructionTrace,List.map_cons] using congrArg (List.cons origin) (ih _)

theorem trace_events :
    (instructionTrace sources originals state).flatMap (fun record => (record.result.transition sources).events) =
      (consumeOrigins_run sources originals state).events := by
  induction originals generalizing state with
  | nil => rfl
  | cons origin rest ih =>
      let result := consume sources origin state
      change (result.transition sources).events ++
          (instructionTrace sources rest (result.next sources)).flatMap (fun record => (record.result.transition sources).events) =
        ((result.transition sources).concatRuns (process sources) (consumeOrigins_run sources rest (result.next sources))).events
      rw [NativeResponsibilityProcess.Run.events_concatRuns,ih]

theorem issued_event_is_actual (issue : Issued sources) (member : issue.record ∈ instructionTrace sources originals state) :
    issue.admitted ∈ (consumeOrigins_run sources originals state).events := by
  rw [← trace_events]
  refine List.mem_flatMap.mpr ⟨issue.record,member,?_⟩
  rw [issue.emitted]
  change issue.admitted ∈ [] ++ [issue.admitted]
  exact List.mem_singleton_self _

theorem issued_event_has_its_original_birth {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (issue : Issued sources) (actual : issue.admitted ∈ run.events) :
    ∃ birth ∈ Exposure.admissions sources run, birth.index = issue.slot ∧ birth.claim = issue.original := by
  have marked : (issue.slot,issue.original) ∈ run.events.filterMap (Exposure.admittedAddress sources) :=
    List.mem_filterMap.mpr ⟨issue.admitted,actual,rfl⟩
  rw [← Exposure.admissions_exact sources run] at marked
  obtain ⟨birth,member,same⟩ := List.mem_map.mp marked
  exact ⟨birth,member,congrArg Prod.fst same,congrArg Prod.snd same⟩

variable (receipt : Posting.VisitReceipt sources)
def trace := instructionTrace sources (visitOrigins sources receipt.sourceIndex receipt.ordinal) receipt.before
def entries := (trace sources receipt).filterMap (readIssue sources)

theorem entry_record_is_actual (issue : Issued sources) (member : issue ∈ entries sources receipt) :
    issue.record ∈ trace sources receipt := by
  obtain ⟨record,inside,generated⟩ := List.mem_filterMap.mp member
  rw [readIssue_preserves_record sources record issue generated]
  exact inside

omit [DecidableEq Port] in
private theorem inventory_visit (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (origin : InstructionOrigin input) (member : origin ∈ inventoryAt input visit) : origin.visit = visit := by
  cases emission : input.emission? with
  | none =>
      simp only [inventoryAt,emission,administrativeInventoryAt] at member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
      rfl
  | some emit =>
      simp only [inventoryAt,emission,List.mem_append] at member
      rcases member with administrative | traced
      · obtain ⟨index,rfl⟩ := List.mem_ofFn.mp administrative; rfl
      · obtain ⟨index,rfl⟩ := List.mem_ofFn.mp traced; rfl

theorem entry_has_the_same_source_window (issue : Issued sources) (member : issue ∈ entries sources receipt) :
    Exposure.windowOf sources issue.original = receipt.window sources := by
  have inTrace := entry_record_is_actual sources receipt issue member
  have inOrigins : issue.record.origin ∈ visitOrigins sources receipt.sourceIndex receipt.ordinal := by
    rw [← trace_origins sources (visitOrigins sources receipt.sourceIndex receipt.ordinal) receipt.before]
    exact List.mem_map.mpr ⟨issue.record,inTrace,rfl⟩
  obtain ⟨origin,inInventory,same⟩ := List.mem_map.mp inOrigins
  change (⟨issue.record.origin.1,issue.claim.origin.visit⟩ : Exposure.Window sources) = _
  rw [issue.exactOrigin,← same,inventory_visit _ _ origin inInventory]
  rfl

def keys (mask : Nat → Bool) (issue : Issued sources) : List Nat :=
  if mask issue.slot then (origins sources issue.original).map (fun origin => origin.access.access.val.index) else []

def positions (mask : Nat → Bool) := (entries sources receipt).flatMap (keys sources mask)
def markedBy (positions : List Nat) (index : Nat) : Bool := positions.any fun position => position == index
def selected (mask : Nat → Bool) (index : Nat) := markedBy (positions sources receipt mask) index

theorem selected_exact (mask : Nat → Bool) (index : Nat) :
    selected sources receipt mask index = true ↔
      ∃ issue ∈ entries sources receipt, mask issue.slot = true ∧
        ∃ origin ∈ origins sources issue.original, origin.access.access.val.index = index := by
  constructor
  · intro selected
    obtain ⟨position,member,same⟩ := List.any_eq_true.mp selected
    have same := beq_iff_eq.mp same
    subst position
    obtain ⟨issue,inside,hit⟩ := List.mem_flatMap.mp member
    unfold keys at hit
    split at hit
    · rename_i marked
      obtain ⟨origin,listed,equal⟩ := List.mem_map.mp hit
      exact ⟨issue,inside,marked,origin,listed,equal⟩
    · cases hit
  · rintro ⟨issue,inside,marked,origin,listed,same⟩
    apply List.any_eq_true.mpr
    refine ⟨index,List.mem_flatMap.mpr ⟨issue,inside,?_⟩,beq_iff_eq.mpr rfl⟩
    unfold keys
    rw [if_pos marked]
    exact List.mem_map.mpr ⟨origin,listed,same⟩

def rawItems := (sources receipt.sourceIndex).law.rawItems
  (ProgrammeSource.rawCurrent (sources receipt.sourceIndex) (receipt.window sources).2.current)
  (ProgrammeSource.rawEvent (sources receipt.sourceIndex) (receipt.window sources).2.current)

theorem original_advance_is_in_this_actual_receipt (issue : Issued sources) (member : issue ∈ entries sources receipt)
    (origin : Open sources issue.original) : origin.access.access.val ∈ rawItems sources receipt := by
  let atWindow (window : Exposure.Window sources) := (sources window.1).law.rawItems
    (ProgrammeSource.rawCurrent (sources window.1) window.2.current) (ProgrammeSource.rawEvent (sources window.1) window.2.current)
  change origin.access.access.val ∈ atWindow (receipt.window sources)
  rw [← entry_has_the_same_source_window sources receipt issue member]
  exact origin.access.access.property

/-- The evidence is unioned before each actual cash instruction is folded once. -/
def cashBy (positions : List Nat) (selected credit : Bool) (party : Party) (good : Good) : ℚ :=
  ((rawItems sources receipt).map fun item =>
    if markedBy positions item.index = selected then
      if PublicFunction.Costs.isDebtPayment item.request then 0 else
        flowAt (if credit then (sources receipt.sourceIndex).law.actualCredit item.before item.request
          else (sources receipt.sourceIndex).law.actualDebit item.before item.request) party good
    else 0).sum

def cash (mask : Nat → Bool) := cashBy sources receipt (positions sources receipt mask)

theorem duplicate_explanations_do_not_duplicate_any_cash (positions : List Nat) (selected credit : Bool) (party : Party) (good : Good) :
    cashBy sources receipt (positions ++ positions) selected credit party good = cashBy sources receipt positions selected credit party good := by
  simp only [cashBy,markedBy,List.any_append,Bool.or_self]
  rfl

theorem cash_partition (mask : Nat → Bool) (credit : Bool) (party : Party) (good : Good) :
    cash sources receipt mask true credit party good + cash sources receipt mask false credit party good =
      ((rawItems sources receipt).map fun item => if PublicFunction.Costs.isDebtPayment item.request then 0 else
        flowAt (if credit then (sources receipt.sourceIndex).law.actualCredit item.before item.request
          else (sources receipt.sourceIndex).law.actualDebit item.before item.request) party good).sum := by
  unfold cash cashBy
  induction rawItems sources receipt with
  | nil => simp only [List.map_nil,List.sum_nil,add_zero]
  | cons item rest ih =>
      simp only [List.map_cons,List.sum_cons]
      cases markedBy (positions sources receipt mask) item.index <;>
        simp only [Bool.false_eq_true,Bool.true_eq_false,if_false,if_true] <;> linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.DelayedFinancing.Cash
