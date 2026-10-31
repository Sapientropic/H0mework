import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Cuts
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Prefix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.InventoryExact

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def issuedClaim? (origin : InstructionOrigin input) : Option (IssuedClaim input) :=
  match readIssue input origin with
  | .issued claim _ => some claim
  | _ => none

def issuedClaims (origins : List (InstructionOrigin input)) := origins.filterMap (issuedClaim? input)

theorem consume_claims (origin : InstructionOrigin input) (state : (process input).GeneratedState) :
    ((consume input origin state).next input).current.slots.map (slotClaim input) =
      state.current.slots.map (slotClaim input) ++ (issuedClaim? input origin).toList := by
  unfold consume issuedClaim?
  cases readIssue input origin with
  | issued claim exactOrigin =>
      change (state.current.slots ++ [ObligationSlot.live (admission input claim).toObligation]).map _ = _
      simp only [List.map_append, List.map_cons, List.map_nil, slotClaim, slotObligation,
        Option.toList_some]
      rfl
  | nonfinancial =>
      cases readMovement input origin with
      | none => simp only [InstructionResult.next, Option.toList_none, List.append_nil]
      | some movement =>
          simpa only [InstructionResult.next, Option.toList_none, List.append_nil] using
            (allocate input origin state movement.quantity (movement.quantity_nonnegative input)).original_claims
  | rejected instruction original refused => simp only [InstructionResult.next, Option.toList_none, List.append_nil]
  | missingBirth party notBorn => simp only [InstructionResult.next, Option.toList_none, List.append_nil]

theorem consumeOrigins_claims (origins : List (InstructionOrigin input)) (state : (process input).GeneratedState) :
    (consumeOrigins input origins state).current.slots.map (slotClaim input) =
      state.current.slots.map (slotClaim input) ++ issuedClaims input origins := by
  induction origins generalizing state with
  | nil => simp only [consumeOrigins, issuedClaims, List.filterMap_nil, List.append_nil]
  | cons origin tail ih =>
      rw [consumeOrigins, ih, consume_claims]
      simp only [issuedClaims, List.filterMap_cons]
      cases issuedClaim? input origin <;> simp only [Option.toList_none, Option.toList_some,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

def issuedBefore : Nat → List (IssuedClaim input)
  | 0 => []
  | visit + 1 => issuedBefore visit ++ issuedClaims input
      (inventoryAt input (ProgrammeHistory.visitAt input visit))

theorem account_claims_are_exactly_the_source_issues (visit : Nat) :
    (accountAt input visit).current.slots.map (slotClaim input) = issuedBefore input visit := by
  induction visit with
  | zero => rfl
  | succ visit ih => rw [accountAt_successor, consumeOrigins_claims, ih]; rfl

theorem consumeOrigins_append (first second : List (InstructionOrigin input))
    (state : (process input).GeneratedState) :
    consumeOrigins input (first ++ second) state =
      consumeOrigins input second (consumeOrigins input first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons origin tail ih => exact ih _

namespace IssueTrace

abbrev inventory (visit : Nat) := inventoryAt input (ProgrammeHistory.visitAt input visit)
abbrev origin (visit : Nat) (index : Fin (inventory input visit).length) :=
  (inventory input visit).get index

def before (visit : Nat) (index : Fin (inventory input visit).length) :=
  consumeOrigins input ((inventory input visit).take index.val) (accountAt input visit)

def after (visit : Nat) (index : Fin (inventory input visit).length) :=
  (consume input (origin input visit index) (before input visit index)).next input

theorem before_claims (initialZero : input.initial.claims = fun _ _ _ => 0)
    (visit : Nat) (index : Fin (inventory input visit).length)
    (instruction : Source.Program.ExecutionItem Party Good Port Technology Instrument)
    (decoded : (origin input visit index).instruction? input = some instruction) :
    BalanceConservation.ledgerClaims input (before input visit index).current = instruction.before.claims := by
  exact BalanceConservation.prefix_claims_before_original input (inventory input visit)
    (accountAt input visit) (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input visit).current)
    0 (ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input visit).current)
    (inventoryAt_instructions_exact input _) (BalanceConservation.generated_prefix_claims input initialZero visit)
    index.val (origin input visit index) instruction
    (by simp only [origin, List.get_eq_getElem, List.getElem?_eq_getElem index.isLt]) decoded

def arrival (visit : Nat) (index : Fin (inventory input visit).length) :
    (process input).Run (accountAt input visit).current (before input visit index).current :=
  consumeOrigins_run input _ _

private theorem account_after (visit : Nat) (index : Fin (inventory input visit).length) :
    accountAt input (visit + 1) =
      consumeOrigins input ((inventory input visit).drop (index.val + 1)) (after input visit index) := by
  rw [accountAt_successor]
  change consumeOrigins input (inventory input visit) _ = _
  conv_lhs => rw [← List.take_append_drop index.val (inventory input visit),
    List.drop_eq_getElem_cons index.isLt]
  rw [consumeOrigins_append]
  rfl

def departure (visit : Nat) (index : Fin (inventory input visit).length) (later : Nat) :
    (process input).Run (after input visit index).current (accountAt input (visit + 1 + later)).current := by
  have suffix := consumeOrigins_run input ((inventory input visit).drop (index.val + 1)) (after input visit index)
  rw [← account_after] at suffix
  exact suffix.concatRuns (process input) (BalanceConservation.fromActualCut input (visit + 1) later)

omit [DecidableEq Port] in
private theorem preserve_slot {first second : List (IssuedClaim input)} (keeps : first <+: second)
    (slot : Nat) (claim : IssuedClaim input) (present : first[slot]? = some claim) :
    second[slot]? = some claim := by
  obtain ⟨tail, rfl⟩ := keeps
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).choose]
  exact present

structure IssuedSlot (visit : Nat) (index : Fin (inventory input visit).length)
    (claim : IssuedClaim input) : Type where
  private mk ::
  arrival : (process input).Run (accountAt input visit).current (before input visit index).current
  birth : (process input).Run (before input visit index).current (after input visit index).current
  continuation : ∀ later, (process input).Run (after input visit index).current
    (accountAt input (visit + 1 + later)).current
  exact_origin : claim.origin = origin input visit index
  emitted : readIssue input (origin input visit index) = .issued claim exact_origin
  native_admission : (after input visit index).current.slots[(before input visit index).current.slots.length]? =
    some (.live (admission input claim).toObligation)
  retained : ∀ later,
    ((accountAt input (visit + 1 + later)).current.slots.map (slotClaim input))[(before input visit index).current.slots.length]? = some claim

def generate (visit : Nat) (index : Fin (inventory input visit).length) (claim : IssuedClaim input)
    (exactOrigin : claim.origin = origin input visit index)
    (emitted : readIssue input (origin input visit index) = .issued claim exactOrigin) :
    IssuedSlot input visit index claim := by
  have admitted := issued_appends_actual_original_debt input (origin input visit index)
    (before input visit index) claim exactOrigin emitted
  change (after input visit index).current.slots[(before input visit index).current.slots.length]? = _ at admitted
  refine ⟨arrival input visit index, (consume input _ _).transition input, departure input visit index,
    exactOrigin, emitted, admitted, ?_⟩
  intro later
  have present : ((after input visit index).current.slots.map (slotClaim input))[(before input visit index).current.slots.length]? = some claim := by
    rw [List.getElem?_map, admitted]
    rfl
  have tailKeeps : (after input visit index).current.slots.map (slotClaim input) <+:
      (accountAt input (visit + 1)).current.slots.map (slotClaim input) := by
    rw [account_after]
    exact consumeOrigins_preserves_original_claims input _ _
  have keeps := tailKeeps.trans (BalanceConservation.cut_preserves_all_original_claims input (visit + 1) later)
  exact preserve_slot input keeps _ claim present

def traceIndex (visit : Nat)
    (emit : Source.Program.RawCurrent Party Good Technology Instrument →
      Source.Program.RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit)
    (index : Fin (Source.ProgrammeFace.Registered.traceItems input
      (ProgrammeHistory.visitAt input visit).current).length) : Fin (inventory input visit).length :=
  ⟨(administrativeInventoryAt input (ProgrammeHistory.visitAt input visit)).length + index.val, by
    simpa only [inventory, inventoryAt, generated, List.length_append, traceInventoryAt,
      List.length_ofFn, Nat.add_lt_add_iff_left] using index.isLt⟩

omit [DecidableEq Port] in
theorem traceIndex_origin (visit : Nat)
    (emit : Source.Program.RawCurrent Party Good Technology Instrument →
      Source.Program.RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit)
    (index : Fin (Source.ProgrammeFace.Registered.traceItems input
      (ProgrammeHistory.visitAt input visit).current).length) :
    origin input visit (traceIndex input visit emit generated index) =
      traceOriginAt input (ProgrammeHistory.visitAt input visit) index := by
  simp only [origin, inventory, inventoryAt, generated, List.get_eq_getElem, traceIndex]
  rw [List.getElem_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left, traceInventoryAt, List.getElem_ofFn]

end IssueTrace
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
