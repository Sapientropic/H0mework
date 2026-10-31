import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Allocation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

inductive InstructionResult (origin : Origin sources) (before : (process sources).GeneratedState)
  | issued (claim : IssuedClaim (sources origin.1)) (exactOrigin : claim.origin = origin.2)
  | movement (source : Movement (sources origin.1) origin.2)
      (allocation : Allocation sources before source.quantity)
  | retained
  | refused (instruction : Source.Program.ExecutionItem Party Good Port Technology Instrument)
      (original : origin.2.instruction? (sources origin.1) = some instruction)
      (refused : ¬ (sources origin.1).law.Valid instruction.before instruction.request)
  | missingBirth (party : Party) (notBorn : party ∉ bornParties (sources origin.1))

def InstructionResult.next {origin : Origin sources} {before : (process sources).GeneratedState} :
    InstructionResult sources origin before → (process sources).GeneratedState
  | .issued claim _ => admit sources before ⟨origin.1, claim⟩
  | .movement _ allocation => allocation.after
  | .retained | .refused .. | .missingBirth .. => before

def InstructionResult.transition {origin : Origin sources} {before : (process sources).GeneratedState}
    (result : InstructionResult sources origin before) :
    (process sources).Run before.current (result.next sources).current := by
  cases result with
  | issued claim _ => exact .step .nil (.admit (P := process sources) ⟨origin.1, claim⟩)
  | movement _ allocation => exact allocation.transition
  | retained => exact .nil
  | refused _ _ _ => exact .nil
  | missingBirth _ _ => exact .nil

theorem InstructionResult.original_claims_retained {origin : Origin sources}
    {before : (process sources).GeneratedState} (result : InstructionResult sources origin before) :
    before.current.slots.map (slotClaim sources) <+:
      (result.next sources).current.slots.map (slotClaim sources) := by
  cases result with
  | issued claim exactOrigin =>
      change _ <+: (before.current.slots ++ _).map _
      rw [List.map_append]
      exact List.prefix_append _ _
  | movement _ allocation => rw [InstructionResult.next, allocation.original_claims]
  | retained => exact List.prefix_rfl
  | refused _ _ _ => exact List.prefix_rfl
  | missingBirth _ _ => exact List.prefix_rfl

def consume (origin : Origin sources) (before : (process sources).GeneratedState) :
    InstructionResult sources origin before :=
  match readIssue (sources origin.1) origin.2 with
  | .issued claim exactOrigin => .issued claim exactOrigin
  | .rejected instruction original refused => .refused instruction original refused
  | .missingBirth party notBorn => .missingBirth party notBorn
  | .nonfinancial =>
      match readMovement (sources origin.1) origin.2 with
      | some movement => .movement movement
          (allocate sources origin before movement.quantity (movement.quantity_nonnegative _))
      | none => .retained

structure InstructionRecord where
  private mk ::
  origin : Origin sources
  before : (process sources).GeneratedState
  result : InstructionResult sources origin before
  result_exact : result = consume sources origin before

def instructionTrace : List (Origin sources) → (process sources).GeneratedState → List (InstructionRecord sources)
  | [], _ => []
  | origin :: tail, before =>
      let result := consume sources origin before
      ⟨origin, before, result, rfl⟩ :: instructionTrace tail (result.next sources)

def InstructionResult.Unallocated {origin : Origin sources} {before : (process sources).GeneratedState} :
    InstructionResult sources origin before → Prop
  | .movement _ allocation => 0 < allocation.remaining
  | _ => False

def consumeOrigins : List (Origin sources) → (process sources).GeneratedState → (process sources).GeneratedState
  | [], state => state
  | origin :: tail, state => consumeOrigins tail ((consume sources origin state).next sources)

def consumeOrigins_run (origins : List (Origin sources)) (state : (process sources).GeneratedState) :
    (process sources).Run state.current (consumeOrigins sources origins state).current := by
  induction origins generalizing state with
  | nil => exact .nil
  | cons origin tail ih =>
      exact ((consume sources origin state).transition sources).concatRuns (process sources)
        (ih ((consume sources origin state).next sources))

theorem consumeOrigins_preserves_original_claims (origins : List (Origin sources))
    (state : (process sources).GeneratedState) :
    state.current.slots.map (slotClaim sources) <+:
      (consumeOrigins sources origins state).current.slots.map (slotClaim sources) := by
  induction origins generalizing state with
  | nil => exact List.prefix_rfl
  | cons origin tail ih =>
      exact ((consume sources origin state).original_claims_retained sources).trans
        (ih ((consume sources origin state).next sources))

def visitOrigins (index : Index) (ordinal : Nat) : List (Origin sources) :=
  (inventoryAt (sources index) (ProgrammeHistory.visitAt (sources index) ordinal)).map (Sigma.mk index)

def consumeVisit (index : Index) (ordinal : Nat) (state : (process sources).GeneratedState) :
    (process sources).GeneratedState := consumeOrigins sources (visitOrigins sources index ordinal) state

def visitRun (index : Index) (ordinal : Nat) (state : (process sources).GeneratedState) :
    (process sources).Run state.current (consumeVisit sources index ordinal state).current :=
  consumeOrigins_run sources _ _

def through (index : Index) : Nat → (process sources).GeneratedState
  | 0 => .initial (process sources)
  | ordinal + 1 => consumeVisit sources index ordinal (through index ordinal)

def originsClaim? (origin : Origin sources) : Option (Claim sources) :=
  match readIssue (sources origin.1) origin.2 with
  | .issued claim _ => some ⟨origin.1, claim⟩
  | _ => none

theorem consume_exact_claims (origin : Origin sources) (state : (process sources).GeneratedState) :
    ((consume sources origin state).next sources).current.slots.map (slotClaim sources) =
      state.current.slots.map (slotClaim sources) ++ (originsClaim? sources origin).toList := by
  unfold consume originsClaim?
  cases readIssue (sources origin.1) origin.2 with
  | issued claim exactOrigin =>
      change (state.current.slots ++ [ObligationSlot.live (admission sources ⟨origin.1, claim⟩).toObligation]).map _ = _
      simp only [List.map_append, List.map_cons, List.map_nil, slotClaim, slotObligation, Option.toList_some]
      rfl
  | nonfinancial =>
      cases readMovement (sources origin.1) origin.2 with
      | none => simp only [InstructionResult.next, Option.toList_none, List.append_nil]
      | some movement =>
          simpa only [InstructionResult.next, Option.toList_none, List.append_nil] using
            (allocate sources origin state movement.quantity (movement.quantity_nonnegative _)).original_claims
  | rejected instruction original refused => simp only [InstructionResult.next, Option.toList_none, List.append_nil]
  | missingBirth party notBorn => simp only [InstructionResult.next, Option.toList_none, List.append_nil]

theorem origins_exact_claims (origins : List (Origin sources)) (state : (process sources).GeneratedState) :
    (consumeOrigins sources origins state).current.slots.map (slotClaim sources) =
      state.current.slots.map (slotClaim sources) ++ origins.filterMap (originsClaim? sources) := by
  induction origins generalizing state with
  | nil => exact (List.append_nil _).symm
  | cons origin tail ih =>
      change (consumeOrigins sources tail ((consume sources origin state).next sources)).current.slots.map _ = _
      rw [ih, consume_exact_claims]
      simp only [List.filterMap_cons]
      cases originsClaim? sources origin <;> simp only [Option.toList_none, Option.toList_some,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family
