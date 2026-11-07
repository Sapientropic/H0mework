import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Scan.Tail
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.Boundary
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.CurrentScope.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (located : Located input depth count prefixLimit renewalLimit)
  (prepared : Prepared input depth count prefixLimit renewalLimit located)

local notation "rawAt" => Material.rawAt input depth count prefixLimit renewalLimit

inductive Stop : Type
  | exhausted {start current : Physical.Cursor Party Good Port Technology Instrument}
      (prior : PendingAt input depth count prefixLimit renewalLimit located prepared start current)
      (empty : prior.remaining = [])
  | feeBlocked {start current : Physical.Cursor Party Good Port Technology Instrument}
      (prior : PendingAt input depth count prefixLimit renewalLimit located prepared start current)
      (pair : Abolition.Material.Migration.CodePair Party Good Port Technology Instrument)
      (remaining : List (Abolition.Material.Migration.CodePair Party Good Port Technology Instrument))
      (head : prior.remaining = pair :: remaining)
      (obstruction : Review.Blockage input.law prepared.fee.request prepared.fee.scope (rawAt current))
      (attempted : Review.attempt input.law prepared.fee.request prepared.fee.scope (rawAt current) = .inr obstruction)
  | diverged (before : Physical.Cursor Party Good Port Technology Instrument)
      (expected supplied : Compile.RawInput Party Good Port Technology Instrument)
      (different : supplied ≠ expected)

/-- A dependent readout of the one physical input history. Material payment
keeps the original native responsibility; it is not a lifecycle terminal. -/
inductive PhaseAt (current : Physical.Cursor Party Good Port Technology Instrument) : Type
  | priming (due : Mandatory.FirstRenewalDue input depth count prefixLimit renewalLimit located.event ∧
      Mandatory.CurrentScope.Clear input depth count prefixLimit renewalLimit located.event)
      (atRegistration : current = located.epoch input depth count prefixLimit renewalLimit)
  | pending {start} (pending : PendingAt input depth count prefixLimit renewalLimit located prepared start current)
  | materialCandidate {start} (candidate : CandidateAt input depth count prefixLimit renewalLimit located prepared start current)
  | frontExecuted {start before}
      (candidate : CandidateAt input depth count prefixLimit renewalLimit located prepared start before)
      (actual : current = candidate.frontTarget)
  | materialPaid {start before}
      (candidate : CandidateAt input depth count prefixLimit renewalLimit located prepared start before)
      (occurred : candidate.tailTarget.past <+: current.past)
  | stopped (reason : Stop input depth count prefixLimit renewalLimit located prepared)

abbrev View := Σ current : Physical.Cursor Party Good Port Technology Instrument,
  PhaseAt input depth count prefixLimit renewalLimit located prepared current

def first : View input depth count prefixLimit renewalLimit located prepared :=
  if due : Mandatory.FirstRenewalDue input depth count prefixLimit renewalLimit located.event ∧
      Mandatory.CurrentScope.Clear input depth count prefixLimit renewalLimit located.event then
    ⟨located.epoch input depth count prefixLimit renewalLimit, .priming due rfl⟩
  else ⟨located.epoch input depth count prefixLimit renewalLimit,
    .pending (initialPending input depth count prefixLimit renewalLimit located prepared _)⟩

def expectedRaw (view : View input depth count prefixLimit renewalLimit located prepared) :
    Compile.RawInput Party Good Port Technology Instrument :=
  match view.2 with
  | .priming .. => .advance
  | .pending pending => match pending.remaining with
    | [] => .stopReview
    | _ :: _ => .primitive prepared.fee.request
  | .materialCandidate candidate => .migrate candidate.pair
  | .frontExecuted .. | .materialPaid .. => .advance
  | .stopped _ => .stopReview

def advance (view : View input depth count prefixLimit renewalLimit located prepared) :
    View input depth count prefixLimit renewalLimit located prepared :=
  match view.2 with
  | .priming _ _ =>
      let after := Physical.next (Physical.receive view.1 .advance)
      ⟨after, .pending (initialPending input depth count prefixLimit renewalLimit located prepared after)⟩
  | .pending pending =>
      match head : pending.remaining with
      | [] => ⟨Physical.next (Physical.receive view.1 .stopReview), .stopped (.exhausted pending head)⟩
      | pair :: remaining =>
          match afterFee input depth count prefixLimit renewalLimit located prepared pending pair remaining head with
          | .candidate candidate => ⟨Fees.feeTarget view.1 prepared.fee, .materialCandidate candidate⟩
          | .rejected _ _ _ after _ => ⟨Fees.feeTarget view.1 prepared.fee, .pending after⟩
          | .blocked obstruction attempted =>
              ⟨Fees.feeTarget view.1 prepared.fee, .stopped (.feeBlocked pending pair remaining head obstruction attempted)⟩
  | .materialCandidate candidate => ⟨candidate.frontTarget, .frontExecuted candidate rfl⟩
  | .frontExecuted candidate actual =>
      ⟨Physical.next (Physical.receive view.1 .advance), .materialPaid candidate (by
        rw [actual]
        exact List.prefix_rfl)⟩
  | .materialPaid candidate occurred =>
      ⟨Physical.next (Physical.receive view.1 .advance), .materialPaid candidate
        (occurred.trans (List.prefix_append _ _))⟩
  | .stopped reason => ⟨Physical.next (Physical.receive view.1 .stopReview), .stopped reason⟩

theorem advancement_is_the_original_physical_input
    (view : View input depth count prefixLimit renewalLimit located prepared) :
    (advance input depth count prefixLimit renewalLimit located prepared view).1 =
      Physical.next (Physical.receive view.1 (expectedRaw input depth count prefixLimit renewalLimit located prepared view)) := by
  rcases view with ⟨current, phase⟩
  cases phase with
  | pending pending =>
      dsimp only [advance, expectedRaw]
      split
      next empty => conv_rhs => rw [empty]
      next pair remaining head =>
        conv_rhs => rw [head]
        split <;> rfl
  | priming due atRegistration => rfl
  | materialCandidate candidate => rfl
  | frontExecuted candidate actual => rfl
  | materialPaid candidate occurred => rfl
  | stopped reason => rfl

/-- Every supplied raw input is interpreted by the existing physical fold.
Deviation retains the original expected opcode and becomes a typed residual;
it cannot silently choose a new epoch or grant a successful candidate. -/
def consume (view : View input depth count prefixLimit renewalLimit located prepared)
    (raw : Compile.RawInput Party Good Port Technology Instrument) :
    View input depth count prefixLimit renewalLimit located prepared := by
  classical
  exact match view.2 with
  | .stopped reason => ⟨Physical.next (Physical.receive view.1 raw), .stopped reason⟩
  | .materialPaid candidate occurred =>
      ⟨Physical.next (Physical.receive view.1 raw), .materialPaid candidate
        (occurred.trans (List.prefix_append _ _))⟩
  | _ =>
      if same : raw = expectedRaw input depth count prefixLimit renewalLimit located prepared view then
        advance input depth count prefixLimit renewalLimit located prepared view
      else ⟨Physical.next (Physical.receive view.1 raw), .stopped
        (.diverged view.1 (expectedRaw input depth count prefixLimit renewalLimit located prepared view) raw same)⟩

theorem consume_uses_the_literal_original_next
    (view : View input depth count prefixLimit renewalLimit located prepared)
    (raw : Compile.RawInput Party Good Port Technology Instrument) :
    (consume input depth count prefixLimit renewalLimit located prepared view raw).1 =
      Physical.next (Physical.receive view.1 raw) := by
  rcases view with ⟨current, phase⟩
  cases phase <;> dsimp only [consume]
  all_goals first
    | rfl
    | (split
       · next same =>
           rw [advancement_is_the_original_physical_input, ← same]
       · rfl)

def replay (view : View input depth count prefixLimit renewalLimit located prepared) :
    List (Compile.RawInput Party Good Port Technology Instrument) →
      View input depth count prefixLimit renewalLimit located prepared
  | [] => view
  | raw :: rest => replay (consume input depth count prefixLimit renewalLimit located prepared view raw) rest

theorem replay_preserves_the_entire_actual_input_order
    (view : View input depth count prefixLimit renewalLimit located prepared)
    (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    (replay input depth count prefixLimit renewalLimit located prepared view past).1.past = view.1.past ++ past := by
  induction past generalizing view with
  | nil => simp only [replay, List.append_nil]
  | cons raw rest ih =>
      rw [replay, ih, consume_uses_the_literal_original_next]
      simp only [Physical.next, Physical.receive, List.append_assoc, List.singleton_append]

def atCursor (current : Physical.Cursor Party Good Port Technology Instrument) :=
  replay input depth count prefixLimit renewalLimit located prepared
    (first input depth count prefixLimit renewalLimit located prepared)
    (current.past.drop (located.epoch input depth count prefixLimit renewalLimit).past.length)

theorem recovered_phase_reads_the_same_actual_past
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (original : recovered input depth count prefixLimit renewalLimit current = some located) :
    (atCursor input depth count prefixLimit renewalLimit located prepared current).1.past = current.past := by
  obtain ⟨remaining, decomposition⟩ := recovery_uses_a_real_consumed_registration input depth count
    prefixLimit renewalLimit current located original
  have pastEq : current.past = (located.epoch input depth count prefixLimit renewalLimit).past ++ remaining := by
    rw [located.epoch_is_after_the_original_registration]
    exact decomposition
  unfold atCursor
  rw [replay_preserves_the_entire_actual_input_order]
  have firstPast : (first input depth count prefixLimit renewalLimit located prepared).1.past =
      (located.epoch input depth count prefixLimit renewalLimit).past := by unfold first; split <;> rfl
  rw [firstPast, pastEq, List.drop_left]

#print axioms advancement_is_the_original_physical_input
#print axioms consume_uses_the_literal_original_next
#print axioms recovered_phase_reads_the_same_actual_past

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control
