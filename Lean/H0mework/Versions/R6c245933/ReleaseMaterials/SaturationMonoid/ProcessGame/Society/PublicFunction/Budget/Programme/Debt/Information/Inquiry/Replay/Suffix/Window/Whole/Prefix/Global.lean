import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (past : List (Rule model.source.code)) (reference : Program model.source.code (horizon domain))

abbrev proposal (tail : Complete.FiniteProgram model.source.code) := extension (horizon domain) past tail.2

/-- The host fixes the paid prefix before testing the complete present-and-future relation. -/
structure Candidate (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) where
  tail : Program model.source.code (horizon domain)
  verified : Selection.Restoration.verify (tariff := tariff) (requested := requested) model domain original reference (proposal model domain past ⟨_,tail⟩) = true

abbrev Candidate.protocol {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (candidate : Candidate (tariff := tariff) (requested := requested) model domain original past reference) := proposal model domain past ⟨_,candidate.tail⟩

inductive Failure (protocol : Program model.source.code (horizon domain)) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) where
  | inadmissible (row : Selection.Restoration.Rejection (tariff := tariff) (requested := requested) model domain original reference protocol)
  | dominated (other : Program model.source.code (horizon domain))
      (accepted : Selection.Restoration.acceptable (tariff := tariff) (requested := requested) model domain original reference other)
      (strict : Selection.Restoration.strict (tariff := tariff) (requested := requested) model domain original protocol other)

variable {model domain original reference}
def failure {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (protocol : Program model.source.code (horizon domain))
    (failed : Selection.Restoration.verify (tariff := tariff) (requested := requested) model domain original reference protocol ≠ true) :
    Failure (tariff := tariff) (requested := requested) model domain original reference protocol :=
  if accepted : Selection.Restoration.acceptable (tariff := tariff) (requested := requested) model domain original reference protocol then
    match Distributed.inspect (fun other : Program model.source.code (horizon domain) =>
        ¬ Selection.Restoration.strict (tariff := tariff) (requested := requested) model domain original protocol other)
        (programs model.source.code (horizon domain)) with
    | .accepted maximal => False.elim (failed ((Selection.Restoration.verify_iff (tariff := tariff) (requested := requested) _ _ _ _ _).mpr
        ⟨accepted,fun other => maximal other (every_bounded_program_is_source_generated _ _ _)⟩))
    | .rejected other _ broken =>
        let better : Selection.Restoration.strict (tariff := tariff) (requested := requested) model domain original protocol other := of_not_not broken
        .dominated other (Selection.Restoration.acceptable_trans (tariff := tariff) (requested := requested) _ _ _ _ _ _ better.1 accepted) better
  else .inadmissible (Selection.Restoration.rejectionFrom (tariff := tariff) (requested := requested) model domain original reference protocol accepted)

variable (model domain original reference)
def check (tail : Program model.source.code (horizon domain)) (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : Option (Candidate (tariff := tariff) (requested := requested) model domain original past reference) :=
  if verified : Selection.Restoration.verify (tariff := tariff) (requested := requested) model domain original reference (proposal model domain past ⟨_,tail⟩) = true then
    some ⟨tail,verified⟩ else none

/-- Published controls have already consumed this many positions. Enumerate
only the real suffix; verification still compares every original full policy. -/
def tailPool : List (Program model.source.code (horizon domain)) :=
  (programs model.source.code (horizon domain - past.length)).map fun tail =>
    ⟨tail.controls,tail.bounded.trans (Nat.sub_le _ _)⟩

def residualTail {fuel : Nat} (tail : Program model.source.code fuel) :
    Program model.source.code (horizon domain) :=
  ⟨(clip (horizon domain - past.length) tail).controls,
    (clip (horizon domain - past.length) tail).bounded.trans (Nat.sub_le _ _)⟩

theorem every_finite_tail_has_its_source_generated_residual {fuel : Nat}
    (tail : Program model.source.code fuel) :
    residualTail model domain past tail ∈ tailPool model domain past := by
  exact List.mem_map.mpr ⟨clip (horizon domain - past.length) tail,
    every_bounded_program_is_source_generated _ _ _,rfl⟩

theorem the_residual_tail_preserves_the_entire_consumed_completion {fuel : Nat}
    (tail : Program model.source.code fuel) :
    extension (horizon domain) past (residualTail model domain past tail) =
      extension (horizon domain) past tail := by
  apply (Continuation.Whole.Program.mk.injEq ..).mpr
  change (past ++ tail.controls.take (horizon domain - past.length)).take (horizon domain) =
    (past ++ tail.controls).take (horizon domain)
  rw [List.take_append,List.take_append,List.take_take,Nat.min_self]

def candidates (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) := (tailPool model domain past).filterMap (check (tariff := tariff) (requested := requested) model domain original past reference)

def firstCandidate (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) := (tailPool model domain past).findSome? (check (tariff := tariff) (requested := requested) model domain original past reference)

theorem firstCandidate_is_the_original_source_head {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} :
    firstCandidate (tariff := tariff) (requested := requested) model domain original past reference = (candidates (tariff := tariff) (requested := requested) model domain original past reference).head? :=
  List.head?_filterMap.symm

theorem every_certified_completion_is_generated {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (tail : Complete.FiniteProgram model.source.code)
    (verified : Selection.Restoration.verify (tariff := tariff) (requested := requested) model domain original reference (proposal model domain past tail) = true) :
    ∃ candidate ∈ candidates (tariff := tariff) (requested := requested) model domain original past reference,candidate.protocol = proposal model domain past tail := by
  have same := the_residual_tail_preserves_the_entire_consumed_completion model domain past tail.2
  have normalized : Selection.Restoration.verify (tariff := tariff) (requested := requested) model domain original reference
      (proposal model domain past ⟨_,residualTail model domain past tail.2⟩) = true := by
    change Selection.Restoration.verify (tariff := tariff) (requested := requested) _ _ _ _ (extension _ _ _) = true
    rw [same];exact verified
  refine ⟨⟨residualTail model domain past tail.2,normalized⟩,List.mem_filterMap.mpr
    ⟨residualTail model domain past tail.2,every_finite_tail_has_its_source_generated_residual model domain past tail.2,?_⟩,same⟩
  simp only [check,dif_pos normalized]

inductive Outcome (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) where
  | selected (candidate : Candidate (tariff := tariff) (requested := requested) model domain original past reference)
  | blocked (rejected : ∀ tail : Complete.FiniteProgram model.source.code,
      Failure (tariff := tariff) (requested := requested) model domain original reference (proposal model domain past tail))

def compile (tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument) := .unpriced) (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) := []) : Outcome (tariff := tariff) (requested := requested) model domain original past reference :=
  match found : firstCandidate (tariff := tariff) (requested := requested) model domain original past reference with
  | some candidate => .selected candidate
  | none => .blocked fun tail => failure (tariff := tariff) (requested := requested) (proposal model domain past tail) (by
      intro verified
      obtain ⟨candidate,inside,_⟩ := every_certified_completion_is_generated model domain original past reference tail verified
      have empty := List.head?_eq_none_iff.mp ((firstCandidate_is_the_original_source_head model domain original past reference).symm.trans found)
      rw [empty] at inside;exact List.not_mem_nil inside)

namespace Candidate
variable {model domain original past reference} {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (candidate : Candidate (tariff := tariff) (requested := requested) model domain original past reference)

theorem fullAccepted : Selection.Restoration.acceptable (tariff := tariff) (requested := requested) model domain original reference candidate.protocol :=
  ((Selection.Restoration.verify_iff (tariff := tariff) (requested := requested) _ _ _ _ _).mp candidate.verified).1

theorem accepted : Selection.acceptable model domain original reference candidate.protocol :=
  Selection.Restoration.retains_original_acceptance (tariff := tariff) (requested := requested) _ _ _ _ _ candidate.fullAccepted

theorem maximal (other : Program model.source.code (horizon domain)) :
    ¬ Selection.Restoration.strict (tariff := tariff) (requested := requested) model domain original candidate.protocol other :=
  ((Selection.Restoration.verify_iff (tariff := tariff) (requested := requested) _ _ _ _ _).mp candidate.verified).2 other

theorem committed_prefix (within : past.length ≤ horizon domain) : candidate.protocol.controls.take past.length = past :=
  every_completion_preserves_the_committed_control_prefix _ _ candidate.tail within

theorem strict_if_any_original_policy_improves
    (available : ∃ other : Program model.source.code (horizon domain),Selection.Restoration.strict (tariff := tariff) (requested := requested) model domain original reference other) :
    Selection.Restoration.strict (tariff := tariff) (requested := requested) model domain original reference candidate.protocol := by
  refine ⟨candidate.fullAccepted,?_⟩
  intro backward
  obtain ⟨other,forward,notBackward⟩ := available
  apply candidate.maximal other
  refine ⟨Selection.Restoration.acceptable_trans (tariff := tariff) (requested := requested) _ _ _ _ _ _ forward backward,?_⟩
  intro reverse
  exact notBackward (Selection.Restoration.acceptable_trans (tariff := tariff) (requested := requested) _ _ _ _ _ _ backward reverse)

theorem every_finite_policy_is_compared (other : Complete.FiniteProgram model.source.code) :
    ¬ Selection.Restoration.strict (tariff := tariff) (requested := requested) model domain original candidate.protocol (clip (horizon domain) other.2) :=
  candidate.maximal _
end Candidate

variable {model domain original past reference}
def reviewFailure {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (protocol : Program model.source.code (horizon domain)) : Failure (tariff := tariff) (requested := requested) model domain original reference protocol → Bool
  | .inadmissible row => !decide (Selection.Restoration.holds (tariff := tariff) (requested := requested) model domain original reference protocol row.row)
  | .dominated other _ _ => decide (Selection.Restoration.acceptable (tariff := tariff) (requested := requested) model domain original reference other) &&
      decide (Selection.Restoration.strict (tariff := tariff) (requested := requested) model domain original protocol other)

theorem every_failure_is_independently_replayable {tariff : Native.Future.Recovery.Pricing (Request Party Good Port (Mandate.State Party Technology) Instrument)} {requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)} (protocol : Program model.source.code (horizon domain))
    (rejected : Failure (tariff := tariff) (requested := requested) model domain original reference protocol) : reviewFailure (tariff := tariff) (requested := requested) protocol rejected = true := by
  cases rejected with
  | inadmissible row => simp only [reviewFailure,Bool.not_eq_true',decide_eq_false_iff_not];exact row.broken
  | dominated other accepted strict => simp only [reviewFailure,Bool.and_eq_true,decide_eq_true_eq];exact ⟨accepted,strict⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global
