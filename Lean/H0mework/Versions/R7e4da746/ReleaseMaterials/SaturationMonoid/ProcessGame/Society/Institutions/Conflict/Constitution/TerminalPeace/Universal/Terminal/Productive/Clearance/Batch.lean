import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Payment
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Whole

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open Capitalism.Universal.Source.Program
open Reparation Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)

local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "ClaimKey" => Key Party Good

structure ClearedPrefix (reserve : Party → Good → ℚ) (front : Word) where
  word : Word
  beginsWith : front.IsPrefix word
  eligible : Occurrence.Eligible answers loss word
  ready : ReadyEntry loss word
  cleared : WholeCleared loss answers word
  reserved : ∀ person good, reserve person good ≤ (prefixRaw loss word).stock person good
  claims : (prefixRaw loss word).claims = (prefixRaw loss front).claims
  technology : (prefixRaw loss word).technology = (prefixRaw loss front).technology
  clock : (prefixRaw loss word).clock = (prefixRaw loss front).clock
  round : (prefixRaw loss word).round = (prefixRaw loss front).round

variable (channels : IndependentReceiptChannels loss answers) (reserve : Party → Good → ℚ)
  (reserveOK : ∀ person good, 0 ≤ reserve person good)

include channels reserveOK

private def payRemainingKeys (pending : List ClaimKey) (front : Word)
    (listed : ∀ key ∈ pending, key ∈ originalKeys loss)
    (outside : ∀ key ∉ pending, dueFor key (prefixRows loss answers front) = 0)
    (safe : Occurrence.Eligible answers loss front) (ready : ReadyEntry loss front)
    (funded : CoversPortfolio loss answers reserve front) :
    ClearedPrefix loss answers reserve front := by
  classical
  induction pending generalizing front with
  | nil =>
    refine ⟨front, List.prefix_rfl, safe, ready, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · intro row present
      exact every_original_row_is_cleared_when_its_key_has_zero_due row.1.key _ (outside _ (by simp)) row present rfl
    · intro person good
      exact (le_add_of_nonneg_right (cellDue_nonnegative _ (person, good))).trans (funded person good)
  | cons key rest later =>
    have original := listed key List.mem_cons_self
    have keys (other : ClaimKey) (present : other ∈ rest) := listed other (List.mem_cons_of_mem _ present)
    have missing (other : ClaimKey) (different : other ≠ key) (absent : other ∉ rest) :
        dueFor other (prefixRows loss answers front) = 0 :=
      outside other (fun present => (List.mem_cons.mp present).elim different absent)
    by_cases zero : dueFor key (prefixRows loss answers front) = 0
    · refine later front keys (fun other absent => ?_) safe ready funded
      by_cases same : other = key
      · exact same.symm ▸ zero
      · exact missing other same absent
    · let next := payKeyWord loss answers channels front key
      have positive := lt_of_le_of_ne (dueFor_nonnegative key (prefixRows loss answers front)) (Ne.symm zero)
      obtain ⟨safeNext, readyNext, fundsNext, debts, raw⟩ :=
        paying_a_key_writes_its_original_settlement loss answers channels reserve front key original
          safe ready funded reserveOK positive
      have settled (other : ClaimKey) (absent : other ∉ rest) : dueFor other (prefixRows loss answers next) = 0 := by
        rw [debts other]
        split
        · rfl
        · exact missing other ‹other ≠ key› absent
      let last := later next keys settled safeNext readyNext fundsNext
      have earlierPrefix : front.IsPrefix next := by
        unfold next payKeyWord
        rw [List.append_assoc]
        exact List.prefix_append _ _
      have claims := congrArg (fun state : Raw => state.claims) raw
      have technology := congrArg (fun state : Raw => state.technology) raw
      have clock := congrArg (fun state : Raw => state.clock) raw
      have round := congrArg (fun state : Raw => state.round) raw
      exact ⟨last.word, earlierPrefix.trans last.beginsWith, last.eligible, last.ready, last.cleared, last.reserved,
        last.claims.trans claims, last.technology.trans technology, last.clock.trans clock, last.round.trans round⟩

/-- Traverse the original claim keys and read the amount afresh at every
actual successor. The result carries the fully paid original history. -/
def clearFundedPortfolio (front : Word) (safe : Occurrence.Eligible answers loss front)
    (ready : ReadyEntry loss front) (funded : CoversPortfolio loss answers reserve front) :
    ClearedPrefix loss answers reserve front := by
  apply payRemainingKeys loss answers channels reserve reserveOK (originalKeys loss) front
    (fun _ present => present) ?_ safe ready funded
  intro key absent
  apply dueFor_eq_zero_of_key_absent
  intro present
  exact absent ((eligible_prefix_has_the_original_keys loss answers front safe) ▸ List.mem_dedup.mpr present)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
