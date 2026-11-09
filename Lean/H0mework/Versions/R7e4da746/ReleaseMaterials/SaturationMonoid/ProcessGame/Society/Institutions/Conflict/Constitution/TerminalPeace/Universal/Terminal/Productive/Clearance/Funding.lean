import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Funding.Signatures
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Productive.Accumulation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Entry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Quantities.Execution
open Reparation.Actual (ReceiptAnswers Script)
open Runtime.Viability (Move)
open ExposureGuard.Exit (SignersChose)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Loss" => Reparation.Actual.Occurrence seed community
local notation "Word" => Script Party Good Port Technology Instrument

abbrev FundingMove (loss : Loss) :=
  Move seed.native.input (originalRaw loss) (originalBearers loss) (originalRaw loss)

/-- Start at the original opening occurrence, drain its own pending native
work, and append the actual material word and its own accounting at each cut. -/
def fundingWord (loss : Loss) (move : FundingMove loss) : Nat → Word
  | 0 => drain (endAt seed (Occurrence.history loss))
  | n + 1 =>
    let front := fundingWord loss move n
    let source := endAt seed (Occurrence.history loss ++ front)
    front ++ periodAndAccounting source move.word

abbrev fundingCut (loss : Loss) (move : FundingMove loss) (n : Nat) :=
  endAt seed (Occurrence.history loss ++ fundingWord loss move n)

variable (loss : Reparation.Actual.Occurrence seed community) (move : FundingMove loss) {quantum : ℚ}
  (law : move.AccumulationLaw quantum) (answers : ReceiptAnswers seed) (n : Nat)

include law

private theorem funding_exact
    (initialReview : ReviewAvailable (endAt seed (Occurrence.history loss)))
    (checks : ∀ k < n, FundingChecks (fundingCut loss move k) (originalRaw loss) (originalBearers loss) move.word)
    (signed : ∀ k < n,
      SignersChose answers (Occurrence.history loss ++ fundingWord loss move k) [some (.execute move.word)]) :
    Occurrence.Eligible answers loss (fundingWord loss move n) ∧ ReadyEntry loss (fundingWord loss move n) ∧
      (fundingCut loss move n).raw = (repeatPeriod seed.native.input (originalRaw loss) move.word).currentAt n := by
  induction n with
  | zero =>
    let past := Occurrence.history loss
    let opening := endAt seed past
    have drainProof := the_first_exhausted_native_cut_is_the_original_paid_drain opening
    have aligned : fundingCut loss move 0 = endAt opening (drain opening) := endAt_append seed past _
    refine ⟨Funding.empty_inventory_is_eligible answers past past _ drainProof.2.2.1, ?_, ?_⟩
    · change Ready (fundingCut loss move 0) ∧ ReviewAvailable (fundingCut loss move 0)
      rw [aligned]
      exact ⟨drainProof.1, Funding.drain_keeps_review opening initialReview⟩
    · rw [aligned]
      exact drainProof.2.1
  | succ k earlier =>
    obtain ⟨eligible, ⟨ready, review⟩, exactRaw⟩ :=
      earlier (fun i before => checks i (before.trans (Nat.lt_succ_self k)))
        (fun i before => signed i (before.trans (Nat.lt_succ_self k)))
    let source := fundingCut loss move k
    let tail := periodAndAccounting source move.word
    have sameInput : source.native.input = seed.native.input := endAt_input _ _
    have paid : Supply.Period source.native.input (originalRaw loss) source.raw (originalBearers loss) move.word := by
      rw [sameInput, show source.raw = _ from exactRaw]
      exact (move.paid.replay law.timing law.reserve law.accumulating quantum law.positive law.duration k).1
    have currentChecks := checks k (Nat.lt_succ_self _)
    have currentSigns := signed k (Nat.lt_succ_self _)
    have allowed := Funding.signed_period_and_accounting_is_eligible (community := community)
      answers (Occurrence.history loss) (Occurrence.history loss ++ fundingWord loss move k)
      (originalRaw loss) (originalBearers loss) move.word ready review paid currentChecks currentSigns
    have actual := Funding.paid_body_reads_the_original_execution source (originalRaw loss) (originalBearers loss)
      move.word ready review paid currentChecks
    have aligned : fundingCut loss move (k + 1) = endAt source tail := by
      change endAt seed (Occurrence.history loss ++ (fundingWord loss move k ++ tail)) = endAt source tail
      rw [← List.append_assoc, endAt_append]
    refine ⟨Funding.eligible_append answers (Occurrence.history loss) (Occurrence.history loss)
      (fundingWord loss move k) tail eligible allowed, ?_, ?_⟩
    · change Ready (fundingCut loss move (k + 1)) ∧ ReviewAvailable (fundingCut loss move (k + 1))
      rw [aligned]
      exact Funding.period_and_accounting_is_ready source move.word ready review
    · have drainProof := the_first_exhausted_native_cut_is_the_original_paid_drain (next source (some (.execute move.word)))
      have exactEnd : (endAt source tail).raw = source.native.input.law.next source.raw move.word :=
        drainProof.2.1.trans actual.1
      rw [aligned, exactEnd, sameInput, show source.raw = _ from exactRaw]
      rfl

/-- The stock and elapsed time at the funded cut are those of the
actual finite original prefix, including all intervening accounting. -/
theorem funding_is_actual
    (initialReview : ReviewAvailable (endAt seed (Occurrence.history loss)))
    (checks : ∀ k < n, FundingChecks (fundingCut loss move k) (originalRaw loss) (originalBearers loss) move.word)
    (signed : ∀ k < n,
      SignersChose answers (Occurrence.history loss ++ fundingWord loss move k) [some (.execute move.word)]) :
    Occurrence.Eligible answers loss (fundingWord loss move n) ∧ ReadyEntry loss (fundingWord loss move n) ∧
      (fundingCut loss move n).raw = (repeatPeriod seed.native.input (originalRaw loss) move.word).currentAt n ∧
      (∀ person good, (fundingCut loss move n).raw.stock person good =
        (originalRaw loss).stock person good +
          (n : ℚ) * Balance.gain seed.native.input.law (originalRaw loss) move.word person good) ∧
      (originalRaw loss).clock + (n : ℚ) * quantum ≤ (fundingCut loss move n).raw.clock := by
  obtain ⟨eligible, ready, same⟩ := funding_exact loss move law answers n initialReview checks signed
  refine ⟨eligible, ready, same, ?_, ?_⟩
  · rw [same]
    exact (move.paid.replay law.timing law.reserve law.accumulating quantum law.positive law.duration n).2.1
  · rw [same]
    exact move.paid.replay_clock_bound law.timing law.reserve law.accumulating quantum law.positive law.duration n

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
