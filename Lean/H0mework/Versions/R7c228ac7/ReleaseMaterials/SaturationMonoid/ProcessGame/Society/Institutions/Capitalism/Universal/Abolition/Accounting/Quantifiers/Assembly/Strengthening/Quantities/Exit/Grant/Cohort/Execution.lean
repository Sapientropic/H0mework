import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction.Repayment
open Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Redemption (sourceLaw sourceOrigin)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Bid" => Position Party Instrument × ℚ

def paidWord (source : C) (bid : Bid) := grantScript source bid.1 bid.2

def compileBatch : C → List Bid → Script
  | _, [] => []
  | source, bid :: rest =>
      let word := paidWord source bid
      word ++ compileBatch (Execution.endAt source word) rest

inductive FundedBatch : C → List Bid → Prop
  | empty (source : C) : FundedBatch source []
  | extend {source : C} {bid : Bid} {rest : List Bid}
      (ready : Ready source) (review : ReviewAvailable source)
      (positive : 0 < bid.2) (paid : PaidAt source bid.1 bid.2)
      (later : FundedBatch (Execution.endAt source (paidWord source bid)) rest) :
      FundedBatch source (bid :: rest)

inductive PaymentIssue (source : C) (bid : Bid)
  | nonpositive (amount : bid.2 ≤ 0)
  | pending (original : NativeObstruction source)
  | review (unavailable : ¬ ReviewAvailable source)
  | capacity (missing : ¬ Qualified (sourceLaw source) (sourceOrigin source) source.raw bid.1 bid.2)

inductive BatchIssue : C → List Bid → Type 4
  | first {source : C} {bid : Bid} {rest : List Bid} (cause : PaymentIssue source bid) :
      BatchIssue source (bid :: rest)
  | later {source : C} {bid : Bid} {rest : List Bid}
      (paid : PaidAt source bid.1 bid.2)
      (cause : BatchIssue (Execution.endAt source (paidWord source bid)) rest) :
      BatchIssue source (bid :: rest)

theorem BatchIssue.refutes {source : C} {bids : List Bid}
    (issue : BatchIssue source bids) : ¬ FundedBatch source bids := by
  induction issue with
  | first cause =>
    intro actual
    cases actual with
    | extend ready review positive paid _ =>
      cases cause with
      | nonpositive amount => exact (not_lt_of_ge amount) positive
      | pending original => exact ready original.pending
      | review unavailable => exact unavailable review
      | capacity missing => exact missing paid.qualified
  | later paid cause ih =>
    intro actual
    cases actual with
    | extend _ _ _ _ later => exact ih later

inductive BatchDecision (source : C) (bids : List Bid)
  | paid (actual : FundedBatch source bids)
  | blocked (issue : BatchIssue source bids)

/-- Each payment consumes the previous native successor. All attempted
amounts are fixed before the first payment, while checking uses the real
remaining payer capacity and original liability at each cut. -/
def decideBatch : (source : C) → (bids : List Bid) → BatchDecision source bids
  | source, [] => .paid (.empty source)
  | source, bid :: rest => by
    letI : Decidable (Qualified (sourceLaw source) (sourceOrigin source) source.raw bid.1 bid.2) := by
      unfold Qualified Redemption.Safe
      infer_instance
    exact if positive : 0 < bid.2 then
      match pending : inspectNative source with
      | some issue => .blocked (.first (.pending issue))
      | none =>
        if available : ReviewAvailable source then
          if qualified : Qualified (sourceLaw source) (sourceOrigin source) source.raw bid.1 bid.2 then
            let ready := native_is_finished_without_a_pending_item source pending
            let actual := paid_grant_is_the_literal_original_issue_and_redemption source bid.1 bid.2
              ready available qualified
            match decideBatch (Execution.endAt source (paidWord source bid)) rest with
            | .paid later => .paid (.extend ready available positive actual later)
            | .blocked issue => .blocked (.later actual issue)
          else .blocked (.first (.capacity qualified))
        else .blocked (.first (.review available))
    else .blocked (.first (.nonpositive (le_of_not_gt positive)))

theorem every_tender_has_its_actual_original_prefix_and_payment
    {source : C} {bids : List Bid} (funded : FundedBatch source bids) (bid : Bid) (listed : bid ∈ bids) :
    ∃ before after : Script, PaidAt (Execution.endAt source before) bid.1 bid.2 ∧
      compileBatch source bids = before ++ paidWord (Execution.endAt source before) bid ++ after := by
  induction funded with
  | empty _ => exact (List.not_mem_nil listed).elim
  | @extend source first rest _ready _review _positive paid later ih =>
    rcases List.mem_cons.mp listed with same | laterBid
    · subst bid
      exact ⟨[], compileBatch (Execution.endAt source (paidWord source first)) rest, paid, rfl⟩
    · obtain ⟨before, after, actual, word⟩ := ih laterBid
      let firstWord := paidWord source first
      refine ⟨firstWord ++ before, after, ?_, ?_⟩
      · rw [Execution.endAt_append]
        exact actual
      · unfold compileBatch
        dsimp only
        rw [Execution.endAt_append, word]
        simp only [firstWord, List.append_assoc]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort
