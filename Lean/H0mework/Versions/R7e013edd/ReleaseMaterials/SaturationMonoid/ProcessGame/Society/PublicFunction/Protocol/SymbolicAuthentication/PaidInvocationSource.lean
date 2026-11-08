import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidInvocationRebase
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidInvocationSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
abbrev Action := Request Party Good Port (Mandate.State Party Technology) Instrument

-- Installed service code fixes the exchange; bills and consensus readouts cannot choose its price.
structure Contract where
 payer : Party
 provider : Party
 unit : Good
 units : ℚ
 steps : Nat
 payment : Action (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
 acceptance : Action (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)

variable (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
 (contract : Contract (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
 (saved : Cursor old)
def catalogue : CatalogueHandoffSource.Catalogue old :=
 ⟨[contract.payment,contract.acceptance],1,[],0,
   (List.finRange old.sites).map Event.activate ++ [.adversary contract.acceptance]⟩
abbrev code := CatalogueHandoffSource.code old (catalogue old contract)
abbrev start := CatalogueHandoffSource.cursor old (catalogue old contract) saved

omit [DecidableEq Port] [DecidableEq Technology] in
theorem activation_present (site : Fin old.sites) :
 Event.activate site ∈ (code old contract).eventAlphabet :=
 List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨site,List.mem_finRange _,rfl⟩))

def protocol (enabled : Bool) : Rule (code old contract) where
 work := ⟨fun _ _ => if enabled then [contract.payment] else [], by
   apply (code old contract).every_local_policy_is_enumerated
   intro key _
   apply (mem_words_iff _ _ _).mpr
   cases enabled with
   | false => simp
   | true => exact ⟨Nat.le_max_right _ _,by simp [catalogue]⟩⟩
 events := fun key _ => ⟨some ⟨.activate key.1,activation_present old contract key.1⟩,by
   apply List.mem_cons_of_mem
   apply List.mem_map.mpr
   refine ⟨⟨.activate key.1,activation_present old contract key.1⟩,?_,rfl⟩
   exact List.mem_filter.mpr ⟨List.mem_attach _ _,by simp⟩⟩

def supplier (accept : Bool) : Opponent (code old contract) :=
 EventStep.fixed (if accept then some ⟨.adversary contract.acceptance,by
   exact List.mem_append_right _ (List.mem_append_right _ (by simp))⟩ else none)
def stages (enabled accept : Bool) : List (EventHistory.Stage (code := code old contract)) :=
 [(protocol old contract enabled,EventStep.fixed none),(SilentWindow.quiet,supplier old contract accept)]
abbrev paymentRow (enabled : Bool) := StageTrace.material (start old contract saved)
 (protocol old contract enabled) (EventStep.fixed none)
abbrev acceptanceRow (enabled accept : Bool) := StageTrace.material
 ((start old contract saved).after (protocol old contract enabled) (EventStep.fixed none))
 SilentWindow.quiet (supplier old contract accept)
abbrev paid (enabled accept : Bool) := EventHistory.execute (start old contract saved) (stages old contract enabled accept)

def Full (enabled accept : Bool) : Prop :=
 (paymentRow old contract saved enabled).submitted = [contract.payment] ∧
 (acceptanceRow old contract saved enabled accept).submitted = [contract.acceptance] ∧
 contract.payment.signer = contract.payer ∧ contract.acceptance.signer = contract.provider ∧
 (∀ item ∈ StageTrace.items (paymentRow old contract saved enabled), old.law.Valid item.before item.request) ∧
 (∀ item ∈ StageTrace.items (acceptanceRow old contract saved enabled accept), old.law.Valid item.before item.request) ∧
 0 < contract.units ∧ 0 < contract.steps ∧
 flowAt (old.law.actualDebit (paymentRow old contract saved enabled).before.current contract.payment) contract.payer contract.unit = contract.units ∧
 flowAt (old.law.actualCredit (paymentRow old contract saved enabled).before.current contract.payment) contract.provider contract.unit = contract.units ∧
 (paid old contract saved enabled accept).cut ≤ (paid old contract saved enabled accept).entry.budget
instance (enabled accept : Bool) : Decidable (Full old contract saved enabled accept) := by unfold Full;infer_instance
def admitted (enabled accept : Bool) : Bool := decide (Full old contract saved enabled accept)

structure Bill where
 origin : Nat
 payer : Party
 provider : Party
 unit : Good
 units : ℚ
 steps : Nat
 deriving DecidableEq

def quote (enabled : Bool) : Bill (Party := Party) (Good := Good) :=
 ⟨(paymentRow old contract saved enabled).cursor.cut,contract.payer,contract.provider,contract.unit,contract.units,contract.steps⟩
structure Account (enabled accept : Bool) where
 private mk ::
 ancestor : Cursor old
 ancestor_exact : ancestor = saved
 point : Cursor (code old contract)
 used : List Nat

def initial (enabled accept : Bool) : Account old contract saved enabled accept :=
 ⟨saved,rfl,paid old contract saved enabled accept,[]⟩
inductive Refusal where
 | changedBill | unpaid | duplicate | stale
 deriving DecidableEq
inductive Result (enabled accept : Bool) where
 | blocked (reason : Refusal) (account : Account old contract saved enabled accept)
 | opened (account : Account old contract saved enabled accept)

def redeem {enabled accept : Bool} (account : Account old contract saved enabled accept)
 (bill : Bill (Party := Party) (Good := Good)) : Result old contract saved enabled accept :=
 if bill ≠ quote old contract saved enabled then .blocked .changedBill account
 else if admitted old contract saved enabled accept ≠ true then .blocked .unpaid account
 else if bill.origin ∈ account.used then .blocked .duplicate account
 else if account.point.cut ≠ (paid old contract saved enabled accept).cut ∨
   account.point.entry.budget ≠ (paid old contract saved enabled accept).entry.budget then .blocked .stale account
 else .opened ⟨account.ancestor,account.ancestor_exact,
   PaidInvocationRebase.cursor account.point bill.steps,account.used++[bill.origin]⟩
def produce (enabled accept : Bool) := redeem old contract saved (initial old contract saved enabled accept) (quote old contract saved enabled)
def opened (enabled accept : Bool) (_accepted : admitted old contract saved enabled accept = true) : Account old contract saved enabled accept :=
 ⟨saved,rfl,PaidInvocationRebase.cursor (paid old contract saved enabled accept) contract.steps,
   [(quote old contract saved enabled).origin]⟩

theorem actual_admission_requires_both_original_valid_occurrences (enabled accept : Bool)
 (accepted : admitted old contract saved enabled accept = true) : Full old contract saved enabled accept := of_decide_eq_true accepted

theorem actual_admission_generates_the_paid_window (enabled accept : Bool)
 (accepted : admitted old contract saved enabled accept = true) :
 produce old contract saved enabled accept = .opened (opened old contract saved enabled accept accepted) := by
 simp [produce,redeem,initial,opened,accepted,quote]

theorem the_same_invoice_cannot_be_redeemed_again (enabled accept : Bool)
 (accepted : admitted old contract saved enabled accept = true) :
 redeem old contract saved (opened old contract saved enabled accept accepted) (quote old contract saved enabled) =
 .blocked .duplicate (opened old contract saved enabled accept accepted) := by simp [redeem,opened,accepted]

theorem absent_payment_or_acceptance_cannot_open_the_window (enabled accept : Bool)
 (refused : admitted old contract saved enabled accept = false) :
 produce old contract saved enabled accept = .blocked .unpaid (initial old contract saved enabled accept) := by
 simp [produce,redeem,refused]

theorem changed_price_or_identity_is_rejected {enabled accept : Bool}
 (account : Account old contract saved enabled accept) (bill : Bill (Party := Party) (Good := Good))
 (changed : bill ≠ quote old contract saved enabled) :
 redeem old contract saved account bill = .blocked .changedBill account := by simp only [redeem,if_pos changed]

theorem paid_opening_preserves_the_entire_actual_endpoint (enabled accept : Bool)
 (accepted : admitted old contract saved enabled accept = true) :
 EventStep.seed (opened old contract saved enabled accept accepted).point =
 PaidInvocationRebase.credit (EventStep.seed (paid old contract saved enabled accept)) contract.steps :=
 PaidInvocationRebase.seed_credit _ _ (actual_admission_requires_both_original_valid_occurrences old contract saved enabled accept accepted).2.2.2.2.2.2.2.2.2.2

theorem paid_opening_preserves_every_original_financial_account (enabled accept : Bool)
 (accepted : admitted old contract saved enabled accept = true) (ordinal : Nat)
 (earlier : ordinal ≤ EventStep.boundary (paid old contract saved enabled accept)) :
 Native.Coupling.Match (code old contract) (paid old contract saved enabled accept).source.input
 (opened old contract saved enabled accept accepted).point.source.input
 (Financial.accountAt (paid old contract saved enabled accept).source.input ordinal)
 (Financial.accountAt (opened old contract saved enabled accept accepted).point.source.input ordinal) :=
 PaidInvocationRebase.complete_financial_prefix _ _
 (actual_admission_requires_both_original_valid_occurrences old contract saved enabled accept accepted).2.2.2.2.2.2.2.2.2.2 ordinal earlier

theorem a_wrong_signer_cannot_open_any_window (enabled accept : Bool)
 (wrong : contract.acceptance.signer ≠ contract.provider) :
 admitted old contract saved enabled accept = false := by
 apply decide_eq_false_iff_not.mpr
 intro full
 exact wrong full.2.2.2.1

theorem missing_acceptance_cannot_open_any_window (enabled accept : Bool)
 (missing : (acceptanceRow old contract saved enabled accept).submitted ≠ [contract.acceptance]) :
 admitted old contract saved enabled accept = false := by
 apply decide_eq_false_iff_not.mpr
 intro full
 exact missing full.2.1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidInvocationSource
