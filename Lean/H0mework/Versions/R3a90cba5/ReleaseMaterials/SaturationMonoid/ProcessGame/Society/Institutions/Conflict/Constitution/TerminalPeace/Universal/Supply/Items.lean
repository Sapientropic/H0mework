import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction.Checks
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Exit.AutonomousProduction (SelfOperation)
open Capitalism.Universal.Abolition.Material (inspectList)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def OwnOperation (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .transfer payer _ _ => request.signer = payer
  | .present => True
  | _ => SelfOperation request

instance (request : Request Party Good Port Technology Instrument) : Decidable (OwnOperation request) := by
  unfold OwnOperation
  cases request.operation <;> infer_instance

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem OwnOperation.of_self {request : Request Party Good Port Technology Instrument}
    (self : SelfOperation request) : OwnOperation request := by
  cases operation : request.operation <;> simp_all [OwnOperation, SelfOperation]

variable (law : RawLaw Party Good Port Technology Instrument) (roster : List Party)
  (item : ExecutionItem Party Good Port Technology Instrument)

/-- Publicly available ports are usable at the original law. The actual
instruction spends its own actor's stock and carries no third-party consent. -/
structure OwnItem : Prop where
  operation : OwnOperation item.request
  member : item.request.signer ∈ roster
  noConsent : item.request.consents = []
  valid : law.Valid item.before item.request

inductive ItemIssue : Type
  | nonPersonal (failed : ¬ OwnOperation item.request)
  | outsider (failed : item.request.signer ∉ roster)
  | thirdPartyConsent (failed : item.request.consents ≠ [])
  | materialShortage (lot : (Party × Good) × ℚ)
      (original : lot ∈ law.debit item.before item.request)
      (short : item.before.stock lot.1.1 lot.1.2 < flowAt (law.debit item.before item.request) lot.1.1 lot.1.2)
  | authority (failed : ¬ law.Valid item.before item.request)
      (stocked : ∀ lot ∈ law.debit item.before item.request,
        flowAt (law.debit item.before item.request) lot.1.1 lot.1.2 ≤ item.before.stock lot.1.1 lot.1.2)

omit [DecidableEq Instrument] in
theorem ItemIssue.refutes (issue : ItemIssue law roster item) : ¬ OwnItem law roster item := by
  intro checked
  cases issue with
  | nonPersonal failed => exact failed checked.operation
  | outsider failed => exact failed checked.member
  | thirdPartyConsent failed => exact failed checked.noConsent
  | materialShortage lot original short =>
    exact (not_le_of_gt short) (checked.valid.2.2.2.2.2 lot original)
  | authority failed _ => exact failed checked.valid

private def inspectItem : ItemIssue law roster item ⊕ PLift (OwnItem law roster item) :=
  if own : OwnOperation item.request then
    if member : item.request.signer ∈ roster then
      if signed : item.request.consents = [] then
        if paid : law.Valid item.before item.request then
          .inr ⟨⟨own, member, signed, paid⟩⟩
        else
          match inspectList (fun lot : (Party × Good) × ℚ =>
            flowAt (law.debit item.before item.request) lot.1.1 lot.1.2 ≤ item.before.stock lot.1.1 lot.1.2)
              (law.debit item.before item.request) with
          | .failure lot original short => .inl (.materialShortage lot original (lt_of_not_ge short))
          | .clear stocked => .inl (.authority paid stocked)
      else .inl (.thirdPartyConsent signed)
    else .inl (.outsider member)
  else .inl (.nonPersonal own)

variable (items : List (ExecutionItem Party Good Port Technology Instrument))

structure ItemFailure : Type where
  position : Fin items.length
  issue : ItemIssue law roster items[position]
  earlier : ∀ prior : Fin items.length, prior.val < position.val → OwnItem law roster items[prior]

omit [DecidableEq Instrument] in
theorem ItemFailure.refutes (failure : ItemFailure law roster items) :
    ¬ ∀ item ∈ items, OwnItem law roster item :=
  fun paid => failure.issue.refutes law roster _ (paid _ (List.getElem_mem failure.position.isLt))

/-- The first failure is at the original ordinal even if equal requests
appear elsewhere in the same finite execution. -/
def inspectItems : (items : List (ExecutionItem Party Good Port Technology Instrument)) →
    ItemFailure law roster items ⊕ PLift (∀ item ∈ items, OwnItem law roster item)
  | [] => .inr ⟨by simp⟩
  | head :: tail =>
    match inspectItem law roster head with
    | .inl issue => .inl ⟨0, issue, fun _ early => (Nat.not_lt_zero _ early).elim⟩
    | .inr first =>
      match inspectItems tail with
      | .inl failed =>
        .inl ⟨failed.position.succ, failed.issue, by
          intro prior
          refine Fin.cases ?_ (fun rest => ?_) prior
          · intro _
            exact first.down
          · intro early
            exact failed.earlier rest (Nat.lt_of_succ_lt_succ early)⟩
      | .inr later => .inr ⟨fun actual listed => by
          rcases List.mem_cons.mp listed with rfl | original
          · exact first.down
          · exact later.down actual original⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply
