import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Issues
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.NeedFloor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.NonFinancial

/-! A migration prefix may still contain the relation being left and may
change technology. Its actual payments and old obligations are checked here;
the independent continuation is checked at its computed target. Full service
capacity transport remains distinct from the original livelihood floor. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration

open Source.Program Source.ProgrammeControl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument)
  (members : List Party) (word : RawEvent Party Good Port Technology Instrument)

def PrefixChecks : Prop :=
  ActualAndIndependent input current word ∧
  Exit.Necessity.AllNeedsPaid input.law current members word ∧
  OriginalNeedFloor input origin current members word ∧
  Root.Settlement.NonFinancial word ∧ PolicyExplained input

instance : Decidable (PrefixChecks input origin current members word) := by
  unfold PrefixChecks
  infer_instance

theorem prefix_of_period
    (paid : PeriodChecks input current members word)
    (floor : OriginalNeedFloor input origin current members word)
    (financial : Root.Settlement.NonFinancial word) : PrefixChecks input origin current members word :=
  ⟨paid.1, paid.2.1, floor, financial, paid.2.2.2.2⟩

inductive PrefixIssue : Type
  | refused (item : OriginalItem input.law current word)
      (failed : ¬ input.law.Valid item.val.before item.val.request)
  | consentRequired (item : OriginalItem input.law current word)
      (failed : ¬ input.law.Valid item.val.before (withoutControllerConsents item.val.request))
  | foreignDebit (item : OriginalItem input.law current word)
      (lot : (Party × Good) × ℚ) (original : lot ∈ input.law.debit item.val.before item.val.request)
      (positive : 0 < lot.2) (foreign : lot.1.1 ≠ item.val.request.signer)
  | necessity (person : Party) (member : person ∈ members)
      (unpaid : ¬ Exit.Necessity.BundlePaid input.law current word person
        (input.law.necessities current person) .necessity)
  | maintenance (person : Party) (member : person ∈ members)
      (unpaid : ¬ Exit.Necessity.BundlePaid input.law current word person
        (input.law.mandatoryMaintenance current person) .maintenance)
  | originalFloor (issue : NeedFloorIssue input origin current members word)
  | financial (request : Request Party Good Port Technology Instrument) (original : request ∈ word)
      (unsupported : ¬ Root.Settlement.NonFinancialRequest request)
  | opaquePolicy (callback : RawCurrent Party Good Technology Instrument →
      Request Party Good Port Technology Instrument → Bool) (source : input.law.policy = .opaque callback)

omit [DecidableEq Port] in
theorem PrefixIssue.refutes (issue : PrefixIssue input origin current members word) :
    ¬ PrefixChecks input origin current members word := by
  intro paid
  cases issue with
  | refused item failed => exact failed (paid.1 item.val item.property).1
  | consentRequired item failed => exact failed (paid.1 item.val item.property).2.1
  | foreignDebit item lot original positive foreign =>
      exact foreign ((paid.1 item.val item.property).2.2 lot original positive)
  | necessity person member unpaid => exact unpaid (paid.2.1 person member).1
  | maintenance person member unpaid => exact unpaid (paid.2.1 person member).2
  | originalFloor issue => exact issue.refutes input paid.2.2.1
  | financial request original unsupported => exact unsupported (paid.2.2.2.1 request original)
  | opaquePolicy callback source => simpa only [PolicyExplained, source] using paid.2.2.2.2

private def paymentIssue (item : OriginalItem input.law current word)
    (failed : ¬ (input.law.Valid item.val.before item.val.request ∧
      input.law.Valid item.val.before (withoutControllerConsents item.val.request) ∧
      ∀ lot ∈ input.law.debit item.val.before item.val.request,
        0 < lot.2 → lot.1.1 = item.val.request.signer)) : PrefixIssue input origin current members word :=
  if accepted : input.law.Valid item.val.before item.val.request then
    if independent : input.law.Valid item.val.before (withoutControllerConsents item.val.request) then
      match inspectList (fun lot : (Party × Good) × ℚ =>
          0 < lot.2 → lot.1.1 = item.val.request.signer) (input.law.debit item.val.before item.val.request) with
      | .clear owned => False.elim (failed ⟨accepted, independent, owned⟩)
      | .failure lot original foreign =>
          if positive : 0 < lot.2 then
            .foreignDebit item lot original positive (fun same => foreign (fun _ => same))
          else False.elim (foreign (fun h => (positive h).elim))
    else .consentRequired item independent
  else .refused item accepted

inductive PrefixDecision : Type
  | accepted (checked : PrefixChecks input origin current members word)
  | rejected (issue : PrefixIssue input origin current members word)

def checkPrefix : PrefixDecision input origin current members word :=
  match inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
      input.law.Valid item.before item.request ∧
      input.law.Valid item.before (withoutControllerConsents item.request) ∧
      ∀ lot ∈ input.law.debit item.before item.request, 0 < lot.2 → lot.1.1 = item.request.signer)
      (input.law.rawItems current word) with
  | .failure item original failed => .rejected (paymentIssue input origin current members word ⟨item, original⟩ failed)
  | .clear actual =>
      match inspectList (fun person =>
          Exit.Necessity.BundlePaid input.law current word person (input.law.necessities current person) .necessity ∧
          Exit.Necessity.BundlePaid input.law current word person (input.law.mandatoryMaintenance current person) .maintenance)
          members with
      | .failure person member unpaid =>
          if need : Exit.Necessity.BundlePaid input.law current word person
              (input.law.necessities current person) .necessity then
            .rejected (.maintenance person member (fun maintained => unpaid ⟨need, maintained⟩))
          else .rejected (.necessity person member need)
      | .clear needs =>
          match checkOriginalNeedFloor input origin current members word with
          | .rejected issue => .rejected (.originalFloor issue)
          | .accepted floor =>
              match Root.Settlement.checkFinancial word with
              | .rejected request original unsupported => .rejected (.financial request original unsupported)
              | .accepted financial =>
                  match source : input.law.policy with
                  | .opaque callback => .rejected (.opaquePolicy callback source)
                  | .unrestricted => .accepted ⟨actual, needs, floor, financial, by simp [PolicyExplained, source]⟩
                  | .settlement _ => .accepted ⟨actual, needs, floor, financial, by simp [PolicyExplained, source]⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration
