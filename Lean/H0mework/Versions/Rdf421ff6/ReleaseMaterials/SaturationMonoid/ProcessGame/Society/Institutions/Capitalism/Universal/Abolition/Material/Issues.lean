import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Checks
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan

/-! Computable inspection of one candidate's original interpreter trace.
A rejected period carries a concrete original item, member, resource, port
or policy clause.  No successful future or existential choice is an input. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

open Source.Program Source.ProgrammeControl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (members : List Party) (word : RawEvent Party Good Port Technology Instrument)

inductive PeriodIssue : Type
  | refused (item : OriginalItem input.law current word)
      (failed : ¬ input.law.Valid item.val.before item.val.request)
  | consentRequired (item : OriginalItem input.law current word)
      (failed : ¬ input.law.Valid item.val.before (withoutControllerConsents item.val.request))
  | foreignDebit (item : OriginalItem input.law current word)
      (accepted : input.law.Valid item.val.before item.val.request)
      (debit : (Party × Good) × ℚ) (original : debit ∈ input.law.debit item.val.before item.val.request)
      (positive : 0 < debit.2) (different : debit.1.1 ≠ item.val.request.signer)
  | unpaidNecessity (person : Party) (original : person ∈ members)
      (unpaid : ¬ Exit.Necessity.BundlePaid input.law current word person
        (input.law.necessities current person) .necessity)
  | unpaidMaintenance (person : Party) (original : person ∈ members)
      (unpaid : ¬ Exit.Necessity.BundlePaid input.law current word person
        (input.law.mandatoryMaintenance current person) .maintenance)
  | localControl (use : ControlUse input.law current word (localFamily input current word))
      (original : use ∈ controlInventory input.law current word (localFamily input current word))
  | freshControl (item : OriginalItem input.law current word)
      (port : Port) (required : port ∈ input.law.requiredPorts item.val.before item.val.request)
      (person : Party) (affected : person ∈ History.affectedSubjects input item.val)
      (accepted : input.law.Valid item.val.before item.val.request)
      (exclusive : PrivatePhase input.law item.val.before port person)
  | outputLoss (person : Party) (original : person ∈ members) (lot : Good × ℚ)
      (listed : lot ∈ (input.law.technique current.technology person).outputs ++
        (input.law.technique (input.law.next current word).technology person).outputs)
      (loss : amount Good (input.law.technique (input.law.next current word).technology person).outputs lot.1 <
        amount Good (input.law.technique current.technology person).outputs lot.1)
  | inputIncrease (person : Party) (original : person ∈ members) (lot : Good × ℚ)
      (listed : lot ∈ (input.law.technique current.technology person).inputs ++
        (input.law.technique (input.law.next current word).technology person).inputs)
      (loss : amount Good (input.law.technique current.technology person).inputs lot.1 <
        amount Good (input.law.technique (input.law.next current word).technology person).inputs lot.1)
  | maintenanceIncrease (person : Party) (original : person ∈ members) (lot : Good × ℚ)
      (listed : lot ∈ (input.law.technique current.technology person).maintenance ++
        (input.law.technique (input.law.next current word).technology person).maintenance)
      (loss : amount Good (input.law.technique current.technology person).maintenance lot.1 <
        amount Good (input.law.technique (input.law.next current word).technology person).maintenance lot.1)
  | opaquePolicy (callback : RawCurrent Party Good Technology Instrument →
        Request Party Good Port Technology Instrument → Bool)
      (original : input.law.policy = .opaque callback)

namespace PeriodIssue

theorem refutes (issue : PeriodIssue input current members word) : ¬ PeriodChecks input current members word := by
  intro checked
  cases issue with
  | refused item failed => exact failed (checked.1 item.val item.property).1
  | consentRequired item failed => exact failed (checked.1 item.val item.property).2.1
  | foreignDebit item _ debit original positive different =>
      exact different ((checked.1 item.val item.property).2.2 debit original positive)
  | unpaidNecessity person original unpaid => exact unpaid (checked.2.1 person original).1
  | unpaidMaintenance person original unpaid => exact unpaid (checked.2.1 person original).2
  | localControl use original =>
      have empty := List.length_eq_zero_iff.mp checked.2.2.1.1
      rw [empty] at original
      exact List.not_mem_nil original
  | freshControl item port required person affected accepted exclusive =>
      exact checked.2.2.1.2 item.val item.property port required ⟨accepted, required, person, affected, exclusive⟩
  | outputLoss person original lot listed loss =>
      exact (not_le_of_gt loss) ((checked.2.2.2.1 person original).1 lot listed)
  | inputIncrease person original lot listed loss =>
      exact (not_le_of_gt loss) ((checked.2.2.2.1 person original).2.1 lot listed)
  | maintenanceIncrease person original lot listed loss =>
      exact (not_le_of_gt loss) ((checked.2.2.2.1 person original).2.2 lot listed)
  | opaquePolicy callback original =>
      have explained := checked.2.2.2.2
      simp only [PolicyExplained, original] at explained

end PeriodIssue

private def instructionIssue (item : OriginalItem input.law current word)
    (failed : ¬ (input.law.Valid item.val.before item.val.request ∧
      input.law.Valid item.val.before (withoutControllerConsents item.val.request) ∧
      ∀ debit ∈ input.law.debit item.val.before item.val.request,
        0 < debit.2 → debit.1.1 = item.val.request.signer)) : PeriodIssue input current members word :=
  if accepted : input.law.Valid item.val.before item.val.request then
    if independent : input.law.Valid item.val.before (withoutControllerConsents item.val.request) then
      match inspectList (fun debit : (Party × Good) × ℚ =>
          0 < debit.2 → debit.1.1 = item.val.request.signer) (input.law.debit item.val.before item.val.request) with
      | .clear owned => False.elim (failed ⟨accepted, independent, owned⟩)
      | .failure debit original foreign =>
          if positive : 0 < debit.2 then
            .foreignDebit item accepted debit original positive (fun same => foreign (fun _ => same))
          else False.elim (foreign (fun h => (positive h).elim))
    else .consentRequired item independent
  else .refused item accepted

private def needsIssue (person : Party) (original : person ∈ members)
    (failed : ¬ (Exit.Necessity.BundlePaid input.law current word person
        (input.law.necessities current person) .necessity ∧
      Exit.Necessity.BundlePaid input.law current word person
        (input.law.mandatoryMaintenance current person) .maintenance)) : PeriodIssue input current members word :=
  if paid : Exit.Necessity.BundlePaid input.law current word person
      (input.law.necessities current person) .necessity then
    .unpaidMaintenance person original (fun maintenance => failed ⟨paid, maintenance⟩)
  else .unpaidNecessity person original paid

private def historicalIssue (item : OriginalItem input.law current word)
    (failed : ¬ (∀ port ∈ input.law.requiredPorts item.val.before item.val.request,
      ¬ History.FreshControl input port item.val)) : PeriodIssue input current members word :=
  match inspectList (fun port => ¬ History.FreshControl input port item.val)
      (input.law.requiredPorts item.val.before item.val.request) with
  | .clear checked => False.elim (failed checked)
  | .failure port required notAbsent =>
      if fresh : History.FreshControl input port item.val then
        match inspectList (fun person => ¬ PrivatePhase input.law item.val.before port person)
            (History.affectedSubjects input item.val) with
        | .clear noExcluded => False.elim (by
            obtain ⟨person, affected, excluded⟩ := fresh.2.2
            exact noExcluded person affected excluded)
        | .failure person affected notShared =>
            if exclusive : PrivatePhase input.law item.val.before port person then
              .freshControl item port required person affected fresh.1 exclusive
            else False.elim (notShared exclusive)
      else False.elim (notAbsent fresh)

private def productionIssue (person : Party) (original : person ∈ members)
    (failed : ¬ TechniqueDominates (input.law.technique current.technology person)
      (input.law.technique (input.law.next current word).technology person)) : PeriodIssue input current members word :=
  let before := input.law.technique current.technology person
  let after := input.law.technique (input.law.next current word).technology person
  match inspectList (fun lot : Good × ℚ => amount Good before.outputs lot.1 ≤ amount Good after.outputs lot.1)
      (before.outputs ++ after.outputs) with
  | .failure lot listed loss => .outputLoss person original lot listed (lt_of_not_ge loss)
  | .clear outputs =>
      match inspectList (fun lot : Good × ℚ => amount Good after.inputs lot.1 ≤ amount Good before.inputs lot.1)
          (before.inputs ++ after.inputs) with
      | .failure lot listed loss => .inputIncrease person original lot listed (lt_of_not_ge loss)
      | .clear inputs =>
          match inspectList (fun lot : Good × ℚ =>
              amount Good after.maintenance lot.1 ≤ amount Good before.maintenance lot.1)
              (before.maintenance ++ after.maintenance) with
          | .failure lot listed loss => .maintenanceIncrease person original lot listed (lt_of_not_ge loss)
          | .clear maintenance => False.elim (failed ⟨outputs, inputs, maintenance⟩)

inductive PeriodDecision : Type
  | accepted (checked : PeriodChecks input current members word)
  | rejected (issue : PeriodIssue input current members word)

def checkPeriod : PeriodDecision input current members word :=
  match inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
      input.law.Valid item.before item.request ∧
      input.law.Valid item.before (withoutControllerConsents item.request) ∧
      ∀ debit ∈ input.law.debit item.before item.request, 0 < debit.2 → debit.1.1 = item.request.signer)
      (input.law.rawItems current word) with
  | .failure item original failed => .rejected (instructionIssue input current members word ⟨item, original⟩ failed)
  | .clear actual =>
      match inspectList (fun person =>
          Exit.Necessity.BundlePaid input.law current word person (input.law.necessities current person) .necessity ∧
          Exit.Necessity.BundlePaid input.law current word person (input.law.mandatoryMaintenance current person) .maintenance)
          members with
      | .failure person original failed => .rejected (needsIssue input current members word person original failed)
      | .clear needs =>
          match controls : controlInventory input.law current word (localFamily input current word) with
          | use :: _ => .rejected (.localControl use (by rw [controls]; exact List.mem_cons_self))
          | [] =>
              match inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
                  ∀ port ∈ input.law.requiredPorts item.before item.request, ¬ History.FreshControl input port item)
                  (input.law.rawItems current word) with
              | .failure item original failed => .rejected (historicalIssue input current members word ⟨item, original⟩ failed)
              | .clear historical =>
                  match inspectList (fun person => TechniqueDominates (input.law.technique current.technology person)
                      (input.law.technique (input.law.next current word).technology person)) members with
                  | .failure person original failed => .rejected (productionIssue input current members word person original failed)
                  | .clear production =>
                      match policy : input.law.policy with
                      | .opaque callback => .rejected (.opaquePolicy callback policy)
                      | .unrestricted => .accepted ⟨actual, needs, ⟨by rw [controls]; rfl, historical⟩,
                          production, by simp only [PolicyExplained, policy]⟩
                      | .settlement _ => .accepted ⟨actual, needs, ⟨by rw [controls]; rfl, historical⟩,
                          production, by simp only [PolicyExplained, policy]⟩

namespace PeriodDecision

def isAccepted : PeriodDecision input current members word → Bool
  | .accepted _ => true
  | .rejected _ => false

end PeriodDecision

theorem checkPeriod_accepts_iff :
    (checkPeriod input current members word).isAccepted input current members word = true ↔
      PeriodChecks input current members word := by
  cases checkPeriod input current members word with
  | accepted checked => simp only [PeriodDecision.isAccepted, checked]
  | rejected issue =>
      simp only [PeriodDecision.isAccepted, Bool.false_eq_true, false_iff]
      exact issue.refutes input current members word

#print axioms PeriodIssue.refutes
#print axioms checkPeriod
#print axioms checkPeriod_accepts_iff

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material
