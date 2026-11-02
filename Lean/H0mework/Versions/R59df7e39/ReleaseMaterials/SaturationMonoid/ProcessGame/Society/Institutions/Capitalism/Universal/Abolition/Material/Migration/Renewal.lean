import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Prefix
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Shared
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction.Checks

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration

open Source.Program Source.ProgrammeControl Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument)
  (members : List Party) (word : RawEvent Party Good Port Technology Instrument)

def RenewalChecks : Prop :=
  PeriodChecks input current members word ∧
  OriginalNeedFloor input origin current members word ∧
  Balance.FiniteChecks .accumulating input.law current word ∧
  ((∀ item ∈ input.law.rawItems current word, Exit.AutonomousProduction.At input.law item) ∨
    FiniteShared input current word)

instance : Decidable (RenewalChecks input origin current members word) := by
  unfold RenewalChecks
  infer_instance

structure SharedIssue where
  item : OriginalItem input.law current word
  port : Port
  required : port ∈ input.law.requiredPorts item.val.before item.val.request
  person : Party
  original : person ∈ subjects input current word
  excluded : input.law.allowed item.val.before.technology port person = false

omit [DecidableEq Port] in
theorem SharedIssue.refutes (issue : SharedIssue input current word) : ¬ FiniteShared input current word := by
  intro checked
  exact Bool.noConfusion ((checked issue.item.val issue.item.property issue.port issue.required
    issue.person issue.original).symm.trans issue.excluded)

private def sharedIssue (failed : ¬ FiniteShared input current word) : SharedIssue input current word :=
  match inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
      ∀ port ∈ input.law.requiredPorts item.before item.request,
        ∀ person ∈ subjects input current word, input.law.allowed item.before.technology port person = true)
      (input.law.rawItems current word) with
  | .clear checked => False.elim (failed checked)
  | .failure item original excluded =>
      match inspectList (fun port => ∀ person ∈ subjects input current word,
          input.law.allowed item.before.technology port person = true)
          (input.law.requiredPorts item.before item.request) with
      | .clear checked => False.elim (excluded checked)
      | .failure port required denied =>
          match inspectList (fun person => input.law.allowed item.before.technology port person = true)
              (subjects input current word) with
          | .clear checked => False.elim (denied checked)
          | .failure person present notAllowed =>
              ⟨⟨item, original⟩, port, required, person, present, Bool.eq_false_iff.mpr notAllowed⟩

inductive RenewalIssue : Type
  | period (issue : PeriodIssue input current members word)
  | floor (issue : NeedFloorIssue input origin current members word)
  | balance (issue : Balance.Issue .accumulating input.law current word)
  | unexplained (item : OriginalItem input.law current word)
      (notSelf : ¬ Exit.AutonomousProduction.At input.law item.val)
      (notShared : SharedIssue input current word)

theorem RenewalIssue.refutes (issue : RenewalIssue input origin current members word) :
    ¬ RenewalChecks input origin current members word := by
  intro checked
  cases issue with
  | period issue => exact issue.refutes input current members word checked.1
  | floor issue => exact issue.refutes input checked.2.1
  | balance issue => exact issue.refutes .accumulating input.law current word checked.2.2.1
  | unexplained item notSelf notShared =>
      rcases checked.2.2.2 with self | shared
      · exact notSelf (self item.val item.property)
      · exact notShared.refutes input current word shared

inductive RenewalDecision : Type
  | accepted (checked : RenewalChecks input origin current members word)
  | rejected (issue : RenewalIssue input origin current members word)

def checkRenewal : RenewalDecision input origin current members word :=
  match checkPeriod input current members word with
  | .rejected issue => .rejected (.period issue)
  | .accepted period =>
      match checkOriginalNeedFloor input origin current members word with
      | .rejected issue => .rejected (.floor issue)
      | .accepted floor =>
          match Balance.check .accumulating input.law current word with
          | .rejected issue => .rejected (.balance issue)
          | .accepted balance =>
              match inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
                  Exit.AutonomousProduction.At input.law item)
                  (input.law.rawItems current word) with
              | .clear self => .accepted ⟨period, floor, balance, Or.inl self⟩
              | .failure item original notSelf =>
                  if shared : FiniteShared input current word then
                    .accepted ⟨period, floor, balance, Or.inr shared⟩
                  else .rejected (.unexplained ⟨item, original⟩ notSelf (sharedIssue input current word shared))

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration
