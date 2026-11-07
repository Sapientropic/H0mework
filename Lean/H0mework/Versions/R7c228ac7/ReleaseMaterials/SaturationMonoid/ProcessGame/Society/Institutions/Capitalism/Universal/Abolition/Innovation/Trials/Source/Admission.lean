import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Material.Safety

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

namespace Mechanism

variable (mechanism : Mechanism Party Good Port Technology Instrument)

/-- The original primitive event menu, not a table of successful futures. -/
def natures : List mechanism.QuotedNature := mechanism.code.eventAlphabet.attach.filterMap fun event =>
  match original : event.val with
  | .adversary request => some ⟨request, by rw [← original]; exact event.property⟩
  | .send _ _ | .deliver _ | .activate _ => none

theorem every_declared_unknown_event_is_generated (nature : mechanism.QuotedNature) : nature ∈ mechanism.natures := by
  unfold natures
  exact List.mem_filterMap.mpr ⟨⟨.adversary nature.val, nature.property⟩, List.mem_attach _ _, rfl⟩

structure RiskAdmitted where
  private mk ::
  financed : mechanism.funded = true
  invested : mechanism.invested = true
  possibleEvent : mechanism.natures ≠ []
  safe : ∀ nature ∈ mechanism.natures, Safety.Safe mechanism nature.val

inductive AdmissionFailure where
  | unfunded (missing : mechanism.funded = false)
  | investment (unpaid : mechanism.invested = false)
  | noNature (empty : mechanism.natures = [])
  | budget (nature : mechanism.QuotedNature) (original : nature ∈ mechanism.natures)
      (issue : Safety.Issue mechanism nature.val)

theorem AdmissionFailure.excludes_admission (failure : AdmissionFailure mechanism) :
    ¬ Nonempty (RiskAdmitted mechanism) := by
  rintro ⟨admitted⟩
  cases failure with
  | unfunded missing => cases missing.symm.trans admitted.financed
  | investment unpaid => cases unpaid.symm.trans admitted.invested
  | noNature empty => exact admitted.possibleEvent empty
  | budget nature original issue => exact issue.refutes mechanism nature.val (admitted.safe nature original)

inductive Admission where
  | admitted (protocol : RiskAdmitted mechanism)
  | rejected (failure : AdmissionFailure mechanism)

/-- Admission is before nature arrives. Its test protects the life budget
on every supported branch, and deliberately imposes no branchwise profit. -/
def admit : Admission mechanism :=
  if financed : mechanism.funded = true then
    if invested : mechanism.invested = true then
      if possible : mechanism.natures = [] then .rejected (.noNature possible) else
        match Material.inspectList (fun nature : mechanism.QuotedNature => Safety.Safe mechanism nature.val) mechanism.natures with
        | .clear safe => .admitted ⟨financed, invested, possible, safe⟩
        | .failure nature original notSafe =>
            match Safety.check mechanism nature.val with
            | .rejected issue => .rejected (.budget nature original issue)
            | .accepted safe => False.elim (notSafe safe)
    else .rejected (.investment (Bool.eq_false_of_not_eq_true invested))
  else .rejected (.unfunded (Bool.eq_false_of_not_eq_true financed))

theorem an_admitted_mechanism_protects_every_priced_event
    (admitted : RiskAdmitted mechanism) (nature : mechanism.QuotedNature) : Safety.Safe mechanism nature.val :=
  admitted.safe nature (mechanism.every_declared_unknown_event_is_generated nature)

theorem admission_is_fixed_before_the_unknown_event
    (first second : mechanism.Nature) :
    (fun _ : mechanism.Nature => mechanism.admit) first = (fun _ : mechanism.Nature => mechanism.admit) second := rfl

end Mechanism
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials
