import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Renewal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

structure Plan where
  private mk ::
  rawWord : RawEvent Party Good Port Technology Instrument
  generated : rawWord ∈ candidates input depth count prefixLimit renewalLimit oldPast current
  checked : Checks input depth count prefixLimit renewalLimit oldPast current rawWord

structure Obstruction where
  private mk ::
  excluded : ∀ word ∈ candidates input depth count prefixLimit renewalLimit oldPast current,
    ¬ Checks input depth count prefixLimit renewalLimit oldPast current word
  failureAt : ∀ word ∈ candidates input depth count prefixLimit renewalLimit oldPast current,
    Macro.Public.Scope.Failure input depth count prefixLimit renewalLimit oldPast current (.execute word)

inductive Outcome : Type
  | accepted (plan : Plan input depth count prefixLimit renewalLimit oldPast current)
  | obstructed (obstruction : Obstruction input depth count prefixLimit renewalLimit oldPast current)

def exactFailure (word : RawEvent Party Good Port Technology Instrument)
    (unchecked : ¬ Checks input depth count prefixLimit renewalLimit oldPast current word) :
    Macro.Public.Scope.Failure input depth count prefixLimit renewalLimit oldPast current (.execute word) := by
  cases found : Macro.Public.Scope.inspect input depth count prefixLimit renewalLimit oldPast current (.execute word) with
  | rejected failed => exact failed
  | delegated absent => cases absent
  | accepted actual selected checked =>
      have same : actual = executable word := Option.some.inj selected.symm
      cases same
      exact False.elim (unchecked checked)

private def compileFeasible : Outcome input depth count prefixLimit renewalLimit oldPast current :=
  match Material.inspectList (fun word => ¬ Checks input depth count prefixLimit renewalLimit oldPast current word)
      (candidates input depth count prefixLimit renewalLimit oldPast current) with
  | .failure word generated notUnchecked => .accepted ⟨word, generated, of_not_not notUnchecked⟩
  | .clear excluded => .obstructed ⟨excluded, fun word present =>
      exactFailure input depth count prefixLimit renewalLimit oldPast current word (excluded word present)⟩

def compile : Outcome input depth count prefixLimit renewalLimit oldPast current :=
  match Abolition.Completion.Actual.Dividend.Financial.Preference.Renewal.select
      input depth count prefixLimit renewalLimit oldPast current with
  | .selected selection => .accepted ⟨selection.rawWord, selection.generated, selection.checked⟩
  | .noStrict _ => compileFeasible input depth count prefixLimit renewalLimit oldPast current

theorem an_available_full_account_extension_is_the_actual_renewal_plan
    (selection : Abolition.Completion.Actual.Dividend.Financial.Preference.Renewal.Selected
      input depth count prefixLimit renewalLimit oldPast current)
    (source : Abolition.Completion.Actual.Dividend.Financial.Preference.Renewal.select
      input depth count prefixLimit renewalLimit oldPast current = .selected selection) :
    ∃ plan, compile input depth count prefixLimit renewalLimit oldPast current = .accepted plan ∧
      plan.rawWord = selection.rawWord ∧
      Abolition.Completion.Actual.Dividend.Financial.Checks input depth count prefixLimit renewalLimit oldPast
        (Abolition.Completion.Actual.Dividend.Financial.Preference.Renewal.successor current plan.rawWord) := by
  unfold compile
  rw [source]
  exact ⟨_, rfl, rfl, selection.strict⟩

#print axioms compile
#print axioms exactFailure
#print axioms an_available_full_account_extension_is_the_actual_renewal_plan

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive
