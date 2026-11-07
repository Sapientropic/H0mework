import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (snapshot : Physical.Cursor Party Good Port Technology Instrument)

structure Plan where
  private mk ::
  rawWord : RawEvent Party Good Port Technology Instrument
  generated : rawWord ∈ candidates input depth count prefixLimit renewalLimit snapshot
  checked : Checks input depth count prefixLimit renewalLimit snapshot rawWord

structure Obstruction where
  private mk ::
  excluded : ∀ word ∈ candidates input depth count prefixLimit renewalLimit snapshot,
    ¬ Checks input depth count prefixLimit renewalLimit snapshot word
  failureAt : ∀ word ∈ candidates input depth count prefixLimit renewalLimit snapshot,
    Macro.Public.Scope.Failure input depth count prefixLimit renewalLimit snapshot.past publicStart (.execute word)

inductive Outcome : Type
  | accepted (plan : Plan input depth count prefixLimit renewalLimit snapshot)
  | obstructed (obstruction : Obstruction input depth count prefixLimit renewalLimit snapshot)

def exactFailure (word : RawEvent Party Good Port Technology Instrument)
    (unchecked : ¬ Checks input depth count prefixLimit renewalLimit snapshot word) :
    Macro.Public.Scope.Failure input depth count prefixLimit renewalLimit snapshot.past publicStart (.execute word) := by
  cases found : Macro.Public.Scope.inspect input depth count prefixLimit renewalLimit snapshot.past publicStart (.execute word) with
  | rejected failed => exact failed
  | delegated absent => cases absent
  | accepted actual selected checked =>
      have same : actual = executable word := Option.some.inj selected.symm
      cases same
      exact False.elim (unchecked checked)

/-- The private constructors and sole source factory stay together. -/
private def compileFeasible : Outcome input depth count prefixLimit renewalLimit snapshot :=
  match Material.inspectList (fun word => ¬ Checks input depth count prefixLimit renewalLimit snapshot word)
      (candidates input depth count prefixLimit renewalLimit snapshot) with
  | .failure word generated notUnchecked => .accepted ⟨word, generated, of_not_not notUnchecked⟩
  | .clear excluded => .obstructed ⟨excluded, fun word present =>
      exactFailure input depth count prefixLimit renewalLimit snapshot word (excluded word present)⟩

def compile : Outcome input depth count prefixLimit renewalLimit snapshot :=
  match Abolition.Completion.Actual.Dividend.Financial.Preference.select
      input depth count prefixLimit renewalLimit snapshot with
  | .selected selection => .accepted ⟨selection.rawWord, selection.generated, selection.checked⟩
  | .noStrict _ => compileFeasible input depth count prefixLimit renewalLimit snapshot

theorem an_available_full_account_improvement_is_the_actual_public_plan
    (selection : Abolition.Completion.Actual.Dividend.Financial.Preference.Selected
      input depth count prefixLimit renewalLimit snapshot)
    (source : Abolition.Completion.Actual.Dividend.Financial.Preference.select
      input depth count prefixLimit renewalLimit snapshot = .selected selection) :
    ∃ plan, compile input depth count prefixLimit renewalLimit snapshot = .accepted plan ∧
      plan.rawWord = selection.rawWord ∧
      Abolition.Completion.Actual.Dividend.Financial.Checks input depth count prefixLimit renewalLimit snapshot.past
        (Abolition.Completion.Actual.Dividend.Financial.Preference.firstPeriod plan.rawWord) := by
  unfold compile
  rw [source]
  exact ⟨_, rfl, rfl, selection.strict⟩

#print axioms exactFailure
#print axioms compile
#print axioms an_available_full_account_improvement_is_the_actual_public_plan

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan
