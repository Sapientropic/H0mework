import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Lookahead

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program
open Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

def firstPeriod (word : RawEvent Party Good Port Technology Instrument) :
    Physical.Cursor Party Good Port Technology Instrument :=
  Physical.next (Physical.receive Physical.initial (.execute word))

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (snapshot : Physical.Cursor Party Good Port Technology Instrument)

def Checks (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  PublicPlan.Checks input depth count prefixLimit renewalLimit snapshot word ∧
    Financial.Checks input depth count prefixLimit renewalLimit snapshot.past (firstPeriod word)

instance (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (Checks input depth count prefixLimit renewalLimit snapshot word) := by
  unfold Checks
  infer_instance

abbrev PostFeasible (word : RawEvent Party Good Port Technology Instrument) :=
  Lookahead.Available input depth count prefixLimit renewalLimit snapshot.past (firstPeriod word)

private def scopeFailure (word : RawEvent Party Good Port Technology Instrument)
    (unchecked : ¬ PublicPlan.Checks input depth count prefixLimit renewalLimit snapshot word) :
    Macro.Public.Scope.Failure input depth count prefixLimit renewalLimit snapshot.past
      PublicPlan.publicStart (.execute word) := by
  cases found : Macro.Public.Scope.inspect input depth count prefixLimit renewalLimit
      snapshot.past PublicPlan.publicStart (.execute word) with
  | rejected failed => exact failed
  | delegated absent => cases absent
  | accepted actual selected checked =>
      have same : actual = PublicPlan.executable word := Option.some.inj selected.symm
      cases same
      exact False.elim (unchecked checked)

inductive Issue (word : RawEvent Party Good Port Technology Instrument) : Type
  | originalScope (unchecked : ¬ PublicPlan.Checks input depth count prefixLimit renewalLimit snapshot word)
      (failure : Macro.Public.Scope.Failure input depth count prefixLimit renewalLimit snapshot.past
        PublicPlan.publicStart (.execute word))
  | fullAccount (feasible : PublicPlan.Checks input depth count prefixLimit renewalLimit snapshot word)
      (issue : Financial.Issue input depth count prefixLimit renewalLimit snapshot.past (firstPeriod word))

theorem Issue.refutes (word : RawEvent Party Good Port Technology Instrument)
    (issue : Issue input depth count prefixLimit renewalLimit snapshot word) :
    ¬ Checks input depth count prefixLimit renewalLimit snapshot word := by
  intro checked
  cases issue with
  | originalScope unchecked _failure => exact unchecked checked.1
  | fullAccount _feasible issue => exact issue.refutes _ _ _ _ _ _ _ checked.2

def explain (word : RawEvent Party Good Port Technology Instrument)
    (unchecked : ¬ Checks input depth count prefixLimit renewalLimit snapshot word) :
    Issue input depth count prefixLimit renewalLimit snapshot word :=
  if feasible : PublicPlan.Checks input depth count prefixLimit renewalLimit snapshot word then
    match Financial.check input depth count prefixLimit renewalLimit snapshot.past (firstPeriod word) with
    | .accepted strict => False.elim (unchecked ⟨feasible, strict⟩)
    | .rejected issue => .fullAccount feasible issue
  else .originalScope feasible (scopeFailure input depth count prefixLimit renewalLimit snapshot word feasible)

structure Selected where
  private mk ::
  rawWord : RawEvent Party Good Port Technology Instrument
  generated : rawWord ∈ PublicPlan.candidates input depth count prefixLimit renewalLimit snapshot
  checked : PublicPlan.Checks input depth count prefixLimit renewalLimit snapshot rawWord
  strict : Financial.Checks input depth count prefixLimit renewalLimit snapshot.past (firstPeriod rawWord)

structure NoStrict where
  private mk ::
  issueAt : ∀ word ∈ PublicPlan.candidates input depth count prefixLimit renewalLimit snapshot,
    Issue input depth count prefixLimit renewalLimit snapshot word

inductive Outcome : Type
  | selected (selection : Selected input depth count prefixLimit renewalLimit snapshot)
  | noStrict (report : NoStrict input depth count prefixLimit renewalLimit snapshot)

private def selectStrict : Outcome input depth count prefixLimit renewalLimit snapshot :=
  match Material.inspectList (fun word => ¬ Checks input depth count prefixLimit renewalLimit snapshot word)
      (PublicPlan.candidates input depth count prefixLimit renewalLimit snapshot) with
  | .failure word generated notUnchecked =>
      let checked := of_not_not notUnchecked
      .selected ⟨word, generated, checked.1, checked.2⟩
  | .clear excluded => .noStrict ⟨fun word present =>
      explain input depth count prefixLimit renewalLimit snapshot word (excluded word present)⟩

/-- A complete available replacement takes precedence in the same original
candidate list. The original strict route remains available if none exists. -/
def select : Outcome input depth count prefixLimit renewalLimit snapshot :=
  match Material.inspectList (fun word => ¬ (Checks input depth count prefixLimit renewalLimit snapshot word ∧
      PostFeasible input depth count prefixLimit renewalLimit snapshot word))
      (PublicPlan.candidates input depth count prefixLimit renewalLimit snapshot) with
  | .failure word generated notUnchecked =>
      let checked := of_not_not notUnchecked
      .selected ⟨word, generated, checked.1.1, checked.1.2⟩
  | .clear _ => selectStrict input depth count prefixLimit renewalLimit snapshot

theorem an_available_complete_replacement_is_selected
    (available : ∃ word ∈ PublicPlan.candidates input depth count prefixLimit renewalLimit snapshot,
      Checks input depth count prefixLimit renewalLimit snapshot word ∧
        PostFeasible input depth count prefixLimit renewalLimit snapshot word) :
    ∃ selection, select input depth count prefixLimit renewalLimit snapshot = .selected selection ∧
      PostFeasible input depth count prefixLimit renewalLimit snapshot selection.rawWord := by
  unfold select
  split
  · rename_i word generated notUnchecked _inspected
    exact ⟨_, rfl, (of_not_not notUnchecked).2⟩
  · rename_i excluded _inspected
    obtain ⟨word, generated, checked⟩ := available
    exact False.elim (excluded word generated checked)

theorem an_actually_selected_replacement_has_a_future_when_a_complete_one_is_available
    (available : ∃ word ∈ PublicPlan.candidates input depth count prefixLimit renewalLimit snapshot,
      Checks input depth count prefixLimit renewalLimit snapshot word ∧
        PostFeasible input depth count prefixLimit renewalLimit snapshot word)
    (selection : Selected input depth count prefixLimit renewalLimit snapshot)
    (actual : select input depth count prefixLimit renewalLimit snapshot = .selected selection) :
    PostFeasible input depth count prefixLimit renewalLimit snapshot selection.rawWord := by
  obtain ⟨selected, produced, future⟩ := an_available_complete_replacement_is_selected
    input depth count prefixLimit renewalLimit snapshot available
  have same : selected = selection := Outcome.selected.inj (produced.symm.trans actual)
  exact same ▸ future

theorem an_available_strict_public_candidate_is_selected
    (available : ∃ word ∈ PublicPlan.candidates input depth count prefixLimit renewalLimit snapshot,
      Checks input depth count prefixLimit renewalLimit snapshot word) :
    ∃ selection, select input depth count prefixLimit renewalLimit snapshot = .selected selection := by
  cases produced : select input depth count prefixLimit renewalLimit snapshot with
  | selected selection => exact ⟨selection, rfl⟩
  | noStrict report =>
      obtain ⟨word, generated, checked⟩ := available
      exact ((report.issueAt word generated).refutes _ _ _ _ _ _ _ checked).elim

theorem no_strict_report_excludes_every_original_candidate
    (report : NoStrict input depth count prefixLimit renewalLimit snapshot)
    (word : RawEvent Party Good Port Technology Instrument)
    (generated : word ∈ PublicPlan.candidates input depth count prefixLimit renewalLimit snapshot) :
    ¬ Checks input depth count prefixLimit renewalLimit snapshot word :=
  (report.issueAt word generated).refutes _ _ _ _ _ _ _

theorem the_selected_source_improves_every_original_bearer_and_unit
    (selection : Selected input depth count prefixLimit renewalLimit snapshot) :
    (∀ person good, 0 ≤ Financial.delta input depth count prefixLimit renewalLimit snapshot.past
      (firstPeriod selection.rawWord) person good) ∧
    ∃ person good, 0 < Financial.delta input depth count prefixLimit renewalLimit snapshot.past
      (firstPeriod selection.rawWord) person good :=
  ⟨all_original_bearers_and_goods_keep_their_full_account_share input depth count prefixLimit renewalLimit
      snapshot.past (firstPeriod selection.rawWord) selection.strict,
    one_original_bearer_and_unit_has_strict_full_account_gain input depth count prefixLimit renewalLimit
      snapshot.past (firstPeriod selection.rawWord) selection.strict⟩

#print axioms select
#print axioms an_available_complete_replacement_is_selected
#print axioms an_actually_selected_replacement_has_a_future_when_a_complete_one_is_available
#print axioms an_available_strict_public_candidate_is_selected
#print axioms no_strict_report_excludes_every_original_candidate
#print axioms the_selected_source_improves_every_original_bearer_and_unit

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference
