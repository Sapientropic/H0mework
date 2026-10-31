import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Lookahead

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Renewal

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program
open Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

def successor (current : Physical.Cursor Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    Physical.Cursor Party Good Port Technology Instrument :=
  Physical.next (Physical.receive current (.execute word))

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem the_actual_prefix_is_extended_once
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    (successor current word).past = current.past ++ [.execute word] := rfl

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

def Checks (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  Adaptive.Checks input depth count prefixLimit renewalLimit oldPast current word ∧
    Financial.Checks input depth count prefixLimit renewalLimit oldPast (successor current word)

instance (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (Checks input depth count prefixLimit renewalLimit oldPast current word) := by
  unfold Checks
  infer_instance

abbrev PostFeasible (word : RawEvent Party Good Port Technology Instrument) :=
  Lookahead.Available input depth count prefixLimit renewalLimit oldPast (successor current word)

private def scopeFailure (word : RawEvent Party Good Port Technology Instrument)
    (unchecked : ¬ Adaptive.Checks input depth count prefixLimit renewalLimit oldPast current word) :
    Macro.Public.Scope.Failure input depth count prefixLimit renewalLimit oldPast current (.execute word) := by
  cases found : Macro.Public.Scope.inspect input depth count prefixLimit renewalLimit oldPast current (.execute word) with
  | rejected failed => exact failed
  | delegated absent => cases absent
  | accepted actual selected checked =>
      have same : actual = Adaptive.executable word := Option.some.inj selected.symm
      cases same
      exact False.elim (unchecked checked)

inductive Issue (word : RawEvent Party Good Port Technology Instrument) : Type
  | originalScope (unchecked : ¬ Adaptive.Checks input depth count prefixLimit renewalLimit oldPast current word)
      (failure : Macro.Public.Scope.Failure input depth count prefixLimit renewalLimit oldPast current (.execute word))
  | fullAccount (feasible : Adaptive.Checks input depth count prefixLimit renewalLimit oldPast current word)
      (issue : Financial.Issue input depth count prefixLimit renewalLimit oldPast (successor current word))

theorem Issue.refutes (word : RawEvent Party Good Port Technology Instrument)
    (issue : Issue input depth count prefixLimit renewalLimit oldPast current word) :
    ¬ Checks input depth count prefixLimit renewalLimit oldPast current word := by
  intro checked
  cases issue with
  | originalScope unchecked _failure => exact unchecked checked.1
  | fullAccount _feasible issue => exact issue.refutes _ _ _ _ _ _ _ checked.2

def explain (word : RawEvent Party Good Port Technology Instrument)
    (unchecked : ¬ Checks input depth count prefixLimit renewalLimit oldPast current word) :
    Issue input depth count prefixLimit renewalLimit oldPast current word :=
  if feasible : Adaptive.Checks input depth count prefixLimit renewalLimit oldPast current word then
    match Financial.check input depth count prefixLimit renewalLimit oldPast (successor current word) with
    | .accepted strict => False.elim (unchecked ⟨feasible, strict⟩)
    | .rejected issue => .fullAccount feasible issue
  else .originalScope feasible (scopeFailure input depth count prefixLimit renewalLimit oldPast current word feasible)

structure Selected where
  private mk ::
  rawWord : RawEvent Party Good Port Technology Instrument
  generated : rawWord ∈ Adaptive.candidates input depth count prefixLimit renewalLimit oldPast current
  checked : Adaptive.Checks input depth count prefixLimit renewalLimit oldPast current rawWord
  strict : Financial.Checks input depth count prefixLimit renewalLimit oldPast (successor current rawWord)

structure NoStrict where
  private mk ::
  issueAt : ∀ word ∈ Adaptive.candidates input depth count prefixLimit renewalLimit oldPast current,
    Issue input depth count prefixLimit renewalLimit oldPast current word

inductive Outcome : Type
  | selected (selection : Selected input depth count prefixLimit renewalLimit oldPast current)
  | noStrict (report : NoStrict input depth count prefixLimit renewalLimit oldPast current)

private def selectStrict : Outcome input depth count prefixLimit renewalLimit oldPast current :=
  match Material.inspectList (fun word => ¬ Checks input depth count prefixLimit renewalLimit oldPast current word)
      (Adaptive.candidates input depth count prefixLimit renewalLimit oldPast current) with
  | .failure word generated notUnchecked =>
      let checked := of_not_not notUnchecked
      .selected ⟨word, generated, checked.1, checked.2⟩
  | .clear excluded => .noStrict ⟨fun word present =>
      explain input depth count prefixLimit renewalLimit oldPast current word (excluded word present)⟩

/-- Reassess the actual source list and the same complete prefix. A strict
candidate with a current independent continuation is selected first. -/
def select : Outcome input depth count prefixLimit renewalLimit oldPast current :=
  match Material.inspectList (fun word => ¬ (Checks input depth count prefixLimit renewalLimit oldPast current word ∧
      PostFeasible input depth count prefixLimit renewalLimit oldPast current word))
      (Adaptive.candidates input depth count prefixLimit renewalLimit oldPast current) with
  | .failure word generated notUnchecked =>
      let checked := of_not_not notUnchecked
      .selected ⟨word, generated, checked.1.1, checked.1.2⟩
  | .clear _ => selectStrict input depth count prefixLimit renewalLimit oldPast current

theorem an_available_complete_extension_is_selected
    (available : ∃ word ∈ Adaptive.candidates input depth count prefixLimit renewalLimit oldPast current,
      Checks input depth count prefixLimit renewalLimit oldPast current word ∧
        PostFeasible input depth count prefixLimit renewalLimit oldPast current word) :
    ∃ selection, select input depth count prefixLimit renewalLimit oldPast current = .selected selection ∧
      PostFeasible input depth count prefixLimit renewalLimit oldPast current selection.rawWord := by
  unfold select
  split
  · rename_i word generated notUnchecked _inspected
    exact ⟨_, rfl, (of_not_not notUnchecked).2⟩
  · rename_i excluded _inspected
    obtain ⟨word, generated, checked⟩ := available
    exact False.elim (excluded word generated checked)

theorem an_actually_selected_extension_has_a_future_when_a_complete_one_is_available
    (available : ∃ word ∈ Adaptive.candidates input depth count prefixLimit renewalLimit oldPast current,
      Checks input depth count prefixLimit renewalLimit oldPast current word ∧
        PostFeasible input depth count prefixLimit renewalLimit oldPast current word)
    (selection : Selected input depth count prefixLimit renewalLimit oldPast current)
    (actual : select input depth count prefixLimit renewalLimit oldPast current = .selected selection) :
    PostFeasible input depth count prefixLimit renewalLimit oldPast current selection.rawWord := by
  obtain ⟨selected, produced, future⟩ := an_available_complete_extension_is_selected
    input depth count prefixLimit renewalLimit oldPast current available
  have same : selected = selection := Outcome.selected.inj (produced.symm.trans actual)
  exact same ▸ future

theorem an_available_strict_candidate_at_the_actual_cut_is_selected
    (available : ∃ word ∈ Adaptive.candidates input depth count prefixLimit renewalLimit oldPast current,
      Checks input depth count prefixLimit renewalLimit oldPast current word) :
    ∃ selection, select input depth count prefixLimit renewalLimit oldPast current = .selected selection := by
  cases produced : select input depth count prefixLimit renewalLimit oldPast current with
  | selected selection => exact ⟨selection, rfl⟩
  | noStrict report =>
      obtain ⟨word, generated, checked⟩ := available
      exact ((report.issueAt word generated).refutes _ _ _ _ _ _ _ _ checked).elim

theorem no_strict_report_keeps_every_original_candidate_issue
    (report : NoStrict input depth count prefixLimit renewalLimit oldPast current)
    (word : RawEvent Party Good Port Technology Instrument)
    (generated : word ∈ Adaptive.candidates input depth count prefixLimit renewalLimit oldPast current) :
    ¬ Checks input depth count prefixLimit renewalLimit oldPast current word :=
  (report.issueAt word generated).refutes _ _ _ _ _ _ _ _

theorem the_selected_extension_improves_every_original_bearer_and_unit
    (selection : Selected input depth count prefixLimit renewalLimit oldPast current) :
    (∀ person good, 0 ≤ Financial.delta input depth count prefixLimit renewalLimit oldPast
      (successor current selection.rawWord) person good) ∧
    ∃ person good, 0 < Financial.delta input depth count prefixLimit renewalLimit oldPast
      (successor current selection.rawWord) person good :=
  ⟨all_original_bearers_and_goods_keep_their_full_account_share input depth count prefixLimit renewalLimit
      oldPast (successor current selection.rawWord) selection.strict,
    one_original_bearer_and_unit_has_strict_full_account_gain input depth count prefixLimit renewalLimit
      oldPast (successor current selection.rawWord) selection.strict⟩

#print axioms select
#print axioms an_available_complete_extension_is_selected
#print axioms an_actually_selected_extension_has_a_future_when_a_complete_one_is_available
#print axioms the_actual_prefix_is_extended_once
#print axioms an_available_strict_candidate_at_the_actual_cut_is_selected
#print axioms no_strict_report_keeps_every_original_candidate_issue
#print axioms the_selected_extension_improves_every_original_bearer_and_unit

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Renewal
