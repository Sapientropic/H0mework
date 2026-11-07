import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive.Compiler
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix

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

def absoluteCursor := Physical.receive (Physical.Prefix.cursor (oldPast ++ current.past)) current.incoming

theorem the_reader_is_the_exact_current_source_selection
    (original : Macro.Raw.Reader input depth count)
    (account : (Epoch.Finance.process input depth count).GeneratedState) :
    reader input depth count prefixLimit renewalLimit oldPast original (absoluteCursor oldPast current) account =
      selectedRaw input depth count prefixLimit renewalLimit oldPast current
        (original (absoluteCursor oldPast current) account) := by
  simp only [reader, absoluteCursor, localizing_the_source_cursor_keeps_the_literal_public_prefix]

theorem explicit_proposals_keep_their_exact_source
    (raw : Compile.RawInput Party Good Port Technology Instrument) (explicit : raw ≠ .advance) :
    selectedRaw input depth count prefixLimit renewalLimit oldPast current raw = raw := by
  cases raw <;> first | exact False.elim (explicit rfl) | rfl

theorem the_selected_word_passes_the_actual_full_current_guard
    (plan : Plan input depth count prefixLimit renewalLimit oldPast current) :
    Macro.Public.Scope.executionRaw input depth count prefixLimit renewalLimit oldPast current
      (.execute plan.rawWord) = .execute plan.rawWord :=
  (Macro.Public.Scope.every_checked_period_executes_the_original_proposal input depth count prefixLimit renewalLimit
    oldPast current (.execute plan.rawWord) (executable plan.rawWord) rfl plan.checked).1

theorem the_actual_public_period_is_accepted
    (plan : Plan input depth count prefixLimit renewalLimit oldPast current) :
    (Physical.Public.resultAt input depth count prefixLimit renewalLimit oldPast
      (Physical.receive current (.execute plan.rawWord))).isAccepted = true := by
  cases produced : Physical.Public.resultAt input depth count prefixLimit renewalLimit oldPast
      (Physical.receive current (.execute plan.rawWord)) with
  | accepted word selected checked => rfl
  | refused word selected item listed failed =>
      have same : word = executable plan.rawWord := Option.some.inj selected.symm
      cases same
      exact False.elim (failed (plan.checked.2.2.1 item listed).1)
  | metadata absent => cases absent

theorem the_selected_word_pays_every_current_member
    (plan : Plan input depth count prefixLimit renewalLimit oldPast current)
    (person : Party) (present : person ∈ Epoch.Interface.Actors.PublicCensus.parties input depth count
      prefixLimit renewalLimit oldPast current) :
    Exit.Necessity.BundlePaid (Physical.Public.interpreter input)
      (actualState input depth count prefixLimit renewalLimit oldPast current).raw (executable plan.rawWord) person
      (input.law.necessities (actualState input depth count prefixLimit renewalLimit oldPast current).raw person) .necessity ∧
    Exit.Necessity.BundlePaid (Physical.Public.interpreter input)
      (actualState input depth count prefixLimit renewalLimit oldPast current).raw (executable plan.rawWord) person
      (input.law.mandatoryMaintenance (actualState input depth count prefixLimit renewalLimit oldPast current).raw person) .maintenance :=
  plan.checked.2.2.2.1 person
    (Macro.Public.Scope.every_current_standing_is_checked input depth count prefixLimit renewalLimit oldPast current
      (executable plan.rawWord) person present)

#print axioms the_reader_is_the_exact_current_source_selection
#print axioms the_actual_public_period_is_accepted
#print axioms the_selected_word_pays_every_current_member

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive
