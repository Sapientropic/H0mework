import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Control

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {snapshot : Physical.Cursor Party Good Port Technology Instrument}
  (plan : Plan input depth count prefixLimit renewalLimit snapshot)

def firstCursor := Physical.receive publicStart (.execute plan.rawWord)

theorem the_original_full_current_guard_selects_this_public_word :
    Macro.Public.Scope.executionRaw input depth count prefixLimit renewalLimit snapshot.past publicStart
      (.execute plan.rawWord) = .execute plan.rawWord :=
  (Macro.Public.Scope.every_checked_period_executes_the_original_proposal input depth count prefixLimit renewalLimit
    snapshot.past publicStart (.execute plan.rawWord) (executable plan.rawWord) rfl plan.checked).1

theorem the_actual_public_first_period_is_accepted :
    (Physical.Public.resultAt input depth count prefixLimit renewalLimit snapshot.past (firstCursor plan)).isAccepted = true := by
  cases produced : Physical.Public.resultAt input depth count prefixLimit renewalLimit snapshot.past (firstCursor plan) with
  | accepted word selected checked => rfl
  | refused word selected item listed failed =>
      have same : word = executable plan.rawWord := Option.some.inj selected.symm
      cases same
      exact False.elim (failed (plan.checked.2.2.1 item listed).1)
  | metadata absent => cases absent

theorem the_public_word_pays_each_original_member
    (person : Party) (present : person ∈ Epoch.Interface.Actors.Census.parties input depth count
      prefixLimit renewalLimit (Physical.Prefix.cursor snapshot.past)) :
    Exit.Necessity.BundlePaid (Physical.Public.interpreter input)
      (oldCurrent input depth count prefixLimit renewalLimit snapshot).raw (executable plan.rawWord) person
      (input.law.necessities (oldCurrent input depth count prefixLimit renewalLimit snapshot).raw person) .necessity ∧
    Exit.Necessity.BundlePaid (Physical.Public.interpreter input)
      (oldCurrent input depth count prefixLimit renewalLimit snapshot).raw (executable plan.rawWord) person
      (input.law.mandatoryMaintenance (oldCurrent input depth count prefixLimit renewalLimit snapshot).raw person) .maintenance :=
  plan.checked.2.2.2.1 person
    (every_actual_member_is_checked input depth count prefixLimit renewalLimit snapshot plan.rawWord person present)

#print axioms the_actual_public_first_period_is_accepted
#print axioms the_public_word_pays_each_original_member

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan
