import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Evolution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)

theorem every_actual_step_keeps_all_original_responsibility_keys
    (current : Current input depth count anchor) :
    Financial.Installation.KeepsKeys
      (wholeEvolution input depth count prefixLimit renewalLimit oldPast start family current) :=
  (evolutionWithKeys input depth count prefixLimit renewalLimit oldPast start family current).property

def currentFamily (current : Current input depth count anchor) :
    Epoch.Finance.Future.Continuation.AccountFamily input depth count world current.account :=
  family.after current.account current.native

theorem the_current_family_is_the_same_world_support
    (current : Current input depth count anchor) :
    (currentFamily input depth count family current).currentSupport = support input depth count family current := rfl

theorem the_next_native_run_updates_the_same_support
    (current : Current input depth count anchor) :
    (currentFamily input depth count family current).support
      (next input depth count prefixLimit renewalLimit oldPast start current).account
      ⟨nativeTransition input depth count prefixLimit renewalLimit oldPast start current⟩ =
        support input depth count family (next input depth count prefixLimit renewalLimit oldPast start current) := rfl

theorem every_current_has_finitely_many_original_open_rows
    (current : Current input depth count anchor) :
    Finite (OpenResponsibilityAt world (support input depth count family current)) :=
  family.entries_finite current.account current.native

#print axioms every_actual_step_keeps_all_original_responsibility_keys
#print axioms the_next_native_run_updates_the_same_support
#print axioms every_current_has_finitely_many_original_open_rows

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
