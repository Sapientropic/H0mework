import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.NoControl

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program Source.ProgrammeControl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (snapshot : Physical.Cursor Party Good Port Technology Instrument)
  (visit : Epoch.Interface.Visit input depth count (.publicActual prefixLimit renewalLimit oldPast snapshot))

/-- This consumes the original factory's actual epoch, interpreter and body;
no old occurrence is reinterpreted under another Input. -/
theorem the_original_factory_public_occurrence_has_no_fresh_capital_kernel :
    ¬ Nonempty (Kernel.CapitalRelationKernel
      (Epoch.Interface.interpreter input depth count (.publicActual prefixLimit renewalLimit oldPast snapshot))
      (Epoch.Interface.body input depth count (.publicActual prefixLimit renewalLimit oldPast snapshot) visit).1
      (Epoch.Interface.body input depth count (.publicActual prefixLimit renewalLimit oldPast snapshot) visit).2) :=
  Functions.open_permissions_have_no_capital_kernel _ (fun _ _ _ => rfl) _ _

theorem the_original_factory_generates_no_title_or_actual_surplus_family
    (attempts : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (item : OriginalItem
      (Epoch.Interface.interpreter input depth count (.publicActual prefixLimit renewalLimit oldPast snapshot))
      (Epoch.Interface.body input depth count (.publicActual prefixLimit renewalLimit oldPast snapshot) visit).1
      (Epoch.Interface.body input depth count (.publicActual prefixLimit renewalLimit oldPast snapshot) visit).2) :
    Kernel.AssetAuthority.generatedFamily _ _ _ attempts item = [] ∧ Kernel.ActualSurplus.familyAt _ _ _ item = [] :=
  Functions.open_interpretation_generated_families_empty input.law _ _ attempts item

#print axioms the_original_factory_public_occurrence_has_no_fresh_capital_kernel
#print axioms the_original_factory_generates_no_title_or_actual_surplus_family

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital
