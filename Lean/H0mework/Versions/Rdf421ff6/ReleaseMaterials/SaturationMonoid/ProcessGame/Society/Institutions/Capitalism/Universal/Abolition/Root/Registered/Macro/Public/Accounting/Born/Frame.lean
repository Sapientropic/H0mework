import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.First
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.NativeFrame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (origin : Accounting.Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start origin)

def nativeFrame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start where
  N := Born.N prior origin registered
  anchor := registered.admitted
  family := Born.family prior origin registered
  V := Source.V prior origin registered
  root := Source.livingRoot prior origin registered
  occurrence_eq_emitted := Source.occurrence_eq_emitted prior origin registered
  cursor := id
  support_exact := by
    intro current actual aligned
    change current = some actual at aligned
    subst current
    rfl
  successor := Source.successor prior origin registered
  cursor_next := by
    intro current actual aligned
    change current = some actual at aligned
    subst current
    exact (Source.successor_current prior origin registered (some actual))
  successor_destination := by
    intro current actual aligned
    change current = some actual at aligned
    subst current
    exact Source.successor_destination prior origin registered (some actual)
  entries_finite := Source.entry_finite prior origin registered
  successor_keys := Source.successor_keys prior origin registered

theorem the_running_born_frame_has_the_literal_financial_cursor :
    (nativeFrame prior origin registered).cursor
      (Source.firstVisit prior origin registered).current = some registered.next :=
  Source.first_visit_is_the_literal_registered_next prior origin registered

theorem the_pending_admission_is_not_a_second_financial_cursor :
    (nativeFrame prior origin registered).cursor
      (Source.initialVisit prior origin registered).current = none := rfl

#print axioms nativeFrame
#print axioms the_running_born_frame_has_the_literal_financial_cursor

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born
