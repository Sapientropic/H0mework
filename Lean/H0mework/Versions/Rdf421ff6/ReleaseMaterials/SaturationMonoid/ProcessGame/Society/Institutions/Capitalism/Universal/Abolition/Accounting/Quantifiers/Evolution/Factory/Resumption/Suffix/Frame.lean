import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Abolition.Root.Registered.Macro.Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (cut : frame.V.Current)

def nativeFrame : Abolition.Root.Registered.Macro.Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start where
  N := frame.N
  anchor := frame.anchor
  family := frame.family
  V := Sparse.Compiler.V (code frame cut)
  root := root frame cut
  occurrence_eq_emitted := fun {phase} occurrence => by
    have same := frame.occurrence_eq_emitted (Sparse.Compiler.originalOccurrence (code frame cut) occurrence)
    exact (Sparse.Compiler.represented_original (code frame cut) occurrence).symm.trans
      (congrArg (Sparse.Compiler.represented (code frame cut) phase) same)
  cursor := cursor frame
  support_exact := by
    intro phase actual aligned
    cases phase with
    | none => cases aligned
    | some current => exact frame.support_exact current actual aligned
  successor := Sparse.Compiler.successor (code frame cut)
  cursor_next := by
    intro phase actual aligned
    cases phase with
    | none => cases aligned
    | some current => exact live_cursor_next frame cut current actual aligned
  successor_destination := by
    intro phase actual aligned
    cases phase with
    | none => cases aligned
    | some current => exact live_destination frame cut current actual aligned
  entries_finite := fun phase => by
    cases phase with
    | none => exact frame.entries_finite cut
    | some current => exact frame.entries_finite current
  successor_keys := successor_keys frame cut

theorem after_ingress_the_native_cursor_is_the_original_cut :
    (nativeFrame frame cut).cursor (Sparse.Compiler.successor (code frame cut) none).targetCurrent = frame.cursor cut :=
  congrArg (cursor frame) (Sparse.Compiler.successor_current (code frame cut) none)

theorem each_later_cursor_is_the_original_live_cursor (current : frame.V.Current) :
    (nativeFrame frame cut).cursor (some current) = frame.cursor current := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix
