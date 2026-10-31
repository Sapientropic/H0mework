import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Inventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Complete

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

abbrev Fibre := frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt cut

def supportAt (phase : Option frame.V.Current) (origin : Fibre frame cut) : frame.N.Support :=
  match phase with
  | none => origin.1
  | some current => frame.sourceSupport current

def next : Option frame.V.Current → Option frame.V.Current
  | none => some cut
  | some current => some (frame.successor current).targetCurrent

def evolution (phase : Option frame.V.Current) (origin : Fibre frame cut) :
    LedgerWriteEvolutionAt frame.N ⟨supportAt frame cut phase origin⟩ ⟨supportAt frame cut (next frame cut phase) origin⟩ := by
  cases phase with
  | none =>
      cases frame.occurrence_eq_emitted origin
      exact LedgerWriteEvolutionAt.identity _
  | some current => exact frame.wholeEvolution current

def writes : Option frame.V.Current → Bool
  | none => true
  | some current => match frame.root.toAuthoritativeRoot.toRoot.evolutionAt current with
    | .continuedTransport _ => false
    | _ => true

def code : Sparse.Compiler.Code frame.N where
  Current := Option frame.V.Current
  Fibre := Fibre frame cut
  emission := frame.root.emitted cut
  initial := none
  supportAt := supportAt frame cut
  anchor_coherent := by intro phase origin; cases phase <;> first | rfl | cases frame.occurrence_eq_emitted origin; rfl
  incidence_coherent := by intro phase origin; cases phase <;> first | rfl | cases frame.occurrence_eq_emitted origin; rfl
  lineage_coherent := by intro phase origin; cases phase <;> first | rfl | cases frame.occurrence_eq_emitted origin; rfl
  next := next frame cut
  writes := writes frame
  evolution := evolution frame cut
  inverse_origin := by
    intro phase origin entry
    cases phase with
    | none => cases frame.occurrence_eq_emitted origin; rfl
    | some current =>
        apply Financial.Installation.entry_eq_of_key _ _
        · exact ((frame.whole_keys current).1 _).trans ((frame.whole_keys current).2 entry)
        · exact frame.family.open_fibres _
  inverse_destination := by
    intro phase origin entry
    cases phase with
    | none => cases frame.occurrence_eq_emitted origin; rfl
    | some current =>
        apply Financial.Installation.entry_eq_of_key _ _
        · exact ((frame.whole_keys current).2 _).trans ((frame.whole_keys current).1 entry)
        · exact frame.family.open_fibres _

theorem ingress_does_not_execute_an_old_item :
    (code frame cut).next none = some cut := rfl

theorem each_live_step_is_the_original_native_next (current : frame.V.Current) :
    (code frame cut).next (some current) = some (frame.successor current).targetCurrent := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix
