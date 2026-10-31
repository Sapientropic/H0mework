import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicPast
import Mathlib.Data.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicCensus

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))

abbrev Input := Compile.RawInput Party Good Port Technology Instrument

def eventParties (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : List Party :=
  actualParties input depth count (PublicPast.eventTag input depth count prefixLimit renewalLimit oldPast past raw)
    (PublicPast.eventVisit input depth count prefixLimit renewalLimit oldPast past raw)

theorem event_lookup_iff
    (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (party : Party) :
    (PublicPast.atEvent input depth count prefixLimit renewalLimit oldPast past raw party).isSome = true ↔
      party ∈ eventParties input depth count prefixLimit renewalLimit oldPast past raw := by
  unfold PublicPast.atEvent
  split
  next present => exact ⟨fun _ => present, fun _ => rfl⟩
  next absent => exact ⟨fun impossible => Bool.noConfusion impossible, fun member => (absent member).elim⟩

theorem scan_lookup_iff
    (past remaining : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (party : Party) :
    (PublicPast.scan input depth count prefixLimit renewalLimit oldPast past remaining party).isSome = true ↔
      ∃ position : Fin remaining.length,
        party ∈ eventParties input depth count prefixLimit renewalLimit oldPast
          (past ++ remaining.take position.val) (remaining.get position) := by
  induction remaining generalizing past with
  | nil => simp [PublicPast.scan]
  | cons raw remaining ih =>
      have next := ih (past ++ [raw])
      have head := event_lookup_iff input depth count prefixLimit renewalLimit oldPast past raw party
      simp only [PublicPast.scan, List.length_cons, Fin.exists_fin_succ,
        Fin.val_zero, List.take_zero, List.append_nil, List.get_eq_getElem,
        Fin.val_succ, List.take_succ_cons, List.getElem_cons_zero, List.getElem_cons_succ]
      have tailEq : (∃ position : Fin remaining.length,
          party ∈ eventParties input depth count prefixLimit renewalLimit oldPast
            (past ++ raw :: remaining.take position.val) remaining[position.val]) ↔
          (PublicPast.scan input depth count prefixLimit renewalLimit oldPast (past ++ [raw]) remaining party).isSome = true := by
        simpa only [List.append_assoc, List.singleton_append, List.get_eq_getElem] using next.symm
      rw [tailEq, ← head]
      cases PublicPast.atEvent input depth count prefixLimit renewalLimit oldPast past raw party <;> simp


#print axioms scan_lookup_iff

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicCensus
