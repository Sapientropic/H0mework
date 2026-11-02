import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.PublicPast.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.ActualPast.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count prefixLimit renewalLimit : Nat)

abbrev Input := Registered.Compile.RawInput Party Good Port Technology Instrument
abbrev Item := Epoch.Finance.ActualItem input depth count

/-- An audit read of an existing original occurrence, never an identity supplied
to the source. The full source tag and full past remain in the original item. -/
def stamp : Item input depth count → Option (Bool × Nat)
  | ⟨.actual _ _ _,visit,_⟩ => some (false,visit.current.past.length)
  | ⟨.publicActual _ _ _ _,visit,_⟩ => some (true,visit.current.past.length)
  | _ => none

def phase (oldPast : Option (List (Input (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)))) : Bool := oldPast.isSome

def atInput (oldPast : Option (List (Input (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))))
    (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    List (Item input depth count) := match oldPast with
  | none => Epoch.Finance.inventory input depth count
      (Epoch.Interface.ActualOccurrence.eventTag input depth count prefixLimit renewalLimit past raw)
      (Epoch.Interface.ActualOccurrence.eventVisit input depth count prefixLimit renewalLimit past raw)
  | some old => Epoch.Finance.inventory input depth count
      (Epoch.Interface.Actors.PublicPast.eventTag input depth count prefixLimit renewalLimit old past raw)
      (Epoch.Interface.Actors.PublicPast.eventVisit input depth count prefixLimit renewalLimit old past raw)

def stream (oldPast : Option (List (Input (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))))
    (prior : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) :
    List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) →
      List (Item input depth count)
  | [] => []
  | raw :: rest => atInput input depth count prefixLimit renewalLimit oldPast prior raw ++
      stream oldPast (prior ++ [raw]) rest

theorem each_input_has_its_literal_past_position (oldPast prior raw)
    (item : Item input depth count)
    (member : item ∈ atInput input depth count prefixLimit renewalLimit oldPast prior raw) :
    stamp input depth count item = some (phase oldPast,prior.length) := by
  cases oldPast with
  | none =>
      obtain ⟨position,same⟩ := List.mem_ofFn.mp member
      subst item
      change some (false,(Registered.Physical.Prefix.cursor prior).past.length) = some (phase none,prior.length)
      rw [Registered.Physical.Prefix.past_readback]
      rfl
  | some old =>
      obtain ⟨position,same⟩ := List.mem_ofFn.mp member
      subst item
      change some (true,(Registered.Physical.Prefix.cursor prior).past.length) = some (phase (some old),prior.length)
      rw [Registered.Physical.Prefix.past_readback]
      rfl

theorem every_later_item_has_a_later_original_past (oldPast prior past)
    (item : Item input depth count)
    (member : item ∈ stream input depth count prefixLimit renewalLimit oldPast prior past) :
    ∃ n,prior.length ≤ n ∧ stamp input depth count item = some (phase oldPast,n) := by
  induction past generalizing prior with
  | nil => cases member
  | cons raw rest ih =>
      rcases List.mem_append.mp member with first | later
      · exact ⟨prior.length,le_refl _,each_input_has_its_literal_past_position input depth count prefixLimit renewalLimit
          oldPast prior raw item first⟩
      · obtain ⟨n,bound,same⟩ := ih (prior ++ [raw]) later
        exact ⟨n,by simp only [List.length_append,List.length_singleton] at bound; omega,same⟩

theorem the_entire_actual_input_past_never_replays_an_occurrence (oldPast prior past) :
    (stream input depth count prefixLimit renewalLimit oldPast prior past).Nodup := by
  induction past generalizing prior with
  | nil => exact List.nodup_nil
  | cons raw rest ih =>
      apply List.nodup_append.mpr
      refine ⟨?_,ih (prior ++ [raw]),?_⟩
      · cases oldPast <;> exact Epoch.Finance.inventory_positions_are_not_replayed input depth count _ _
      · intro item first next later sameItem
        subst next
        have original := each_input_has_its_literal_past_position input depth count prefixLimit renewalLimit oldPast prior raw item first
        obtain ⟨n,bound,subsequent⟩ := every_later_item_has_a_later_original_past input depth count prefixLimit renewalLimit
          oldPast (prior ++ [raw]) rest item later
        have same := Option.some.inj (original.symm.trans subsequent)
        have index := congrArg Prod.snd same
        simp only [List.length_append,List.length_singleton] at bound
        omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory
