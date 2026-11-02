import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Epoch.Admissions

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count prefixLimit renewalLimit : Nat)

theorem actual_past_adds_exactly_its_source_origins (prior past)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    origins input depth count (Epoch.Finance.ActualPast.foldFrom input depth count prefixLimit renewalLimit prior past before) =
      origins input depth count before ++
        (stream input depth count prefixLimit renewalLimit none prior past).filterMap (emittedOrigin? input depth count) := by
  induction past generalizing prior before with
  | nil => simp only [Epoch.Finance.ActualPast.foldFrom,stream,List.filterMap_nil,List.append_nil]
  | cons raw rest inherited =>
      rw [Epoch.Finance.ActualPast.foldFrom,inherited,every_visit_adds_exactly_its_source_emitted_origins]
      simp only [stream,List.filterMap_append,List.append_assoc,atInput]

theorem public_past_adds_exactly_its_source_origins (oldPast prior past)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    origins input depth count (Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit oldPast prior past before) =
      origins input depth count before ++
        (stream input depth count prefixLimit renewalLimit (some oldPast) prior past).filterMap (emittedOrigin? input depth count) := by
  induction past generalizing prior before with
  | nil => simp only [Epoch.Finance.PublicPast.foldFrom,stream,List.filterMap_nil,List.append_nil]
  | cons raw rest inherited =>
      rw [Epoch.Finance.PublicPast.foldFrom,inherited,every_visit_adds_exactly_its_source_emitted_origins]
      simp only [stream,List.filterMap_append,List.append_assoc,atInput]

theorem actual_and_public_pasts_have_disjoint_original_occurrences (oldPast newPast) :
    (stream input depth count prefixLimit renewalLimit none [] oldPast ++
      stream input depth count prefixLimit renewalLimit (some oldPast) [] newPast).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨the_entire_actual_input_past_never_replays_an_occurrence input depth count prefixLimit renewalLimit none [] oldPast,
    the_entire_actual_input_past_never_replays_an_occurrence input depth count prefixLimit renewalLimit (some oldPast) [] newPast,?_⟩
  intro first oldMember second publicMember same
  subst second
  obtain ⟨oldPosition,_,oldStamp⟩ := every_later_item_has_a_later_original_past input depth count prefixLimit renewalLimit
    none [] oldPast first oldMember
  obtain ⟨newPosition,_,newStamp⟩ := every_later_item_has_a_later_original_past input depth count prefixLimit renewalLimit
    (some oldPast) [] newPast first publicMember
  have incompatible := congrArg Prod.fst (Option.some.inj (oldStamp.symm.trans newStamp))
  cases incompatible

theorem the_complete_actual_and_public_source_has_unique_emitted_origins (oldPast newPast) :
    ((stream input depth count prefixLimit renewalLimit none [] oldPast ++
      stream input depth count prefixLimit renewalLimit (some oldPast) [] newPast).filterMap
        (emittedOrigin? input depth count)).Nodup :=
  emitted_origins_never_duplicate_the_source_items input depth count _
    (actual_and_public_pasts_have_disjoint_original_occurrences input depth count prefixLimit renewalLimit oldPast newPast)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory
