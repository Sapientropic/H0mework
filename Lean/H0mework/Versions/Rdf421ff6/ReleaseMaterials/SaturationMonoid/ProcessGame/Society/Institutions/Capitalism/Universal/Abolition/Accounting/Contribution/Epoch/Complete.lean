import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Epoch.Accounts
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source.Legacy

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)

/-- The already installed account of the original registered frame. -/
abbrev registeredBase := Epoch.Finance.Legacy.generated input depth count
  ((Financial.Installation.Runtime.frames input sourceDepth sourceCount).cursor input).account

theorem every_registered_base_origin_is_an_original_source_origin
    (origin : Epoch.Finance.Origin input depth count)
    (member : origin ∈ origins input depth count (registeredBase input depth count sourceDepth sourceCount)) :
    ∃ original,origin = Epoch.Finance.Origin.original original := by
  unfold origins at member
  rw [(Epoch.Finance.Legacy.every_slot_and_history_entry_is_retained input depth count _).1,List.map_map] at member
  obtain ⟨slot,_included,rfl⟩ := List.mem_map.mp member
  cases slot <;> exact ⟨_,rfl⟩

theorem the_complete_account_has_exactly_its_original_and_actual_source_origins (oldPast newPast) :
    origins input depth count
      (Epoch.Finance.PublicPast.account input depth count prefixLimit renewalLimit oldPast newPast
        (Epoch.Finance.ActualPast.account input depth count prefixLimit renewalLimit oldPast
          (registeredBase input depth count sourceDepth sourceCount))) =
      origins input depth count (registeredBase input depth count sourceDepth sourceCount) ++
        (stream input depth count prefixLimit renewalLimit none [] oldPast ++
          stream input depth count prefixLimit renewalLimit (some oldPast) [] newPast).filterMap
            (emittedOrigin? input depth count) := by
  rw [Epoch.Finance.PublicPast.account,public_past_adds_exactly_its_source_origins,
    Epoch.Finance.ActualPast.account,actual_past_adds_exactly_its_source_origins]
  simp only [List.filterMap_append,List.append_assoc]

theorem the_complete_actual_account_cannot_reregister_an_original_contribution (oldPast newPast) :
    (origins input depth count
      (Epoch.Finance.PublicPast.account input depth count prefixLimit renewalLimit oldPast newPast
        (Epoch.Finance.ActualPast.account input depth count prefixLimit renewalLimit oldPast
          (registeredBase input depth count sourceDepth sourceCount)))).Nodup := by
  rw [the_complete_account_has_exactly_its_original_and_actual_source_origins]
  apply List.nodup_append.mpr
  refine ⟨Source.the_actual_translated_registered_account_has_one_slot_per_original_source input depth count sourceDepth sourceCount,
    the_complete_actual_and_public_source_has_unique_emitted_origins input depth count prefixLimit renewalLimit oldPast newPast,?_⟩
  intro original oldMember fresh freshMember same
  subst fresh
  obtain ⟨source,sourceEq⟩ := every_registered_base_origin_is_an_original_source_origin input depth count sourceDepth sourceCount original oldMember
  obtain ⟨item,_actual,emitted⟩ := List.mem_filterMap.mp freshMember
  have actualEq := an_emitted_origin_is_its_original_item input depth count item original emitted
  rw [sourceEq] at actualEq
  cases actualEq

theorem the_registered_public_account_cannot_reregister_an_original_contribution (oldPast newPast) :
    (origins input depth count
      (Epoch.Finance.PublicPast.account input depth count prefixLimit renewalLimit oldPast newPast
        (registeredBase input depth count sourceDepth sourceCount))).Nodup := by
  rw [Epoch.Finance.PublicPast.account,public_past_adds_exactly_its_source_origins]
  apply List.nodup_append.mpr
  refine ⟨Source.the_actual_translated_registered_account_has_one_slot_per_original_source input depth count sourceDepth sourceCount,
    emitted_origins_never_duplicate_the_source_items input depth count _
      (the_entire_actual_input_past_never_replays_an_occurrence input depth count prefixLimit renewalLimit (some oldPast) [] newPast),?_⟩
  intro original oldMember fresh freshMember same
  subst fresh
  obtain ⟨source,sourceEq⟩ := every_registered_base_origin_is_an_original_source_origin input depth count sourceDepth sourceCount original oldMember
  obtain ⟨item,_actual,emitted⟩ := List.mem_filterMap.mp freshMember
  have actualEq := an_emitted_origin_is_its_original_item input depth count item original emitted
  rw [sourceEq] at actualEq
  cases actualEq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory
