import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay

open Source.Program Exit

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (original : RawEvent Party Good Port Technology Instrument)

/-- A substituted presentation never pays an original use obligation.
Only an actually accepted source use can supply the matching replay use. -/
theorem original_payment_bundles_are_preserved_in_both_directions
    (person : Party) (goods : Bundle Good) (purpose : Use) :
    Necessity.BundlePaid (PublicFunction.physicalLaw law) current (wordAt law current original) person goods purpose ↔
      Necessity.BundlePaid law current original person goods purpose := by
  have items := (replay_execution_has_the_same_actual_currents law current 0 original).2
  change (PublicFunction.physicalLaw law).rawItems current (wordAt law current original) =
    (law.rawItems current original).map (itemAt law) at items
  constructor
  · rintro (empty | ⟨item, present, legal, matched⟩)
    · exact Or.inl empty
    · rw [items] at present
      obtain ⟨sourceItem, originalItem, rfl⟩ := List.mem_map.mp present
      by_cases accepted : law.Valid sourceItem.before sourceItem.request
      · refine Or.inr ⟨sourceItem, originalItem, accepted, ?_⟩
        simpa only [itemAt, requestAt, if_pos accepted, Request.resign] using matched
      · simp only [itemAt, requestAt, if_neg accepted, presentation, Necessity.UseMatches] at matched
  · rintro (empty | ⟨item, present, accepted, matched⟩)
    · exact Or.inl empty
    · refine Or.inr ⟨itemAt law item, ?_, the_computed_request_is_lawful law item.before item.request, ?_⟩
      · rw [items]
        exact List.mem_map.mpr ⟨item, present, rfl⟩
      · simpa only [itemAt, requestAt, if_pos accepted, Request.resign] using matched

theorem every_original_livelihood_and_maintenance_requirement_is_preserved (members : List Party) :
    Necessity.AllNeedsPaid (PublicFunction.physicalLaw law) current members (wordAt law current original) ↔
      Necessity.AllNeedsPaid law current members original := by
  constructor <;> intro paid person member
  · exact ⟨(original_payment_bundles_are_preserved_in_both_directions law current original person _ .necessity).mp (paid person member).1,
      (original_payment_bundles_are_preserved_in_both_directions law current original person _ .maintenance).mp (paid person member).2⟩
  · exact ⟨(original_payment_bundles_are_preserved_in_both_directions law current original person _ .necessity).mpr (paid person member).1,
      (original_payment_bundles_are_preserved_in_both_directions law current original person _ .maintenance).mpr (paid person member).2⟩

theorem original_services_keep_their_actual_bearers_bundles_and_windows
    (task : PublicFunction.PublicTaskSpec Party Good) :
    PublicFunction.ServiceAdequate (PublicFunction.physicalLaw law) current task (wordAt law current original) ↔
      PublicFunction.ServiceAdequate law current task original := by
  unfold PublicFunction.ServiceAdequate
  rw [replay_preserves_the_original_full_next]
  constructor <;> rintro ⟨earliest, deadline, paid⟩
  · exact ⟨earliest, deadline, fun slot member =>
      (original_payment_bundles_are_preserved_in_both_directions law current original slot.bearer slot.goods slot.purpose).mp
        (paid slot member)⟩
  · exact ⟨earliest, deadline, fun slot member =>
      (original_payment_bundles_are_preserved_in_both_directions law current original slot.bearer slot.goods slot.purpose).mpr
        (paid slot member)⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.original_payment_bundles_are_preserved_in_both_directions
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.original_services_keep_their_actual_bearers_bundles_and_windows
