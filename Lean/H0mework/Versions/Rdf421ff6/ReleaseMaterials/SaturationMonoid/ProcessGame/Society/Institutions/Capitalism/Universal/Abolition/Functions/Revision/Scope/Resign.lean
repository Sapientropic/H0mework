import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.Public

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Scope

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

/-- At the first paid cut the old scope has already checked every actual
instruction. Its public word is a direct resign, with no refusal filter. -/
theorem the_checked_source_word_is_its_direct_public_resign
    (checked : ∀ item ∈ law.rawItems current word, law.Valid item.before item.request) :
    Replay.wordAt law current word = word.map (fun request => request.resign request.signer) := by
  rw [Replay.replay_is_computed_from_the_original_actual_inventory law current 0 word]
  calc
    _ = (law.execute current 0 word).items.map (fun item => item.request.resign item.request.signer) := by
      apply List.map_congr_left
      intro item listed
      exact if_pos (checked item listed)
    _ = _ := by
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (fun request => request.resign request.signer)) (law.inventory_requests_exact current 0 word)

#print axioms the_checked_source_word_is_its_direct_public_resign

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Scope
