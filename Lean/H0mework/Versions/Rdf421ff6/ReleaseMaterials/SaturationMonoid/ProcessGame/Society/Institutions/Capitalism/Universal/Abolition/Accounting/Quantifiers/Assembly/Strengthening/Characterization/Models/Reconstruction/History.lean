import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Family

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Reconstruction

open Source.Program Source.ProgrammeControl
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : History.Visit input)

/-- The source's original title/retention/consumption/investment sum is
not replaced by a finite list of example economies. -/
theorem every_historical_mode_is_compiled_or_retains_an_exact_failed_source_guard
    (access : History.Access input endpoint) (reciprocal : History.Reciprocity input endpoint)
    (disposal : History.Disposal input endpoint) (evidence : History.Evidence input endpoint access) :
    (∃ capital : History.Capital input endpoint,
      History.compile input endpoint access reciprocal disposal evidence = some capital) ∨
    ¬ (access.Checks input endpoint ∧ reciprocal.Checks input endpoint access ∧ disposal.Checks input endpoint access) ∨
    ¬ evidence.Checks input endpoint access := by
  by_cases structural : access.Checks input endpoint ∧ reciprocal.Checks input endpoint access ∧ disposal.Checks input endpoint access
  · by_cases actual : evidence.Checks input endpoint access
    · let capital := (History.compile input endpoint access reciprocal disposal evidence).get (by
        simp only [History.compile,dif_pos structural,dif_pos actual];rfl)
      exact Or.inl ⟨capital,by simp only [capital,History.compile,dif_pos structural,dif_pos actual,Option.get_some]⟩
    · exact Or.inr (Or.inr actual)
  · exact Or.inr (Or.inl structural)

theorem every_historical_capital_is_reconstructed_with_its_exact_original_occurrence_fields
    (capital : History.Capital input endpoint) :
    History.compile input endpoint capital.access capital.reciprocity capital.disposal capital.evidence = some capital := by
  cases capital
  rename_i access reciprocal disposal checked evidence actual
  simp only [History.compile,dif_pos checked,dif_pos actual]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Reconstruction
