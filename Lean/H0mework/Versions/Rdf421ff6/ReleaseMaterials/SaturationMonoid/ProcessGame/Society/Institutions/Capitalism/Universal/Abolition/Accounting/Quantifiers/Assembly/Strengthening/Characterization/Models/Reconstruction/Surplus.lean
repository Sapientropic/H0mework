import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Reconstruction.Kernel
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Reconstruction

open Source.Program Source.ProgrammeControl
universe u
noncomputable section
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

/-- Consumption, investment, retention, controlled routing and financial
return remain the original evidence constructors and original source checks. -/
theorem every_raw_appropriation_mode_has_an_exact_original_compiler_disposition
    (proposal : Kernel.Proposal law current word)
    (evidence : Kernel.ActualSurplus.Evidence law current word) :
    (∃ witness : Kernel.ActualSurplus.Witness law current word,
      Kernel.ActualSurplus.compileProposal law current word proposal evidence = some witness ∧
      witness.dependency.proposal = proposal ∧ witness.evidence = evidence) ∨
    Kernel.compile law current word proposal = none ∨
    ¬ Kernel.ActualSurplus.rawChecks law current word proposal evidence := by
  cases generated : Kernel.compile law current word proposal with
  | none => exact Or.inr (Or.inl rfl)
  | some dependency =>
      have same := the_original_checker_retains_the_exact_raw_proposal law current word proposal dependency generated
      by_cases checked : Kernel.ActualSurplus.rawChecks law current word dependency.proposal evidence
      · let witness := (Kernel.ActualSurplus.compile law current word dependency evidence).get (by
          simp only [Kernel.ActualSurplus.compile,dif_pos checked];rfl)
        have actual : Kernel.ActualSurplus.compile law current word dependency evidence = some witness := by
          simp only [witness,Kernel.ActualSurplus.compile,dif_pos checked,Option.get_some]
        have retained := Kernel.ActualSurplus.compile_preserves_original_dependency law current word dependency evidence witness actual
        refine Or.inl ⟨witness,?_,retained.1 ▸ same,retained.2⟩
        simp only [Kernel.ActualSurplus.compileProposal,generated,Option.bind_some,actual]
      · exact Or.inr (Or.inr (same ▸ checked))

theorem every_actual_appropriation_is_reconstructed_as_the_same_original_witness
    (witness : Kernel.ActualSurplus.Witness law current word) :
    Kernel.ActualSurplus.compileProposal law current word witness.dependency.proposal witness.evidence = some witness := by
  rw [Kernel.ActualSurplus.compileProposal,
    every_existing_capital_is_exactly_reconstructed_by_its_original_source_checker]
  simp only [Option.bind_some]
  cases witness
  rename_i dependency evidence checked
  simp only [Kernel.ActualSurplus.compile,dif_pos checked]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Reconstruction
