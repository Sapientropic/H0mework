import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Core

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

theorem the_original_checker_retains_the_exact_raw_proposal
    (proposal : Kernel.Proposal law current word) (capital : Kernel.CapitalRelationKernel law current word)
    (compiled : Kernel.compile law current word proposal = some capital) : capital.proposal = proposal := by
  unfold Kernel.compile at compiled
  split at compiled
  · cases Option.some.inj compiled
    rfl
  · cases compiled

/-- All three original reciprocity constructors are handled by the same
source checker. A failure retains its exact original structural guard. -/
theorem every_raw_source_reconstruction_generates_capital_or_an_exact_failed_guard
    (proposal : Kernel.Proposal law current word) :
    (∃ capital : Kernel.CapitalRelationKernel law current word,
      Kernel.compile law current word proposal = some capital ∧ capital.proposal = proposal) ∨
    (¬ proposal.access.Checks law current word) ∨
    (¬ proposal.reciprocity.Checks law current word proposal.access) ∨
    (¬ proposal.disposal.Checks law current word proposal.access) := by
  by_cases access : proposal.access.Checks law current word
  · by_cases reciprocal : proposal.reciprocity.Checks law current word proposal.access
    · by_cases disposition : proposal.disposal.Checks law current word proposal.access
      · have checked : proposal.Checks law current word := ⟨access,reciprocal,disposition⟩
        let capital := (Kernel.compile law current word proposal).get (by
          simp only [Kernel.compile,dif_pos checked]; rfl)
        have compiled : Kernel.compile law current word proposal = some capital := by
          simp only [capital,Kernel.compile,dif_pos checked,Option.get_some]
        exact Or.inl ⟨capital,compiled,the_original_checker_retains_the_exact_raw_proposal law current word proposal capital compiled⟩
      · exact Or.inr (Or.inr (Or.inr disposition))
    · exact Or.inr (Or.inr (Or.inl reciprocal))
  · exact Or.inr (Or.inl access)

/-- This is a converse on the original sealed value, not a replacement
kernel with the same port or a newly chosen witness. -/
theorem every_existing_capital_is_exactly_reconstructed_by_its_original_source_checker
    (capital : Kernel.CapitalRelationKernel law current word) :
    Kernel.compile law current word capital.proposal = some capital := by
  cases capital
  rename_i proposal checked
  simp only [Kernel.compile,dif_pos checked]

theorem a_returned_capital_has_no_simultaneous_failed_source_guard
    (proposal : Kernel.Proposal law current word) (capital : Kernel.CapitalRelationKernel law current word)
    (compiled : Kernel.compile law current word proposal = some capital) :
    proposal.access.Checks law current word ∧
      proposal.reciprocity.Checks law current word proposal.access ∧
      proposal.disposal.Checks law current word proposal.access := by
  have exactProposal := the_original_checker_retains_the_exact_raw_proposal law current word proposal capital compiled
  simpa only [Kernel.Proposal.Checks,exactProposal] using capital.checked

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Reconstruction
