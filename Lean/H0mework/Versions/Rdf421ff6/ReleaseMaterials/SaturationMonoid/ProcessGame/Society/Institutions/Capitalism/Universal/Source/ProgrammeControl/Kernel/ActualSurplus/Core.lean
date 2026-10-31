import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Checks

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

/-- The old kernel supplies the actual dependence and a disposal right;
the separate evidence is an original actual appropriation, not that quote. -/
structure Witness where
  private mk ::
  dependency : CapitalRelationKernel law current word
  evidence : Evidence law current word
  checked : rawChecks law current word dependency.proposal evidence

def compile (dependency : CapitalRelationKernel law current word)
    (evidence : Evidence law current word) : Option (Witness law current word) :=
  if checked : rawChecks law current word dependency.proposal evidence then
    some ⟨dependency, evidence, checked⟩ else none

def compileProposal (proposal : Proposal law current word)
    (evidence : Evidence law current word) : Option (Witness law current word) :=
  (Kernel.compile law current word proposal).bind (fun dependency => compile law current word dependency evidence)

theorem compile_preserves_original_dependency (dependency : CapitalRelationKernel law current word)
    (evidence : Evidence law current word) (witness : Witness law current word)
    (generated : compile law current word dependency evidence = some witness) :
    witness.dependency = dependency ∧ witness.evidence = evidence := by
  unfold compile at generated
  split at generated
  · cases Option.some.inj generated
    exact ⟨rfl, rfl⟩
  · cases generated

namespace Witness
variable (witness : Witness law current word)

omit [DecidableEq Port] in
theorem no_material_allocation_as_title : witness.dependency.proposal.disposal.allocations = [] :=
  witness.checked.1

omit [DecidableEq Port] in
theorem actual_acquisition_cell :
    witness.dependency.proposal.access.mode = .acquired ∧
    0 < flowAt (law.actualCredit witness.dependency.proposal.access.access.val.before
      witness.dependency.proposal.access.access.val.request)
      witness.dependency.proposal.access.accessHolder witness.dependency.proposal.access.accessGood := by
  have basis := witness.checked.2.1
  have acquiredMode : witness.dependency.proposal.access.mode = .acquired := by
    cases selected : witness.evidence <;>
      simp only [selected, outputBasis, ownedOutput] at basis
    all_goals first | exact basis.1 | exact basis
  have acquired := witness.dependency.checked.1.2.2.2.2.1
  unfold AccessProposal.Accessed at acquired
  rw [acquiredMode] at acquired
  exact ⟨acquiredMode, acquired.1⟩

omit [DecidableEq Port] in
theorem actual_appropriation_has_original_source :
    (∃ position : OriginalItem law current word,
      witness.evidence = .consumption position ∧
      performedAt law position.val witness.dependency.proposal.access.port
        witness.dependency.proposal.access.accessHolder witness.dependency.proposal.access.accessGood) ∨
    (∃ position : OriginalItem law current word, ∃ growthGood,
      witness.evidence = .investment position growthGood ∧
      investedAt law position.val witness.dependency.proposal.access.port
        witness.dependency.proposal.access.accessHolder witness.dependency.proposal.access.accessGood growthGood) ∨
    (witness.evidence = .retention ∧ retainedOutput law current word witness.dependency.proposal.access) ∨
    (∃ position : OriginalItem law current word, ∃ good route,
      witness.evidence = .routedConsumption position good route ∧
      Follows law current word (witness.dependency.proposal.access.accessHolder,
        witness.dependency.proposal.access.accessGood) (witness.dependency.proposal.access.access.val.index + 1)
        route (law.controller position.val.before.technology witness.dependency.proposal.access.port, good)
        position.val.index ∧
      controlAlong law current word witness.dependency.proposal.access.port
        witness.dependency.proposal.access.recipient (witness.dependency.proposal.access.accessHolder,
          witness.dependency.proposal.access.accessGood) route ∧
      performedAt law position.val witness.dependency.proposal.access.port
        (law.controller position.val.before.technology witness.dependency.proposal.access.port) good) ∨
    (∃ path : Financial.ReturnPath law current word,
      witness.evidence = .financialReturn path ∧
      Financial.ReturnPath.Checks law current word witness.dependency.proposal.access path ∧
      witness.dependency.financialOrigin law current word = some (path.claimOrigin law current word)) := by
  have checked := witness.checked.2.2.1
  cases selected : witness.evidence with
  | consumption position =>
      simp only [selected, evidenceChecks] at checked
      exact Or.inl ⟨position, rfl, checked.2⟩
  | investment position growthGood =>
      simp only [selected, evidenceChecks] at checked
      exact Or.inr (Or.inl ⟨position, growthGood, rfl, checked.2⟩)
  | retention =>
      simp only [selected, evidenceChecks] at checked
      exact Or.inr (Or.inr (Or.inl ⟨rfl, checked⟩))
  | routedConsumption position good route =>
      simp only [selected, evidenceChecks] at checked
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨position, good, route, rfl, checked⟩)))
  | financialReturn path =>
      simp only [selected, evidenceChecks] at checked
      have aligned := witness.checked.2.2.2
      simp only [selected, financialAlignment] at aligned
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨path, rfl, checked,
        Financial.ReturnPath.aligned_is_exact_original_claim law current word path _ aligned⟩)))

end Witness

#print axioms compile
#print axioms Witness.actual_appropriation_has_original_source

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus
