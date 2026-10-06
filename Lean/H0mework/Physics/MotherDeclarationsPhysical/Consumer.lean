import H0mework.Physics.MotherDeclarationsPhysical.CurrentFormation
import H0mework.Physics.MotherProgrammesFormationCauchy.Source

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRawCurrent

open StageNineCanonicalCauchyState StageNineSourceGeneratedMotherTimeCauchyFlow

noncomputable section

/-- The entire raw current is formed once, before every original positive-duration action. -/
theorem every_current_consumed (current : PhysicalCoverage.Current) :
    ∃ law : MotherPointwiseLaws.Law,
      readReal law = CurrentMaterial.observe current.1 current.2 ∧
      readCurrent law = current ∧
      ∀ elapsed : PhysicalCoverage.Duration,
        PhysicalCoverage.advance (readCurrent law) elapsed.val =
          (sourceGeneratedMotherTimeCauchyUpdate PhysicalCoverage.source elapsed.val current.1,
            current.2 + elapsed.val) ∧
        type_of% (PhysicalCoverage.event_consumed PhysicalCoverage.originalInitial
          (readCurrent law) elapsed) := by
  obtain ⟨law, reads, recovered⟩ := every_current current
  refine ⟨law, reads, recovered, fun elapsed => ⟨?_, ?_⟩⟩
  · rw [recovered]
    rfl
  · exact PhysicalCoverage.event_consumed PhysicalCoverage.originalInitial
      (readCurrent law) elapsed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRawCurrent
