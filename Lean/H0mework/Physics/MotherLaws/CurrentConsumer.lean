import H0mework.Physics.MotherLaws.CurrentRecovery
import H0mework.Physics.MotherLaws.CurrentSmooth
import H0mework.Physics.MotherLaws.StreamCompletion

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction

open CurrentMaterial StageNineCanonicalCauchyState StageNineEnrichedProofFreeSource
open StageNineSourceGeneratedMotherTimeCauchyFlow
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

/-- This inverse belongs to the existing complete mother-material readout. -/
def materialEquiv : MotherStreamFormation.Carrier ≃ MotherStreamLaws.Stream :=
  Equiv.ofBijective MotherStreamFormation.read
    ⟨MotherStreamFormation.read_inducing.isInducing.injective,
      MotherStreamFormation.read_surjective⟩

def readInverse (samples : MotherStreamLaws.Stream) : MotherStreamFormation.Carrier :=
  materialEquiv.symm samples

theorem read_readInverse (samples : MotherStreamLaws.Stream) :
    MotherStreamFormation.read (readInverse samples) = samples :=
  materialEquiv.apply_symm_apply samples

theorem readInverse_read (material : MotherStreamFormation.Carrier) :
    readInverse (MotherStreamFormation.read material) = material :=
  materialEquiv.symm_apply_apply material

def evaluate (law : MotherStreamLaws.Law) (material : MotherStreamFormation.Carrier) :
    MotherStreamFormation.Carrier :=
  readInverse (MotherStreamLaws.eval law (MotherStreamFormation.read material))

theorem read_evaluate (law : MotherStreamLaws.Law) (material : MotherStreamFormation.Carrier) :
    MotherStreamFormation.read (evaluate law material) =
      MotherStreamLaws.eval law (MotherStreamFormation.read material) :=
  read_readInverse _

/-- The source and time fix one completed law before any initial current or
query. Its value restores the original complete physical action and clock. -/
theorem source_time_law (source : SmoothUnifiedSource) (time : ℝ) :
    ∃ law : MotherStreamLaws.Law,
      MotherStreamLaws.lawRead law = ⟨updateSamples source time, updateSamples_continuous source time⟩ ∧
      ∀ (initial : StageNineCauchyState) (clock : ℝ), ActualInitial.SmoothInitial initial →
      ∃ before : MotherStreamFormation.Carrier,
        MotherStreamFormation.read before = currentSamples initial clock ∧
        decodeCurrent before = (initial, clock) ∧
        MotherStreamFormation.read (evaluate law before) =
          currentSamples (sourceGeneratedMotherTimeCauchyUpdate source time initial) (clock + time) ∧
        decodeCurrent (evaluate law before) =
          (sourceGeneratedMotherTimeCauchyUpdate source time initial, clock + time) := by
  obtain ⟨law, generated, _⟩ := MotherStreamLaws.every_continuous_law
    ⟨updateSamples source time, updateSamples_continuous source time⟩
  refine ⟨law, generated, ?_⟩
  intro initial clock smooth
  obtain ⟨before, beforeRead, beforeRecovered⟩ := entire_current_formed initial clock smooth
  have afterRead : MotherStreamFormation.read (evaluate law before) =
      currentSamples (sourceGeneratedMotherTimeCauchyUpdate source time initial) (clock + time) := by
    rw [read_evaluate, MotherStreamLaws.eval_eq, generated]
    change updateSamples source time (MotherStreamFormation.read before) = _
    rw [beforeRead, updateSamples_actual]
  have afterSmooth := mother_time_preserves_smooth source time initial smooth
  exact ⟨before, beforeRead, beforeRecovered, afterRead,
    Prod.ext (decodeInitial_recovers _ _ afterSmooth afterRead) (decodeClock_recovers _ _ afterRead)⟩

/-- The formed law is consumed by the existing mother-time event and its
own complete ledger; no material/sourceStep or inquiry next is identified with it. -/
theorem native_source_time_law (elapsed : PhysicalCoverage.Duration) :
    ∃ law : MotherStreamLaws.Law,
      ∀ (initial : StageNineCauchyState) (clock : ℝ), ActualInitial.SmoothInitial initial →
      ∃ before : MotherStreamFormation.Carrier,
        decodeCurrent before = (initial, clock) ∧
        decodeCurrent (evaluate law before) = PhysicalCoverage.advance (decodeCurrent before) elapsed.val ∧
        (RawGeneratedRoot.generatedSuccessor (PhysicalCoverage.dynamics initial)
          (state := decodeCurrent before) elapsed).targetCurrent = decodeCurrent (evaluate law before) ∧
        (RawGeneratedRoot.generatedSuccessor (PhysicalCoverage.dynamics initial)
          (state := decodeCurrent before) elapsed).ledgerEvolution.destination
            (RawGeneratedRoot.entry (PhysicalCoverage.dynamics initial) (decodeCurrent before)) =
          ⟨RawGeneratedRoot.entry (PhysicalCoverage.dynamics initial) (decodeCurrent (evaluate law before)),
            .transferred elapsed rfl rfl (Nat.le_refl _)⟩ := by
  obtain ⟨law, _, allCurrents⟩ := source_time_law PhysicalCoverage.source elapsed.val
  refine ⟨law, ?_⟩
  intro initial clock smooth
  obtain ⟨before, _, beforeRecovered, _, afterRecovered⟩ := allCurrents initial clock smooth
  have actual : decodeCurrent (evaluate law before) = PhysicalCoverage.advance (decodeCurrent before) elapsed.val := by
    rw [beforeRecovered, afterRecovered]
    rfl
  have consumed := PhysicalCoverage.event_consumed initial (decodeCurrent before) elapsed
  refine ⟨before, beforeRecovered, actual, consumed.2.1.trans actual.symm, ?_⟩
  rw [actual]
  exact consumed.2.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction
