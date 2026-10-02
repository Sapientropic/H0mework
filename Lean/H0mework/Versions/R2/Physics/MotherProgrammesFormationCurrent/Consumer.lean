import H0mework.Versions.R2.Physics.MotherProgrammesFormationCurrent.Current
import H0mework.Versions.R2.Physics.MotherProgrammesFormationCauchy.Source

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentMaterial

open StageNineCanonicalCauchyState StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineSourceGeneratedMotherTimeCauchyFlow
open Stage9C.Revision
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

/-- The independently given current is formed first; the unchanged original
source then prepares and writes that generated complete operand. -/
theorem entire_current_native (initial : StageNineCauchyState) (clock elapsed : ℝ)
    (smooth : ActualInitial.SmoothInitial initial)
    (nondegenerate : ∀ space, Matrix.det (initial.coframe space) ≠ 0) :
    ∃ material : MotherStreamFormation.Carrier,
      MotherStreamFormation.read material = currentSamples initial clock ∧
      decodeCurrent material = (initial, clock) ∧
      ∃ formedSmooth : ActualInitial.SmoothInitial (decodeInitial material),
      ∃ formedNondegenerate : ∀ space, Matrix.det ((decodeInitial material).coframe space) ≠ 0,
      let prepared := ActualInitial.state (decodeInitial material) formedSmooth formedNondegenerate
      let successor := ActualSourceCoverage.successor prepared
      SpinPair.source.toRootSource.actual.compile (ActualSourceCoverage.occurrence prepared) =
        .nativeWrite (materialActionAt (SpinPair.underlying (.running prepared))) ∧
      successor.targetCurrent = SpinPair.next (.running prepared) ∧
      Recognition.wholeField successor.targetCurrent =
        Stage9C.Reduction.p286CartanNext positiveSmoothUnifiedSource prepared.current
          prepared.smooth prepared.nondegenerate 0 ∧
      successor.ledgerEvolution.destination (materialEntry (SpinPair.support (.running prepared))) =
        ⟨materialEntry (SpinPair.support (SpinPair.next (.running prepared))),
          .transferred (.transfer (materialActionAt (SpinPair.underlying (.running prepared))))
            rfl rfl (Nat.le_refl _)⟩ ∧
      PhysicalCoverage.advance (decodeCurrent material) elapsed =
        (sourceGeneratedMotherTimeCauchyUpdate PhysicalCoverage.source elapsed initial, clock + elapsed) := by
  obtain ⟨material, formed, recovered⟩ := entire_current_formed initial clock smooth
  have initial_eq : decodeInitial material = initial := congrArg Prod.fst recovered
  have formedSmooth : ActualInitial.SmoothInitial (decodeInitial material) := initial_eq.symm ▸ smooth
  have formedNondegenerate : ∀ space, Matrix.det ((decodeInitial material).coframe space) ≠ 0 :=
    initial_eq.symm ▸ nondegenerate
  refine ⟨material, formed, recovered, formedSmooth, formedNondegenerate, ?_⟩
  have native := ActualInitial.native_consumed (decodeInitial material) formedSmooth formedNondegenerate
  exact ⟨native.1, native.2.1, native.2.2.1, native.2.2.2, by rw [recovered]; rfl⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentMaterial
