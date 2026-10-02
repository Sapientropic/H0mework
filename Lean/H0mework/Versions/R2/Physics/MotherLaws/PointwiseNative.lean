import H0mework.Versions.R2.Physics.MotherLaws.PointwiseRestriction
import H0mework.Versions.R2.Physics.MotherProgrammesFormationCurrent.SpacetimeRecovery

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseNative

open Stage9C.Revision StageNineEnrichedProofFreeSource
open WholeSpacetimeMaterial MotherPointwiseLaws

noncomputable section

/-- Evaluation returns to the already formed mother material through its original inverse. -/
def evaluate (law : Law) (material : MotherStreamFormation.Carrier) :
    MotherStreamFormation.Carrier :=
  CurrentSampleAction.readInverse (eval law (MotherStreamFormation.read material))

theorem read_evaluate (law : Law) (material : MotherStreamFormation.Carrier) :
    MotherStreamFormation.read (evaluate law material) =
      eval law (MotherStreamFormation.read material) :=
  CurrentSampleAction.read_readInverse _

/-- One formed law implements the original whole-field writer on every complete
physical current. Its smoothness and qualification data already belong to that current. -/
theorem native_writer_formed :
    ∃ law : Law, ∀ current : SpinPair.Current,
      evaluate law (encode current) = encode (SpinPair.next current) := by
  obtain ⟨law, generated⟩ := every_restriction samples samples_injective
    (fun current => samples (SpinPair.next current))
  refine ⟨law, fun current => ?_⟩
  apply MotherStreamFormation.read_inducing.isInducing.injective
  rw [read_evaluate, read_encode, generated, read_encode]

/-- The new law's actual value is the original native target, including the
nonlinear reduced-action and Cartan writer. Full field recovery preserves the integral. -/
theorem native_writer_consumed :
    ∃ law : Law,
      (∀ current : SpinPair.Current,
        evaluate law (encode current) = encode (SpinPair.next current) ∧
        decode (evaluate law (encode current)) = SpinPair.next current) ∧
      ∀ state : MaterialState,
        let after := decode (evaluate law (encode (.running state)))
        (∀ occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt (.running state),
          SpinPair.source.toRootSource.actual.compile occurrence =
            .nativeWrite (materialActionAt (SpinPair.underlying (.running state)))) ∧
        (ActualSourceCoverage.successor state).targetCurrent = after ∧
        Recognition.wholeField after =
          Stage9C.Reduction.p286CartanNext positiveSmoothUnifiedSource state.current
            state.smooth state.nondegenerate 0 ∧
        Stage9C.Reduction.actualRelativeAction positiveSmoothUnifiedSource state.current
            (Recognition.wholeField after) =
          Stage9C.Reduction.actualRelativeAction positiveSmoothUnifiedSource state.current
            (materialStateNext state).current ∧
        (ActualSourceCoverage.successor state).ledgerEvolution.destination
            (materialEntry (SpinPair.support (.running state))) =
          ⟨materialEntry (SpinPair.support (SpinPair.next (.running state))),
            .transferred (.transfer (materialActionAt (SpinPair.underlying (.running state))))
              rfl rfl (Nat.le_refl _)⟩ := by
  obtain ⟨law, formed⟩ := native_writer_formed
  have recovered (current : SpinPair.Current) :
      decode (evaluate law (encode current)) = SpinPair.next current := by
    rw [formed, decode_encode]
  refine ⟨law, fun current => ⟨formed current, recovered current⟩, ?_⟩
  intro state
  dsimp only
  rw [recovered]
  exact ⟨fun _ => rfl, ActualSourceCoverage.successor_native state,
    Recognition.native_running_fold state, rfl, rfl⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseNative
