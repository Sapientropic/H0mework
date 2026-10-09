import H0mework.Versions.V2.Arithmetic.RiemannRuntime.PairedOmegaFiniteEffectHistory

/-!
# Named runtime facade for the A1c paired-Omega effect

The facade names the already installed recursive-effect component at every
source-reachable finite runtime state.  It adds no process, occurrence,
classifier or payload.  Its readout is identified with the rooted active
effect fibre generated from the same compiler visit.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

noncomputable section

inductive RuntimeEffectFace (observation : GeneratedRiemannZeroObservation)
  | pairedOmega
  | combCalculation (half : OriginalKCombCalculation.Half observation)
  deriving DecidableEq

def runtimeEffectFacade
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRuntimeFacade CanonicalUnitArithmeticRoot.N where
  process := runtimeEffectProcess observation nontrivial
  FaceAt := fun _ => RuntimeEffectFace observation
  componentAt := fun _ face => match face with
    | .pairedOmega => (runtimeEffectRecognition observation nontrivial).effectComponent
    | .combCalculation _ => OriginalKCombCalculation.component observation nontrivial
  installationAt := fun _ face => match face with
    | .pairedOmega => (runtimeEffectRecognition observation nontrivial).installation
    | .combCalculation _ => runtimeCombCalculationInstallation observation nontrivial
  projectionAt := fun _ face => match face with
    | .pairedOmega => PUnit.unit
    | .combCalculation half => half

def runtimeEffectFacadeReadoutAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :=
  (runtimeEffectFacade observation nontrivial).readoutAt
    (runtimeEffectRuntimeAt observation nontrivial depth)
    .pairedOmega

/-- The named facade and the causally registered effect row are the same
installed source fibre at every finite compiler visit. -/
theorem runtimeEffectFacadeReadoutAt_heq_installedFiber
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    HEq (runtimeEffectFacadeReadoutAt observation nontrivial depth)
      (runtimeEffectRootedActiveAt observation nontrivial depth
        ).installedFiber := by
  change HEq
    ((runtimeEffectRecognition observation nontrivial).effectComponent.outcomeAt
      PUnit.unit
      ((runtimeEffectRoot observation nontrivial).emitted
        (runtimeEffectVisitAt observation nontrivial
          (runtimeEffectRuntimeAt observation nontrivial depth).state).current))
    (runtimeEffectRootedActiveAt observation nontrivial depth).installedFiber
  rw [runtimeEffectRuntimeAt_state observation nontrivial depth]
  exact heq_of_eq <|
    (runtimeEffectRootedActiveAt observation nontrivial depth
      ).componentOutcome_eq_installedFiber

/-- Named-facade provenance at every finite stage: the readout, exact
occurrence, whole ledger and generated next are one runtime tick. -/
theorem runtimeEffectFacadeReadoutAt_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    type_of%
      ((runtimeEffectFacade observation nontrivial).readoutAt_factorizes
        (runtimeEffectRuntimeAt observation nontrivial depth)
        RuntimeEffectFace.pairedOmega) :=
  (runtimeEffectFacade observation nontrivial).readoutAt_factorizes
    (runtimeEffectRuntimeAt observation nontrivial depth)
    RuntimeEffectFace.pairedOmega


def runtimeCombCalculationReadoutAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  (runtimeEffectFacade observation nontrivial).readoutAt
    (runtimeEffectRuntimeAt observation nontrivial depth) (.combCalculation half)

theorem runtimeCombCalculationReadoutAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeCombCalculationReadoutAt observation nontrivial depth half =
      .inl ⟨PUnit.unit, OriginalKCombCalculation.result observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence)⟩ := rfl

def runtimeCombCalculationResultAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :=
  match runtimeCombCalculationReadoutAt observation nontrivial depth half with
  | .inl ⟨_, result⟩ => result
  | .inr impossible => nomatch impossible

theorem runtimeCombCalculationResultAt_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) :
    runtimeCombCalculationResultAt observation nontrivial depth half =
      OriginalKCombCalculation.result observation nontrivial half
        ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence) := rfl

theorem runtimeCombCalculationReadoutAt_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (half : OriginalKCombCalculation.Half observation) : type_of%
    ((runtimeEffectFacade observation nontrivial).readoutAt_factorizes
      (runtimeEffectRuntimeAt observation nontrivial depth) (.combCalculation half)) :=
  (runtimeEffectFacade observation nontrivial).readoutAt_factorizes
    (runtimeEffectRuntimeAt observation nontrivial depth) (.combCalculation half)

end

end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
