import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaFiniteEffectHistory

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

inductive RuntimeEffectFace
  | pairedOmega
  deriving DecidableEq

def runtimeEffectFacade
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRuntimeFacade CanonicalUnitArithmeticRoot.N where
  process := runtimeEffectProcess observation nontrivial
  FaceAt := fun _ => RuntimeEffectFace
  componentAt := fun _ _ =>
    (runtimeEffectRecognition observation nontrivial).effectComponent
  installationAt := fun _ _ =>
    (runtimeEffectRecognition observation nontrivial).installation
  projectionAt := fun _ _ => PUnit.unit

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
