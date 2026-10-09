import H0mework.Versions.V2.Arithmetic.RiemannGraph.IntegralGraphJointAction

/-!
# Same-root occurrence for the paired integral graph action

The paired selected/reversal input is generated from the integral orbits
already stored in the zero-owned joint-state occurrence.  Its complete
occurrence projects through the existing character--Müntz chain to the exact
canonical unit-arithmetic seed, whose activated root already owns the whole
ledger and compiler successor.

No covariance equation, residual-zero field, separator, fixedness or endpoint
branch enters this occurrence.
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

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation

noncomputable section

def pairedGraphMeasurementReadFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial) :
    IntegralScaleCarrier →ₗ[ℤ] QRich.ClozelJPair :=
  (((WithLp.sndₗ 2 ℂ PositiveMellinQuarterEnergy ℂ).restrictScalars ℤ).comp
      source.2.selectedIntegralOrbit).prod
    (((WithLp.sndₗ 2 ℂ PositiveMellinQuarterEnergy ℂ).restrictScalars ℤ).comp
      source.2.reversalIntegralOrbit)

/-- The five action/read maps are read from the same joint-state payload.
Only the scale action is supplied as the dependent coordinate. -/
def pairedJointInputFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial)
    (scale : Units NNReal) :
    SourceGeneratedIntegralCoherentJointAction.Input
      IntegralScaleCarrier (JointGraphTarget × JointGraphTarget)
        QRich.ClozelJPair where
  integralAction := (leftTranslation scale).toLinearMap
  coherentAction := pairedOwnerFreeGraphAction scale
  measurementAction := LinearMap.id
  coherentRead := source.2.selectedIntegralOrbit.prod
    source.2.reversalIntegralOrbit
  measurementRead := pairedGraphMeasurementReadFromSource source

theorem pairedJointInputFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    pairedJointInputFromSource
        (zeroOwnedJointStateModuleOccurrence observation nontrivial).root scale =
      pairedJointInput observation nontrivial scale := by
  rfl

abbrev PairedJointActionPayload
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  Σ _source : ZeroOwnedJointStateModulePayload observation nontrivial,
    SourceGeneratedIntegralCoherentJointAction.Input
      IntegralScaleCarrier (JointGraphTarget × JointGraphTarget)
        QRich.ClozelJPair

/-- The paired action is a dependent face of the actual joint-state tree,
not a second root or a constant payload attached after the fact. -/
def pairedJointActionOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    RootedAccountedUnfolding
      (PairedJointActionPayload observation nontrivial) :=
  (zeroOwnedJointStateModuleOccurrence observation nontrivial).map fun source =>
    ⟨source, pairedJointInputFromSource source scale⟩

theorem pairedJointActionOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (pairedJointActionOccurrence observation nontrivial scale).map Sigma.fst =
      zeroOwnedJointStateModuleOccurrence observation nontrivial := by
  rw [pairedJointActionOccurrence, RootedAccountedUnfolding.map_map]
  change (zeroOwnedJointStateModuleOccurrence observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem pairedJointActionOccurrence_projects_to_characterMuntz
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    ((pairedJointActionOccurrence observation nontrivial scale).map
        Sigma.fst).map Sigma.fst =
      zeroOwnedCharacterMuntzCokernelOccurrence observation nontrivial := by
  rw [pairedJointActionOccurrence_projects,
    zeroOwnedJointStateModuleOccurrence_projects]

theorem pairedJointActionOccurrence_projects_to_seed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (((((((pairedJointActionOccurrence observation nontrivial scale).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Prod.fst = seedOccurrence := by
  rw [pairedJointActionOccurrence_projects,
    zeroOwnedJointStateModuleOccurrence_projects,
    zeroOwnedCharacterMuntzCokernelOccurrence_projects_to_seed]

/-- The seed reached above is the exact activated unit root; this is the
existing emitter, whole-ledger write-back and generated next, not a new
controller-local authority. -/
theorem seedRuntime_root_ledger_next_factorization :
    let runtime := CanonicalUnitArithmeticRoot.runtimeSeed
    runtime.tick.generated.occurrence =
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtime.current.visit.current ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      runtime.tick.nextCurrent =
        CanonicalUnitArithmeticRoot.runtimeFacade.process.stateAt
          (CanonicalUnitArithmeticRoot.runtimeFacade.process.successor
            runtime.state) := by
  let runtime := CanonicalUnitArithmeticRoot.runtimeSeed
  have factorization := CanonicalUnitArithmeticRoot.coversAt_factorizes
    runtime .material
  exact ⟨factorization.2.1, factorization.2.2.1,
    factorization.2.2.2.2⟩

theorem pairedJointActionOccurrence_root_ledger_next
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (((((((pairedJointActionOccurrence observation nontrivial scale).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Prod.fst = seedOccurrence ∧
      (let runtime := CanonicalUnitArithmeticRoot.runtimeSeed
       runtime.tick.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
            runtime.current.visit.current ∧
        HEq runtime.tick.generated.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            runtime.current.visit.current) ∧
        runtime.tick.nextCurrent =
          CanonicalUnitArithmeticRoot.runtimeFacade.process.stateAt
            (CanonicalUnitArithmeticRoot.runtimeFacade.process.successor
              runtime.state)) :=
  ⟨pairedJointActionOccurrence_projects_to_seed
      observation nontrivial scale,
    seedRuntime_root_ledger_next_factorization⟩

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
