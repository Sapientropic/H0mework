import H0mework.Versions.R2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Actor

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace GoldbachUnitSelectedActor

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer
open CanonicalUnitArithmeticExactOccurrenceAdditiveProducer
open ParticleWaveFockAtomicProcess
open ParticleWaveFockFullInventoryAction
open ParticleWaveFockUnitChargeAction
open ParticleWaveFockUnitChargeScan
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

/-- Subordinate receipt under the original exact occurrence.  The actor
outcome cannot be replaced by a caller's reached/exhausted branch. -/
structure RootedRunAt {Occurrence : Type} (rootOccurrence : Occurrence)
    (index : Nat) (indexInRange : 1 ≤ index) : Type where
  private mk ::
  rootSource : RootGeneratedExactOccurrenceOperationalFactorDecayAt
    rootOccurrence index indexInRange
  rootSource_eq : rootSource =
    CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
      rootOccurrence index indexInRange
  source_eq : rootSource.source = canonicalSplit index indexInRange
  occurrenceRoot : rootSource.occurrence.root.rootOccurrence = rootOccurrence
  sourceWholeOccurrence :
    (UnitHistory.generate (splitLeft rootSource.source)).parallel
        (UnitHistory.generate (splitRight rootSource.source)) =
      rootSource.occurrence.fold
        CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.terminalHistoryAlgebra
  outcome : OutcomeAt rootSource.source
  outcome_eq : outcome = GoldbachUnitSelectedActor.generate rootSource.source

def generateRooted {Occurrence : Type} (rootOccurrence : Occurrence)
    (index : Nat) (indexInRange : 1 ≤ index) :
    RootedRunAt rootOccurrence index indexInRange := by
  let rootSource :=
    CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
      rootOccurrence index indexInRange
  exact
    { rootSource := rootSource
      rootSource_eq := rfl
      source_eq := rootSource.source_eq
      occurrenceRoot := rootSource.occurrenceRoot
      sourceWholeOccurrence :=
        (generatedSplitWhole_eq_evenTarget rootSource.source).trans rootSource.targetFold.symm
      outcome := generate rootSource.source
      outcome_eq := rfl }
end
end GoldbachUnitSelectedActor
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
