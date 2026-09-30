import H0mework.Versions.Y.Arithmetic.FockUnitAction.Inventory.SourceSelected.Root
import H0mework.Versions.Y.Arithmetic.FockResponsibility.AtomicRuntime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace GoldbachUnitSelectedActor

open ArithmeticGeneration
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open CanonicalUnitArithmeticRoot

noncomputable section

abbrev BaseAuthoritySource := ParticleWaveFockAtomicDynamicsRuntime.authoritySource
abbrev BaseLedgerSource := BaseAuthoritySource.restructuringSource.toLedgerSource

/-- The actor is projected from the original emitted occurrence. Its source
is the original canonical split, and its outcome is the generated full run. -/
structure RootGeneratedActorAt
    (current : Current)
    (occurrence : BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (indexInRange : 1 ≤ scanIndex current) : Type where
  private mk ::
  sourceOccurrence : BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current
  sourceOccurrence_eq : sourceOccurrence = occurrence
  rooted : RootedRunAt sourceOccurrence (scanIndex current) indexInRange
  rooted_eq : rooted = generateRooted sourceOccurrence (scanIndex current) indexInRange

def generateActorAt (current : Current)
    (occurrence : BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (indexInRange : 1 ≤ scanIndex current) :
    RootGeneratedActorAt current occurrence indexInRange :=
  { sourceOccurrence := occurrence
    sourceOccurrence_eq := rfl
    rooted := generateRooted occurrence (scanIndex current) indexInRange
    rooted_eq := rfl }

def projectionLaw : SourceNativeProjectionLaw BaseLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift (1 ≤ scanIndex current)
  InactiveAt := fun _ {current} _occurrence => PLift (scanIndex current = 0)
  classify := by
    intro projection current occurrence
    cases current with
    | empty => exact .inr ⟨rfl⟩
    | next prior =>
        exact .inl ⟨by
          unfold scanIndex UnitHistory.cardinalShadow
          omega⟩
  PayloadAt := fun _ {current} occurrence active =>
    RootGeneratedActorAt current occurrence active.down
  project := fun _ {current} occurrence active =>
    generateActorAt current occurrence active.down

end
end GoldbachUnitSelectedActor
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
