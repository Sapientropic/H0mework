import H0mework.Versions.X.Arithmetic.FockState.PrimePairOccupation
import H0mework.Versions.Y.Arithmetic.FockResponsibility.DebtActivation
import H0mework.Versions.Y.Arithmetic.FockResponsibility.AtomicRuntime

/-!
# Exact-occurrence prime-pair actuality claim

The registered arithmetic occurrence generates one exact even target, its
particle occupation coordinate, and a zero-field actuality claim.  The claim
contains no prime pair and no nonvanishing premise.  Actual fibre data belongs
only to settlement; the negative classifier branch remains a faithful
representation obstruction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActuality

open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticExactOccurrenceAdditiveProducer
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open ArithmeticGeneration
open ParticleWaveFock
open ParticleWaveFockAtomicDynamicsRuntime
open ParticleWaveFockOccurrenceDebtActivation
open SourceGeneratedEffectiveFibreDisposition

noncomputable section

universe u

/-! ## Witness-free claim -/

/-- The semantic claim is indexed by the complete exact even occurrence.  It
stores neither a prime pair, a nonzero coefficient, nor a terminal branch. -/
structure PrimePairActualityClaimAt
    {Occurrence : Type u} {rootOccurrence : Occurrence}
    (_exactEvenOccurrence : RootedAccountedUnfolding
      (ExactOccurrenceAdditivePointAt rootOccurrence)) : Type u where
  private mk ::

def PrimePairActualityClaimAt.generate
    {Occurrence : Type u} {rootOccurrence : Occurrence}
    (exactEvenOccurrence : RootedAccountedUnfolding
      (ExactOccurrenceAdditivePointAt rootOccurrence)) :
    PrimePairActualityClaimAt exactEvenOccurrence :=
  .mk

instance PrimePairActualityClaimAt.instSubsingleton
    {Occurrence : Type u} {rootOccurrence : Occurrence}
    {exactEvenOccurrence : RootedAccountedUnfolding
      (ExactOccurrenceAdditivePointAt rootOccurrence)} :
    Subsingleton (PrimePairActualityClaimAt exactEvenOccurrence) :=
  ⟨fun left right => by cases left; cases right; rfl⟩

/-! ## Same-occurrence dependent face -/

abbrev BaseAuthoritySource :=
  ParticleWaveFockAtomicDynamicsRuntime.authoritySource

abbrev BaseLedgerSource :=
  BaseAuthoritySource.restructuringSource.toLedgerSource

/-- One exact arithmetic occurrence generates the even target, its
prime-pair actuality claim, and the current occupation coordinate together.
The occupation value is a readout, not a settlement field. -/
structure RootGeneratedPrimePairActualityAt
    (current : CanonicalUnitArithmeticRoot.Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current) : Type where
  private mk ::
  sourceOccurrence :
    BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current
  sourceOccurrence_eq : sourceOccurrence = occurrence
  operational : RootGeneratedOperationalGoldbachCurrentAt
    current occurrence indexInRange
  operational_eq : operational =
    generateOperationalGoldbachCurrent current occurrence indexInRange
  exactEvenOccurrence : RootedAccountedUnfolding
    (ExactOccurrenceAdditivePointAt occurrence)
  exactEvenOccurrence_eq : exactEvenOccurrence = operational.targetOccurrence
  exactEvenRoot : exactEvenOccurrence.root.rootOccurrence = occurrence
  claim : PrimePairActualityClaimAt exactEvenOccurrence
  claim_eq : claim = PrimePairActualityClaimAt.generate exactEvenOccurrence
  particle : ParticleWaveFockRuntime.RootGeneratedParticleWaveCurrentAt
    current occurrence indexInRange
  particle_eq : particle = ParticleWaveFockRuntime.generateParticleWaveCurrent
    current occurrence indexInRange
  occupation : ℤ
  occupation_eq : occupation =
    atomicTargetAmplitude
      (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current)
      particle.sourceState

def generatePrimePairActuality
    (current : CanonicalUnitArithmeticRoot.Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current) :
    RootGeneratedPrimePairActualityAt current occurrence indexInRange := by
  let operational :=
    generateOperationalGoldbachCurrent current occurrence indexInRange
  let exactEvenOccurrence := operational.targetOccurrence
  let particle := ParticleWaveFockRuntime.generateParticleWaveCurrent
    current occurrence indexInRange
  exact
    { sourceOccurrence := occurrence
      sourceOccurrence_eq := rfl
      operational := operational
      operational_eq := rfl
      exactEvenOccurrence := exactEvenOccurrence
      exactEvenOccurrence_eq := rfl
      exactEvenRoot := operational.targetRoot
      claim := PrimePairActualityClaimAt.generate exactEvenOccurrence
      claim_eq := rfl
      particle := particle
      particle_eq := rfl
      occupation := atomicTargetAmplitude
        (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current)
        particle.sourceState
      occupation_eq := rfl }

/-- A settlement contains the actual prime-pair fibre and the resulting
nonzero occupation.  These data are deliberately absent from the claim. -/
structure PrimePairActualitySettlementAt
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) : Type where
  private mk ::
  fibre : EffectiveAdditiveFibreAt
    (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current)
  occupation_ne_zero : actuality.occupation ≠ 0

def PrimePairActualitySettlementAt.ofFibre
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange)
    (fibre : EffectiveAdditiveFibreAt
      (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current)) :
    PrimePairActualitySettlementAt actuality := by
  refine ⟨fibre, ?_⟩
  rw [actuality.occupation_eq, actuality.particle_eq]
  rw [(ParticleWaveFockRuntime.generateParticleWaveCurrent
    current occurrence indexInRange).sourceState_eq]
  change atomicPrimePairOccupation
      (ParticleWaveFockRuntime.liveGlobalOwner current)
      (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current) ≠ 0
  exact (atomicPrimePairOccupation_ne_zero_iff_effectiveFibre
    (ParticleWaveFockRuntime.liveGlobalOwner current)
    (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current)).2
      ⟨fibre⟩

theorem occupation_ne_zero_iff_effectiveFibre
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) :
    actuality.occupation ≠ 0 ↔
      Nonempty (EffectiveAdditiveFibreAt
        (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex
          current)) := by
  rw [actuality.occupation_eq, actuality.particle_eq]
  rw [(ParticleWaveFockRuntime.generateParticleWaveCurrent
    current occurrence indexInRange).sourceState_eq]
  change atomicPrimePairOccupation
      (ParticleWaveFockRuntime.liveGlobalOwner current)
      (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current) ≠
    0 ↔ _
  exact atomicPrimePairOccupation_ne_zero_iff_effectiveFibre _ _

/-- The terminal family is exactly the nonzero occupation event.  This
equivalence does not place either side inside the witness-free claim. -/
theorem settlement_nonempty_iff_occupation_ne_zero
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) :
    Nonempty (PrimePairActualitySettlementAt actuality) ↔
      actuality.occupation ≠ 0 := by
  constructor
  · rintro ⟨settled⟩
    exact settled.occupation_ne_zero
  · intro occupationNonzero
    obtain ⟨fibre⟩ :=
      (occupation_ne_zero_iff_effectiveFibre actuality).1 occupationNonzero
    exact ⟨PrimePairActualitySettlementAt.ofFibre actuality fibre⟩

/-- The negative classifier branch remains an exact faithful residual.  It
is an obstruction coordinate, not a settlement and not a zero field hidden
inside the claim. -/
structure PrimePairActualityObstructionAt
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (_actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) : Type where
  private mk ::
  residual : EffectiveAdditiveResidualAt
    (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current)
  classifier_eq : generatedAdditiveDisposition
      (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current) =
    .residual residual

theorem obstruction_nonempty_iff_occupation_eq_zero
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) :
    Nonempty (PrimePairActualityObstructionAt actuality) ↔
      actuality.occupation = 0 := by
  constructor
  · rintro ⟨blocked⟩
    apply not_ne_iff.mp
    intro occupationNonzero
    obtain ⟨fibre⟩ :=
      (occupation_ne_zero_iff_effectiveFibre actuality).1 occupationNonzero
    exact blocked.residual.fibre_is_empty.false fibre
  · intro occupationZero
    have fibreEmpty : ¬ Nonempty (EffectiveAdditiveFibreAt
        (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex
          current)) := by
      intro inhabited
      have occupationNonzero :=
        (occupation_ne_zero_iff_effectiveFibre actuality).2 inhabited
      exact occupationNonzero occupationZero
    let residual := residualOfEmpty
      (additiveEvaluation
        (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current))
      (evenTargetHistory
        (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current))
      fibreEmpty
    exact ⟨{
      residual := residual
      classifier_eq := settle_eq_residual_of_empty _ _ fibreEmpty }⟩

inductive SourceGeneratedPrimePairActualityDispositionAt
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) : Type
  | settlement (settled : PrimePairActualitySettlementAt actuality)
  | obstruction (blocked : PrimePairActualityObstructionAt actuality)

def generatePrimePairActualityDisposition
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {indexInRange : 1 ≤
      CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current}
    (actuality : RootGeneratedPrimePairActualityAt
      current occurrence indexInRange) :
    SourceGeneratedPrimePairActualityDispositionAt actuality := by
  cases classifier_eq : generatedAdditiveDisposition
      (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current) with
  | inhabited fibre =>
      exact .settlement (PrimePairActualitySettlementAt.ofFibre actuality fibre)
  | residual residual =>
      exact .obstruction ⟨residual, classifier_eq⟩

/-! ## Projection installation contract -/

def actualityProjectionLaw : SourceNativeProjectionLaw BaseLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift
    (1 ≤ CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current)
  InactiveAt := fun _ {current} _occurrence => PLift
    (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex current = 0)
  classify := by
    intro projection current occurrence
    cases current with
    | empty => exact .inr ⟨rfl⟩
    | next prior =>
        exact .inl ⟨by
          unfold CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex
            UnitHistory.cardinalShadow
          omega⟩
  PayloadAt := fun _ {current} occurrence active =>
    RootGeneratedPrimePairActualityAt current occurrence active.down
  project := fun _ {current} occurrence active =>
    generatePrimePairActuality current occurrence active.down

/-! ## Hostile separation from the old factor-process claim -/

inductive ClaimCoordinateAt
    {Occurrence : Type u} {rootOccurrence : Occurrence}
    (exactEvenOccurrence : RootedAccountedUnfolding
      (ExactOccurrenceAdditivePointAt rootOccurrence)) : Type u
  | occurrenceFactorProcess
      (claim : ParticleWaveFockOccurrenceDebtActivation.DebtClaim)
  | primePairActuality
      (claim : PrimePairActualityClaimAt exactEvenOccurrence)

def oldFactorClaimCoordinate
    {Occurrence : Type u} {rootOccurrence : Occurrence}
    (exactEvenOccurrence : RootedAccountedUnfolding
      (ExactOccurrenceAdditivePointAt rootOccurrence)) :
    ClaimCoordinateAt exactEvenOccurrence :=
  .occurrenceFactorProcess .accountOccurrenceFactorProcess

def actualityClaimCoordinate
    {Occurrence : Type u} {rootOccurrence : Occurrence}
    (exactEvenOccurrence : RootedAccountedUnfolding
      (ExactOccurrenceAdditivePointAt rootOccurrence)) :
    ClaimCoordinateAt exactEvenOccurrence :=
  .primePairActuality (PrimePairActualityClaimAt.generate exactEvenOccurrence)

theorem oldFactorClaim_ne_primePairActuality
    {Occurrence : Type u} {rootOccurrence : Occurrence}
    (exactEvenOccurrence : RootedAccountedUnfolding
      (ExactOccurrenceAdditivePointAt rootOccurrence)) :
    oldFactorClaimCoordinate exactEvenOccurrence ≠
      actualityClaimCoordinate exactEvenOccurrence := by
  intro equality
  cases equality

end

end ParticleWaveFockPrimePairActuality
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
