import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.FibreRead
import H0mework.Versions.V2.Arithmetic.FockResponsibility.DirectActuality
import H0mework.Versions.V2.Arithmetic.FockUnitAction.Direct.LivingLawCanonicalParticleWaveFockExactFourierMidpointProducer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace GoldbachUnitSelectedActor

open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open ParticleWaveFockOccurrenceResponsibilityRuntime
open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDirect
open ParticleWaveFockRuntimeExactPrimeFourierSibling
open ParticleWaveFockExactFourierMidpointProducer
open GoldbachPrimePairTrace

noncomputable section

theorem runtime_reached_settlement (depth : Nat)
    (reached : ReachedAt
      (runtimeUnitSelectedActorPayload depth).rooted.rootSource.source) :
    Nonempty (PrimePairActualitySettlementAt (directRuntimeActuality depth)) := by
  let terminal := reached.terminalPath (runtimeActive depth).down
  exact ⟨PrimePairActualitySettlementAt.ofFibre
    (directRuntimeActuality depth) (fibreOfTerminal terminal.terminal)⟩

theorem runtime_exhausted_obstruction (depth : Nat)
    (exhausted : ExhaustedAt
      (runtimeUnitSelectedActorPayload depth).rooted.rootSource.source) :
    Nonempty (PrimePairActualityObstructionAt (directRuntimeActuality depth)) := by
  let actor := runtimeUnitSelectedActorPayload depth
  have sourceEq : actor.rooted.rootSource.source =
      canonicalSplit (scanIndex (runtimeAt depth).current.visit.current)
        (runtimeActive depth).down := actor.rooted.source_eq
  have exhaustedCanonical : ExhaustedAt
      (canonicalSplit (scanIndex (runtimeAt depth).current.visit.current)
        (runtimeActive depth).down) := by
    change ExhaustedAt actor.rooted.rootSource.source at exhausted
    rw [sourceEq] at exhausted
    exact exhausted
  have fibreEmpty := canonical_exhausted_fibre_empty
    (scanIndex (runtimeAt depth).current.visit.current)
    (runtimeActive depth).down exhaustedCanonical
  have occupationZero : (directRuntimeActuality depth).occupation = 0 := by
    apply not_ne_iff.mp
    intro occupationNe
    exact fibreEmpty ((occupation_ne_zero_iff_effectiveFibre
      (directRuntimeActuality depth)).mp occupationNe)
  exact (obstruction_nonempty_iff_occupation_eq_zero
    (directRuntimeActuality depth)).mpr occupationZero

theorem runtimeDisposition_is_obstruction (depth : Nat)
    (blocked : PrimePairActualityObstructionAt (directRuntimeActuality depth)) :
    ∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
      generatePrimePairActualityDisposition (directRuntimeActuality depth) =
        .obstruction generated := by
  cases selected : generatePrimePairActualityDisposition (directRuntimeActuality depth) with
  | obstruction generated => exact ⟨generated, rfl⟩
  | settlement settled =>
      have zero := (obstruction_nonempty_iff_occupation_eq_zero
        (directRuntimeActuality depth)).mp ⟨blocked⟩
      exact False.elim (settled.occupation_ne_zero zero)

/-- The installed source-selected actor chooses the original actuality
disposition from its own chronological result. No reached/obstruction branch
is supplied to the root. -/
theorem runtime_actor_consumes_original_disposition (depth : Nat) :
    (∃ reached : ReachedAt
        (runtimeUnitSelectedActorPayload depth).rooted.rootSource.source,
      (runtimeUnitSelectedActorPayload depth).rooted.outcome = .inl reached ∧
        ∃ generated : PrimePairActualitySettlementAt (directRuntimeActuality depth),
          generatePrimePairActualityDisposition (directRuntimeActuality depth) =
            .settlement generated) ∨
    (∃ exhausted : ExhaustedAt
        (runtimeUnitSelectedActorPayload depth).rooted.rootSource.source,
      (runtimeUnitSelectedActorPayload depth).rooted.outcome = .inr exhausted ∧
        ∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
          generatePrimePairActualityDisposition (directRuntimeActuality depth) =
            .obstruction generated) := by
  cases generated : (runtimeUnitSelectedActorPayload depth).rooted.outcome with
  | inl reached =>
      obtain ⟨settled⟩ := runtime_reached_settlement depth reached
      obtain ⟨selected, selectedEq⟩ :=
        directRuntimeDisposition_is_settlement depth settled
      exact .inl ⟨reached, rfl, selected, selectedEq⟩
  | inr exhausted =>
      obtain ⟨blocked⟩ := runtime_exhausted_obstruction depth exhausted
      obtain ⟨selected, selectedEq⟩ := runtimeDisposition_is_obstruction depth blocked
      exact .inr ⟨exhausted, rfl, selected, selectedEq⟩

/-- One installed actor result is consumed by the old actuality disposition
and the same root's generated projection, whole ledger, and literal next. -/
theorem runtime_actor_original_row_and_next (depth : Nat) :
    let actor := runtimeUnitSelectedActorPayload depth
    ((∃ reached : ReachedAt actor.rooted.rootSource.source,
        actor.rooted.outcome = .inl reached ∧
          ∃ generated : PrimePairActualitySettlementAt (directRuntimeActuality depth),
            generatePrimePairActualityDisposition (directRuntimeActuality depth) =
              .settlement generated) ∨
      (∃ exhausted : ExhaustedAt actor.rooted.rootSource.source,
        actor.rooted.outcome = .inr exhausted ∧
          ∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
            generatePrimePairActualityDisposition (directRuntimeActuality depth) =
              .obstruction generated)) ∧
    actor.sourceOccurrence =
      (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (runtimeAt depth).current.visit.current ∧
    HEq (runtimeAt depth).tick.generated.wholeLedgerWriteBack
      ((runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt depth).current.visit.current) ∧
    (runtimeAt depth).tick.nextCurrent =
      ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeFacade.process.stateAt
        (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeFacade.process.successor
          (runtimeAt depth).state) ∧
    HEq ((Sum.inl ⟨runtimeActive depth, actor⟩) :
      SourceNativeProjectionFiberAt projectionLaw PUnit.unit
        (runtimeAt depth).emittedOccurrence)
      ((runtimeAt depth).tick.generated.projectionOutcome
        ((ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeFacade.installationAt
            (runtimeAt depth)
            ParticleWaveFockOccurrenceResponsibilityRuntime.FaceAt.unitSelectedActor).embed
          (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeFacade.projectionAt
            (runtimeAt depth)
            ParticleWaveFockOccurrenceResponsibilityRuntime.FaceAt.unitSelectedActor))) := by
  dsimp only
  have branch := runtime_actor_consumes_original_disposition depth
  have rooted := runtimeUnitSelectedActor_keeps_occurrence_ledger_next depth
  have projection := runtimeUnitSelectedActorPayload_eq_tickProjection depth
  exact ⟨branch, rooted.1, rooted.2.1, rooted.2.2, projection⟩

/-- The original selected run reaches a terminal exactly when its same-target
prime-only Fourier source coordinate is nonzero. -/
theorem runtime_actor_reached_iff_fourier_nonzero (depth : Nat) :
    (∃ reached : ReachedAt
        (runtimeUnitSelectedActorPayload depth).rooted.rootSource.source,
      (runtimeUnitSelectedActorPayload depth).rooted.outcome = .inl reached) ↔
      runtimePrimeOnlyFourierCoefficient depth ≠ 0 := by
  constructor
  · rintro ⟨reached, _outcome⟩
    exact (directRuntimeSettlement_nonempty_iff_fourier_nonzero depth).mp
      (runtime_reached_settlement depth reached)
  · intro coefficientNonzero
    obtain ⟨settled⟩ :=
      (directRuntimeSettlement_nonempty_iff_fourier_nonzero depth).mpr
        coefficientNonzero
    cases generated : (runtimeUnitSelectedActorPayload depth).rooted.outcome with
    | inl reached => exact ⟨reached, rfl⟩
    | inr exhausted =>
        obtain ⟨blocked⟩ := runtime_exhausted_obstruction depth exhausted
        have occupationZero :=
          (obstruction_nonempty_iff_occupation_eq_zero
            (directRuntimeActuality depth)).mp ⟨blocked⟩
        exact False.elim (settled.occupation_ne_zero occupationZero)

/-- The complete chronological negative result is exactly the zero of the
original fixed-target Fourier source coordinate. -/
theorem runtime_actor_exhausted_iff_fourier_zero (depth : Nat) :
    (∃ exhausted : ExhaustedAt
        (runtimeUnitSelectedActorPayload depth).rooted.rootSource.source,
      (runtimeUnitSelectedActorPayload depth).rooted.outcome = .inr exhausted) ↔
      runtimePrimeOnlyFourierCoefficient depth = 0 := by
  constructor
  · rintro ⟨exhausted, _outcome⟩
    obtain ⟨blocked⟩ := runtime_exhausted_obstruction depth exhausted
    have occupationZero :=
      (obstruction_nonempty_iff_occupation_eq_zero
        (directRuntimeActuality depth)).mp ⟨blocked⟩
    by_contra coefficientNonzero
    obtain ⟨settled⟩ :=
      (directRuntimeSettlement_nonempty_iff_fourier_nonzero depth).mpr
        coefficientNonzero
    exact settled.occupation_ne_zero occupationZero
  · intro coefficientZero
    cases generated : (runtimeUnitSelectedActorPayload depth).rooted.outcome with
    | inl reached =>
        have coefficientNonzero :=
          (directRuntimeSettlement_nonempty_iff_fourier_nonzero depth).mp
            (runtime_reached_settlement depth reached)
        exact False.elim (coefficientNonzero coefficientZero)
    | inr exhausted => exact ⟨exhausted, rfl⟩

/-- At a composite midpoint, the positive actor branch consumes exactly the
off-diagonal prime/complement action of the original Fourier source. -/
theorem runtime_actor_reached_iff_offDiagonal_pos (depth : Nat)
    (midpointComposite : ¬ Nat.Prime (depth + 2)) :
    (∃ reached : ReachedAt
        (runtimeUnitSelectedActorPayload depth).rooted.rootSource.source,
      (runtimeUnitSelectedActorPayload depth).rooted.outcome = .inl reached) ↔
      0 < primeOnlyMidpointOffDiagonal (depth + 2) :=
  (runtime_actor_reached_iff_fourier_nonzero depth).trans
    (runtimePrimeOnlyFourierCoefficient_ne_zero_iff_offDiagonal_pos
      depth midpointComposite)

/-- The faithful exhausted residual at a composite midpoint is exactly zero
off-diagonal prime/complement source action; no negative branch is erased. -/
theorem runtime_actor_exhausted_iff_offDiagonal_zero (depth : Nat)
    (midpointComposite : ¬ Nat.Prime (depth + 2)) :
    (∃ exhausted : ExhaustedAt
        (runtimeUnitSelectedActorPayload depth).rooted.rootSource.source,
      (runtimeUnitSelectedActorPayload depth).rooted.outcome = .inr exhausted) ↔
      primeOnlyMidpointOffDiagonal (depth + 2) = 0 := by
  rw [runtime_actor_exhausted_iff_fourier_zero]
  rw [runtimePrimeOnlyFourierCoefficient_eq_midpoint_sq_add_offDiagonal]
  simp [primeVonMangoldtWeight, midpointComposite]

/-- The original actuality effect's obstruction branch is the same exact
off-diagonal zero equation as the complete source-selected actor. -/
theorem runtime_original_obstruction_iff_offDiagonal_zero (depth : Nat)
    (midpointComposite : ¬ Nat.Prime (depth + 2)) :
    (∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
      generatePrimePairActualityDisposition (directRuntimeActuality depth) =
        .obstruction generated) ↔
      primeOnlyMidpointOffDiagonal (depth + 2) = 0 := by
  constructor
  · rintro ⟨blocked, _effectEq⟩
    have occupationZero :=
      (obstruction_nonempty_iff_occupation_eq_zero
        (directRuntimeActuality depth)).mp ⟨blocked⟩
    have coefficientZero : runtimePrimeOnlyFourierCoefficient depth = 0 := by
      by_contra coefficientNonzero
      obtain ⟨settled⟩ :=
        (directRuntimeSettlement_nonempty_iff_fourier_nonzero depth).mpr
          coefficientNonzero
      exact settled.occupation_ne_zero occupationZero
    exact (runtime_actor_exhausted_iff_offDiagonal_zero
      depth midpointComposite).mp
        ((runtime_actor_exhausted_iff_fourier_zero depth).mpr coefficientZero)
  · intro offDiagonalZero
    obtain ⟨exhausted, _outcomeEq⟩ :=
      (runtime_actor_exhausted_iff_offDiagonal_zero
        depth midpointComposite).mpr offDiagonalZero
    obtain ⟨blocked⟩ := runtime_exhausted_obstruction depth exhausted
    exact runtimeDisposition_is_obstruction depth blocked

/-- The off-diagonal source equation and both actual chronological branches
remain attached to the emitted occurrence, whole row and literal successor. -/
theorem runtime_actor_composite_source_equation_original_row_and_next
    (depth : Nat) (midpointComposite : ¬ Nat.Prime (depth + 2)) :
    let actor := runtimeUnitSelectedActorPayload depth
    ((∃ reached : ReachedAt actor.rooted.rootSource.source,
        actor.rooted.outcome = .inl reached) ↔
      0 < primeOnlyMidpointOffDiagonal (depth + 2)) ∧
    ((∃ exhausted : ExhaustedAt actor.rooted.rootSource.source,
        actor.rooted.outcome = .inr exhausted) ↔
      primeOnlyMidpointOffDiagonal (depth + 2) = 0) ∧
    ((∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
        generatePrimePairActualityDisposition (directRuntimeActuality depth) =
          .obstruction generated) ↔
      primeOnlyMidpointOffDiagonal (depth + 2) = 0) ∧
    runtimePrimeOnlyFourierCoefficient depth =
      ((primeVonMangoldtWeight (depth + 2) ^ 2 +
          primeOnlyMidpointOffDiagonal (depth + 2) : ℝ) : ℂ) ∧
    actor.sourceOccurrence =
      (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (runtimeAt depth).current.visit.current ∧
    HEq (runtimeAt depth).tick.generated.wholeLedgerWriteBack
      ((runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt depth).current.visit.current) ∧
    (runtimeAt depth).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor (runtimeAt depth).state) ∧
    HEq ((Sum.inl ⟨runtimeActive depth, actor⟩) :
      SourceNativeProjectionFiberAt projectionLaw PUnit.unit
        (runtimeAt depth).emittedOccurrence)
      ((runtimeAt depth).tick.generated.projectionOutcome
        ((runtimeFacade.installationAt
            (runtimeAt depth) FaceAt.unitSelectedActor).embed
          (runtimeFacade.projectionAt
            (runtimeAt depth) FaceAt.unitSelectedActor))) := by
  dsimp only
  have row := runtime_actor_original_row_and_next depth
  exact ⟨runtime_actor_reached_iff_offDiagonal_pos depth midpointComposite,
    runtime_actor_exhausted_iff_offDiagonal_zero depth midpointComposite,
    runtime_original_obstruction_iff_offDiagonal_zero depth midpointComposite,
    runtimePrimeOnlyFourierCoefficient_eq_midpoint_sq_add_offDiagonal depth,
    row.2.1, row.2.2.1, row.2.2.2.1, row.2.2.2.2⟩

end
end GoldbachUnitSelectedActor
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
