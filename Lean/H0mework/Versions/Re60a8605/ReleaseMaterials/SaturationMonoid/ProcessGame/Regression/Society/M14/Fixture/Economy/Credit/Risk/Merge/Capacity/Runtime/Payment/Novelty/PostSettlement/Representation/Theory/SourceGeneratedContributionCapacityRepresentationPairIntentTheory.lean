import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.World.SourceGeneratedContributionCapacityRepresentationClaimWorld

/-!
# Fixed two-law representation-intent theory

Raw programs remain the future-free functions `Visible → Nat`.  A program's
claim is obtained by running that same program at the two generated visible
inputs.  The actual obstruction claim is independently read from the two
actual current codes.  Same visible input forces every program claim onto the
diagonal, whereas the actual claim is strictly off-diagonal.

The inventory contains two laws, one per occurrence slot.  Simultaneous
realization is empty, but deleting either law admits an explicit constant
program realizing the surviving slot.  This is a strict residual witness,
not a renamed `Expresses`, `Complete`, failure fibre or truth-indexed
characteristic denotation.

This file proves the mathematical failure candidate.  It does not yet claim
that the theory is a root law surface or that the failure is installed; the
sequential target root must establish that causal order.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityFinitePrefixAuthorityObserver
open M14SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference
open M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking
open M14SourceGeneratedContributionCapacityFinitePrefixOperationalCode
open M14SourceInstalledContributionCapacityFinitePrefixRepresentation
open M14SourceGeneratedContributionCapacityRepresentationIntentActionMaterial
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld

abbrev RepresentationIntentExpressionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (BaseNAt oldVisit sourceIndex boundary).Claim ⊕
    FinitePrefixOperationalProgramAt boundary

/-- Fixed denotation: evaluate the same raw program at the two visible
inputs.  No completeness predicate, target equality or failure test occurs. -/
def representationPairReadoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (program : FinitePrefixOperationalProgramAt boundary) :
    RepresentationPairIntent :=
  let incidence := canonicalIncidenceAt oldVisit sourceIndex boundary
  (program
      ((finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex boundary
        ).forget incidence.leftReplay),
    program
      ((finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex boundary
        ).forget incidence.rightReplay))

def representationIntentSlotReplayAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Fin 2 → AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex :=
  let incidence := canonicalIncidenceAt oldVisit sourceIndex boundary
  fun slot => if slot = 0 then incidence.leftReplay else incidence.rightReplay

def representationIntentSlotVisibleAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) (slot : Fin 2) :=
  (finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex boundary
    ).forget
      (representationIntentSlotReplayAt oldVisit sourceIndex boundary slot)

def representationIntentSlotCurrentAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) (slot : Fin 2) : Nat :=
  replayAuthorityCurrentCodeAt
    (representationIntentSlotReplayAt oldVisit sourceIndex boundary slot)

/-- Both local laws must be realized by one raw program. -/
abbrev StrictRepresentationPairRealizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  Sigma fun program : FinitePrefixOperationalProgramAt boundary =>
    PLift (∀ slot : Fin 2,
      program
          (representationIntentSlotVisibleAt oldVisit sourceIndex boundary
            slot) =
        representationIntentSlotCurrentAt oldVisit sourceIndex boundary slot)

/-- Deleting one law retains only the other slot's requirement. -/
abbrev StrictRepresentationPairRealizationWithoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (deleted : Fin 2) :=
  Sigma fun program : FinitePrefixOperationalProgramAt boundary =>
    PLift (∀ slot : Fin 2, slot ≠ deleted →
      program
          (representationIntentSlotVisibleAt oldVisit sourceIndex boundary
            slot) =
        representationIntentSlotCurrentAt oldVisit sourceIndex boundary slot)

def strictRepresentationIntentRealizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {support : (RepresentationClaimNAt oldVisit sourceIndex boundary).Support} :
    (RepresentationClaimNAt oldVisit sourceIndex boundary).ObstructionAt
        support → Type :=
  representationObstructionCasesAt oldVisit sourceIndex boundary
    (fun _ => PUnit)
    (StrictRepresentationPairRealizationAt oldVisit sourceIndex boundary)

def strictRepresentationIntentRealizationWithoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (deleted : Fin 2)
    {support : (RepresentationClaimNAt oldVisit sourceIndex boundary).Support} :
    (RepresentationClaimNAt oldVisit sourceIndex boundary).ObstructionAt
        support → Type :=
  representationObstructionCasesAt oldVisit sourceIndex boundary
    (fun _ => PUnit)
    (StrictRepresentationPairRealizationWithoutAt oldVisit sourceIndex boundary
      deleted)

def representationPairIntentTheoryAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    TheoryState (RepresentationClaimNAt oldVisit sourceIndex boundary) where
  inventory :=
    { Version := PUnit
      version := ()
      Law := Fin 2
      RealizationAt :=
        strictRepresentationIntentRealizationAt oldVisit sourceIndex boundary
      RealizationWithoutAt :=
        strictRepresentationIntentRealizationWithoutAt oldVisit sourceIndex
          boundary }
  ExpressionAt := fun _ =>
    RepresentationIntentExpressionAt oldVisit sourceIndex boundary
  denotes := fun expression =>
    match expression with
    | .inl oldClaim => .inl oldClaim
    | .inr program =>
        .inr (representationPairReadoutAt oldVisit sourceIndex boundary program)
  TheoremAt := fun {support} expression =>
    (RepresentationClaimNAt oldVisit sourceIndex boundary).HoldsAt support
      (match expression with
      | .inl oldClaim => .inl oldClaim
      | .inr program =>
          .inr
            (representationPairReadoutAt oldVisit sourceIndex boundary program))
  theoremPresentation := fun _ => ConstructivePresentation.refl _

def representationPairIntentTheory_rootSemantic
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConservativeTheoryTranslation
      (representationPairIntentTheoryAt oldVisit sourceIndex boundary)
      (TheoryState.rootSemantic
        (RepresentationClaimNAt oldVisit sourceIndex boundary)) where
  compile :=
    (representationPairIntentTheoryAt oldVisit sourceIndex boundary).denotes
  commuting := fun _ => rfl

theorem representationPairReadout_ne_actual
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (program : FinitePrefixOperationalProgramAt boundary) :
    representationPairReadoutAt oldVisit sourceIndex boundary program ≠
      actualRepresentationPairIntentAt oldVisit sourceIndex boundary := by
  intro pair_eq
  let incidence := canonicalIncidenceAt oldVisit sourceIndex boundary
  let breaking := sourceGeneratedFinitePrefixRepresentationBreakingAt oldVisit
    sourceIndex boundary
  have visible_eq := breaking.sameInstalledVisibleDifferentK.1
  have program_eq := congrArg program visible_eq
  have left_eq := congrArg Prod.fst pair_eq
  have right_eq := congrArg Prod.snd pair_eq
  change
    program
        ((finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex boundary
          ).forget incidence.leftReplay) =
      replayAuthorityCurrentCodeAt incidence.leftReplay at left_eq
  change
    program
        ((finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex boundary
          ).forget incidence.rightReplay) =
      replayAuthorityCurrentCodeAt incidence.rightReplay at right_eq
  have current_eq :
      replayAuthorityCurrentCodeAt incidence.leftReplay =
        replayAuthorityCurrentCodeAt incidence.rightReplay :=
    left_eq.symm.trans (program_eq.trans right_eq)
  exact (Nat.ne_of_lt incidence.leftCurrent_lt_rightCurrent) current_eq

theorem strictRepresentationPairRealization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IsEmpty
      (StrictRepresentationPairRealizationAt oldVisit sourceIndex boundary) := by
  constructor
  rintro ⟨program, realizes⟩
  let incidence := canonicalIncidenceAt oldVisit sourceIndex boundary
  have left_exact :
      program
          ((finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex
            boundary).forget incidence.leftReplay) =
        replayAuthorityCurrentCodeAt incidence.leftReplay := by
    simpa [representationIntentSlotVisibleAt,
      representationIntentSlotCurrentAt, representationIntentSlotReplayAt]
      using realizes.down (0 : Fin 2)
  have right_exact :
      program
          ((finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex
            boundary).forget incidence.rightReplay) =
        replayAuthorityCurrentCodeAt incidence.rightReplay := by
    simpa [representationIntentSlotVisibleAt,
      representationIntentSlotCurrentAt, representationIntentSlotReplayAt]
      using realizes.down (1 : Fin 2)
  have program_eq := congrArg program
    (finitePrefixInstalledKernelPairAt incidence).visible_eq
  have current_eq :
      replayAuthorityCurrentCodeAt incidence.leftReplay =
        replayAuthorityCurrentCodeAt incidence.rightReplay :=
    left_exact.symm.trans (program_eq.trans right_exact)
  exact (Nat.ne_of_lt incidence.leftCurrent_lt_rightCurrent) current_eq

theorem strictRepresentationPairRealizationWithout_nonempty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (deleted : Fin 2) :
    Nonempty
      (StrictRepresentationPairRealizationWithoutAt oldVisit sourceIndex
        boundary deleted) := by
  fin_cases deleted
  · let incidence := canonicalIncidenceAt oldVisit sourceIndex boundary
    refine ⟨⟨fun _ => replayAuthorityCurrentCodeAt incidence.rightReplay,
      ⟨?_⟩⟩⟩
    intro slot slot_ne
    fin_cases slot
    · exact False.elim (slot_ne rfl)
    · simp [representationIntentSlotCurrentAt,
        representationIntentSlotReplayAt]
  · let incidence := canonicalIncidenceAt oldVisit sourceIndex boundary
    refine ⟨⟨fun _ => replayAuthorityCurrentCodeAt incidence.leftReplay,
      ⟨?_⟩⟩⟩
    intro slot slot_ne
    fin_cases slot
    · simp [representationIntentSlotCurrentAt,
        representationIntentSlotReplayAt]
    · exact False.elim (slot_ne rfl)

def representationPairIntentFailureAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ActualExpressibilityFailure
      (representationPairIntentTheoryAt oldVisit sourceIndex boundary)
      (generatedRepresentationObstructionAt oldVisit sourceIndex boundary) where
  notExpressible := by
    constructor
    rintro ⟨expression, denotes_eq⟩
    cases expression with
    | inl oldClaim =>
        change Sum.inl oldClaim = Sum.inr _ at denotes_eq
        cases denotes_eq
    | inr program =>
        change
          Sum.inr
              (representationPairReadoutAt oldVisit sourceIndex boundary
                program) =
            Sum.inr
              (actualRepresentationPairIntentAt oldVisit sourceIndex boundary)
          at denotes_eq
        exact representationPairReadout_ne_actual oldVisit sourceIndex boundary
          program (Sum.inr.inj denotes_eq)
  noLawfulRealization :=
    strictRepresentationPairRealization_isEmpty oldVisit sourceIndex boundary

theorem representationPairIntentStrictDeletionResidual_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let sourceEvent :=
      representationIntentActionExactSourceEventAt oldVisit sourceIndex boundary
    let material := sourceGeneratedRepresentationIntentActionMaterialAt
      oldVisit sourceIndex boundary sourceEvent
    type_of% material.sourceOccurrenceExact ∧
      type_of% material.breakingGenerated.sameInstalledVisibleDifferentK ∧
      Nonempty (FinitePrefixOperationalProgramAt boundary) ∧
      Nonempty
        (ActualExpressibilityFailure
          (representationPairIntentTheoryAt oldVisit sourceIndex boundary)
          (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)) ∧
      (∀ deleted : Fin 2,
        Nonempty
          ((representationPairIntentTheoryAt oldVisit sourceIndex boundary
            ).inventory.RealizationWithoutAt deleted
              (generatedRepresentationObstructionAt oldVisit sourceIndex
                boundary))) := by
  dsimp
  let sourceEvent :=
    representationIntentActionExactSourceEventAt oldVisit sourceIndex boundary
  let material := sourceGeneratedRepresentationIntentActionMaterialAt oldVisit
    sourceIndex boundary sourceEvent
  exact
    ⟨material.sourceOccurrenceExact,
      material.breakingGenerated.sameInstalledVisibleDifferentK,
      ⟨finitePrefixOperationalProgramAt oldVisit sourceIndex boundary⟩,
      ⟨representationPairIntentFailureAt oldVisit sourceIndex boundary⟩,
      strictRepresentationPairRealizationWithout_nonempty oldVisit sourceIndex
        boundary⟩

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory.representationPairIntentTheoryAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory.representationPairIntentTheory_rootSemantic
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory.representationPairReadout_ne_actual
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory.strictRepresentationPairRealization_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory.strictRepresentationPairRealizationWithout_nonempty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory.representationPairIntentFailureAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory.representationPairIntentStrictDeletionResidual_directConsumer
