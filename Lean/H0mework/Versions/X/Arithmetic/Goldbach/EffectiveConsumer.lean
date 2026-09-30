import H0mework.Versions.X.Arithmetic.Goldbach.EffectiveDisposition

/-!
# Direct consumer of the canonical effective additive face

The consumer is indexed by an actual effective fibre.  It simultaneously
uses the exact calculation occurrence, target fold, factorization-generated
prime restrictions, parallel landing, coordinate readout, runtime whole
ledger, and the compiler-generated next current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticEffectiveAdditiveConsumer

open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticRoot
open RootArithmeticUnfoldingFace
open SourceGeneratedEffectiveFibreDisposition

noncomputable section

/-- Complete direct-consumer contract.  Every field is a projection of the
same source-generated occurrence or of the effective fibre generated from
it. -/
structure ConsumesAt
    (index : Nat) (fibre : EffectiveAdditiveFibreAt index) : Prop where
  occurrenceRoot :
    (evenTargetOccurrence index).root.rootOccurrence =
      initialStep.generated.occurrence
  runtimeOccurrence :
    (runtimeAt 0).tick.generated.occurrence =
      initialStep.generated.occurrence
  targetRestriction :
    evenTargetHistory index =
      (evenTargetOccurrence index).fold terminalHistoryAlgebra
  factorizationOccurrence :
    (generatedEvenTargetFactorization index).occurrence =
      evenTargetOccurrence index
  factorizationTarget :
    (generatedEvenTargetFactorization index).target =
      evenTargetHistory index
  targetEven : Even (evenTargetHistory index).cardinalShadow
  leftRestrictionGenerated :
    fibre.leftHistory =
      (evenTargetFactorization index).actualPrimePowerHistory
        fibre.leftPrimeIndex (firstExponentIndex fibre.leftPrimeIndex)
  rightRestrictionGenerated :
    fibre.rightHistory =
      (evenTargetFactorization index).actualPrimePowerHistory
        fibre.rightPrimeIndex (firstExponentIndex fibre.rightPrimeIndex)
  leftPrime : Nat.Prime fibre.leftHistory.cardinalShadow
  rightPrime : Nat.Prime fibre.rightHistory.cardinalShadow
  leftFactorizationLanding :
    CanonicalUnitArithmeticFactorizationOccurrence.factorialHistory
        (evenTargetHistory index) =
      fibre.leftHistory.joint
        (generatedPrimeQuotientHistory fibre.leftPrimeIndex)
  rightFactorizationLanding :
    CanonicalUnitArithmeticFactorizationOccurrence.factorialHistory
        (evenTargetHistory index) =
      fibre.rightHistory.joint
        (generatedPrimeQuotientHistory fibre.rightPrimeIndex)
  fibreMembership :
    additiveEvaluation index fibre.1 = evenTargetHistory index
  parallelLanding :
    evenTargetHistory index =
      fibre.leftHistory.parallel fibre.rightHistory
  siblingFoldLanding :
    evenTargetHistory index =
      parallelChildren [fibre.leftHistory, fibre.rightHistory]
  coordinateTarget :
    (coordinateReadout fibre).target =
      (evenTargetHistory index).cardinalShadow
  coordinateLeft :
    (coordinateReadout fibre).left = fibre.leftHistory.cardinalShadow
  coordinateRight :
    (coordinateReadout fibre).right = fibre.rightHistory.cardinalShadow
  coordinateLanding :
    (coordinateReadout fibre).target =
      (coordinateReadout fibre).left + (coordinateReadout fibre).right
  dispositionGenerated :
    ∃ selected : EffectiveAdditiveFibreAt index,
      generatedAdditiveDisposition index = .inhabited selected
  wholeLedger :
    HEq (runtimeAt 0).tick.generated.wholeLedgerWriteBack
      ((runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt 0).current.visit.current)
  generatedNext :
    (runtimeAt 0).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor (runtimeAt 0).state)

/-- Direct consumption of the faithful residual branch.  The residual keeps
the complete effective image and proves that every actual prime-pair
candidate misses the generated target; the root compiler still supplies the
same whole-ledger write-back and next current. -/
structure ResidualConsumesAt
    (index : Nat) (residual : EffectiveAdditiveResidualAt index) : Prop where
  occurrenceRoot :
    (evenTargetOccurrence index).root.rootOccurrence =
      initialStep.generated.occurrence
  runtimeOccurrence :
    (runtimeAt 0).tick.generated.occurrence =
      initialStep.generated.occurrence
  targetRestriction :
    evenTargetHistory index =
      (evenTargetOccurrence index).fold terminalHistoryAlgebra
  factorizationOccurrence :
    (generatedEvenTargetFactorization index).occurrence =
      evenTargetOccurrence index
  factorizationTarget :
    (generatedEvenTargetFactorization index).target =
      evenTargetHistory index
  targetEven : Even (evenTargetHistory index).cardinalShadow
  imageGenerated :
    residual.image = candidateImage (additiveEvaluation index)
  targetMissing : evenTargetHistory index ∉ residual.image
  everyCandidateMisses :
    ∀ candidate : GeneratedPrimePairCandidateAt index,
      additiveEvaluation index candidate ≠ evenTargetHistory index
  fibreEmpty : IsEmpty (EffectiveAdditiveFibreAt index)
  wholeLedger :
    HEq (runtimeAt 0).tick.generated.wholeLedgerWriteBack
      ((runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt 0).current.visit.current)
  generatedNext :
    (runtimeAt 0).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor (runtimeAt 0).state)

theorem consumeResidual {index : Nat}
    (residual : EffectiveAdditiveResidualAt index) :
    ResidualConsumesAt index residual where
  occurrenceRoot := evenTargetOccurrence_root_is_exact index
  runtimeOccurrence := rfl
  targetRestriction := rfl
  factorizationOccurrence :=
    generatedEvenTargetFactorization_occurrence index
  factorizationTarget := generatedEvenTargetFactorization_target index
  targetEven := evenTargetHistory_is_even index
  imageGenerated := residual.image_eq
  targetMissing := residual.target_not_mem_image
  everyCandidateMisses := residual.misses
  fibreEmpty := residual.fibre_is_empty
  wholeLedger := (runtime_authority_factorizes 0).2.1
  generatedNext := (runtime_authority_factorizes 0).2.2

/-- Branch-preserving total consumer indexed by the exact generated
disposition.  Neither branch nor witness is accepted as an input. -/
inductive TotalConsumesAt (index : Nat) :
    EffectiveAdditiveDispositionAt index → Type where
  | inhabited (fibre : EffectiveAdditiveFibreAt index)
      (consumer : ConsumesAt index fibre) :
      TotalConsumesAt index (.inhabited fibre)
  | residual (residual : EffectiveAdditiveResidualAt index)
      (consumer : ResidualConsumesAt index residual) :
      TotalConsumesAt index (.residual residual)

/-- Direct construction from an actual fibre; no additional premise enters
the consumer. -/
theorem consume {index : Nat}
    (fibre : EffectiveAdditiveFibreAt index) : ConsumesAt index fibre where
  occurrenceRoot := evenTargetOccurrence_root_is_exact index
  runtimeOccurrence := rfl
  targetRestriction := rfl
  factorizationOccurrence :=
    generatedEvenTargetFactorization_occurrence index
  factorizationTarget := generatedEvenTargetFactorization_target index
  targetEven := evenTargetHistory_is_even index
  leftRestrictionGenerated := rfl
  rightRestrictionGenerated := rfl
  leftPrime := fibre.left_isPrime
  rightPrime := fibre.right_isPrime
  leftFactorizationLanding := fibre.left_factorization_lands
  rightFactorizationLanding := fibre.right_factorization_lands
  fibreMembership := fibre.membership
  parallelLanding := fibre.lands
  siblingFoldLanding := fibre.siblingFold_lands
  coordinateTarget := (coordinateReadout fibre).target_eq
  coordinateLeft := (coordinateReadout fibre).left_eq
  coordinateRight := (coordinateReadout fibre).right_eq
  coordinateLanding := (coordinateReadout fibre).target_eq_left_add_right
  dispositionGenerated := by
    let inhabited : Nonempty (EffectiveAdditiveFibreAt index) := ⟨fibre⟩
    exact ⟨Classical.choice inhabited,
      settle_eq_inhabited_of_nonempty _ _ inhabited⟩
  wholeLedger := (runtime_authority_factorizes 0).2.1
  generatedNext := (runtime_authority_factorizes 0).2.2

/-- Consume the framework-generated disposition itself.  The proof branches
only on `settle`'s internal decision and cannot be steered by a caller. -/
noncomputable def consumeGeneratedDisposition (index : Nat) :
    TotalConsumesAt index (generatedAdditiveDisposition index) := by
  unfold generatedAdditiveDisposition
  unfold SourceGeneratedEffectiveFibreDisposition.settle
  split
  · exact .inhabited _ (consume _)
  · exact .residual _ (consumeResidual _)

namespace TotalConsumesAt

variable {index : Nat} {disposition : EffectiveAdditiveDispositionAt index}

theorem occurrenceRoot
    (consumer : TotalConsumesAt index disposition) :
    (evenTargetOccurrence index).root.rootOccurrence =
      initialStep.generated.occurrence := by
  cases consumer with
  | inhabited _ positive => exact positive.occurrenceRoot
  | residual _ negative => exact negative.occurrenceRoot

theorem runtimeOccurrence
    (consumer : TotalConsumesAt index disposition) :
    (runtimeAt 0).tick.generated.occurrence =
      initialStep.generated.occurrence := by
  cases consumer with
  | inhabited _ positive => exact positive.runtimeOccurrence
  | residual _ negative => exact negative.runtimeOccurrence

theorem targetEven
    (consumer : TotalConsumesAt index disposition) :
    Even (evenTargetHistory index).cardinalShadow := by
  cases consumer with
  | inhabited _ positive => exact positive.targetEven
  | residual _ negative => exact negative.targetEven

theorem wholeLedger
    (consumer : TotalConsumesAt index disposition) :
    HEq (runtimeAt 0).tick.generated.wholeLedgerWriteBack
      ((runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt 0).current.visit.current) := by
  cases consumer with
  | inhabited _ positive => exact positive.wholeLedger
  | residual _ negative => exact negative.wholeLedger

theorem generatedNext
    (consumer : TotalConsumesAt index disposition) :
    (runtimeAt 0).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor (runtimeAt 0).state) := by
  cases consumer with
  | inhabited _ positive => exact positive.generatedNext
  | residual _ negative => exact negative.generatedNext

end TotalConsumesAt

theorem zeroResidualConsumer :
    ResidualConsumesAt 0 evenTargetZeroResidual :=
  consumeResidual evenTargetZeroResidual

noncomputable def zeroTotalConsumer :
    TotalConsumesAt 0 (generatedAdditiveDisposition 0) := by
  rw [generatedAdditiveDisposition_zero_eq_residual]
  exact .residual evenTargetZeroResidual zeroResidualConsumer

theorem goldbachConsumer : ConsumesAt 1 goldbachAdditiveFibre :=
  consume goldbachAdditiveFibre

theorem goldbachConsumer_returns_two_plus_two :
    (coordinateReadout goldbachAdditiveFibre).target = 4 ∧
      (coordinateReadout goldbachAdditiveFibre).left = 2 ∧
      (coordinateReadout goldbachAdditiveFibre).right = 2 := by
  exact ⟨rfl, rfl, rfl⟩

end
end CanonicalUnitArithmeticEffectiveAdditiveConsumer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
