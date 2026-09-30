import H0mework.Versions.X.Arithmetic.Goldbach.EffectiveDisposition

/-!
# Runtime-free effective additive readout

This consumer retains exactly the mathematical content of an actual effective
fibre or faithful residual.  It deliberately contains no runtime occurrence,
ledger or next-current field; live authority is supplied only by the named
operational facade which embeds this readout.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticEffectiveAdditiveReadoutConsumer

open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticRoot
open RootArithmeticUnfoldingFace
open SourceGeneratedEffectiveFibreDisposition

noncomputable section

structure PositiveReadoutAt
    (index : Nat) (fibre : EffectiveAdditiveFibreAt index) : Prop where
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
    factorialHistory (evenTargetHistory index) =
      fibre.leftHistory.joint
        (generatedPrimeQuotientHistory fibre.leftPrimeIndex)
  rightFactorizationLanding :
    factorialHistory (evenTargetHistory index) =
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

structure ResidualReadoutAt
    (index : Nat) (residual : EffectiveAdditiveResidualAt index) : Prop where
  targetEven : Even (evenTargetHistory index).cardinalShadow
  imageGenerated :
    residual.image = candidateImage (additiveEvaluation index)
  targetMissing : evenTargetHistory index ∉ residual.image
  everyCandidateMisses : ∀ candidate : GeneratedPrimePairCandidateAt index,
    additiveEvaluation index candidate ≠ evenTargetHistory index
  fibreEmpty : IsEmpty (EffectiveAdditiveFibreAt index)

inductive TotalReadoutAt (index : Nat) :
    EffectiveAdditiveDispositionAt index → Type where
  | inhabited (fibre : EffectiveAdditiveFibreAt index)
      (readout : PositiveReadoutAt index fibre) :
      TotalReadoutAt index (.inhabited fibre)
  | residual (residual : EffectiveAdditiveResidualAt index)
      (readout : ResidualReadoutAt index residual) :
      TotalReadoutAt index (.residual residual)

theorem consumePositive {index : Nat}
    (fibre : EffectiveAdditiveFibreAt index) :
    PositiveReadoutAt index fibre where
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

theorem consumeResidual {index : Nat}
    (residual : EffectiveAdditiveResidualAt index) :
    ResidualReadoutAt index residual where
  targetEven := evenTargetHistory_is_even index
  imageGenerated := residual.image_eq
  targetMissing := residual.target_not_mem_image
  everyCandidateMisses := residual.misses
  fibreEmpty := residual.fibre_is_empty

def consumeDisposition {index : Nat}
    (disposition : EffectiveAdditiveDispositionAt index) :
    TotalReadoutAt index disposition :=
  match disposition with
  | .inhabited fibre => .inhabited fibre (consumePositive fibre)
  | .residual residual => .residual residual (consumeResidual residual)

end
end CanonicalUnitArithmeticEffectiveAdditiveReadoutConsumer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
