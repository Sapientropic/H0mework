import H0mework.Foundation.Semantics.KernelPair
import H0mework.Versions.R2.Arithmetic.RiemannInverseFibre.CompleteFibre

/-!
# Reversal presentation and the surviving partner residual

Reversal removes exactly the installed chart label.  The unrestricted
partner coordinate survives as a kernel-pair invariant, so analytic
observation alone cannot produce a unique component.  This presentation
relation is deliberately not promoted to consumer-relative operational
equivalence; that requires the missing q-rich source separator.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization

noncomputable section

namespace InverseZeroFibre

def partnerResidual {observation : GeneratedRiemannZeroObservation} :
    InverseZeroFibre observation → ℂ
  | ⟨.left point _, _⟩ => point.pair.2
  | ⟨.right point _, _⟩ => point.pair.1

theorem partnerResidual_eq_forgetChart_decode
    {observation : GeneratedRiemannZeroObservation}
    (fibre : InverseZeroFibre observation) :
    partnerResidual fibre = forgetChart (decode fibre) := by
  rcases fibre with ⟨incidence, readback⟩
  cases incidence <;> rfl

@[simp] theorem partnerResidual_leftPreimage
    (observation : GeneratedRiemannZeroObservation) (partner : ℂ) :
    partnerResidual (leftPreimage observation partner) = partner :=
  rfl

@[simp] theorem partnerResidual_rightPreimage
    (observation : GeneratedRiemannZeroObservation) (partner : ℂ) :
    partnerResidual (rightPreimage observation partner) = partner :=
  rfl

def reversal (observation : GeneratedRiemannZeroObservation)
    (fibre : InverseZeroFibre observation) : InverseZeroFibre observation :=
  ⟨fibre.1.reversal, by
    rw [LawfulPointZeroIncidence.reversal_observation]
    exact fibre.2⟩

@[simp] theorem decode_reversal
    (observation : GeneratedRiemannZeroObservation)
    (fibre : InverseZeroFibre observation) :
    decode (reversal observation fibre) = flipChart (decode fibre) := by
  rcases fibre with ⟨incidence, readback⟩
  cases incidence <;> rfl

@[simp] theorem reversal_reversal
    (observation : GeneratedRiemannZeroObservation)
    (fibre : InverseZeroFibre observation) :
    reversal observation (reversal observation fibre) = fibre := by
  apply Subtype.ext
  exact LawfulPointZeroIncidence.reversal_reversal fibre.1

@[simp] theorem partnerResidual_reversal
    (observation : GeneratedRiemannZeroObservation)
    (fibre : InverseZeroFibre observation) :
    partnerResidual (reversal observation fibre) = partnerResidual fibre := by
  rcases fibre with ⟨incidence, readback⟩
  cases incidence <;> rfl

def ReversalPresentationEquivalent
    (observation : GeneratedRiemannZeroObservation)
    (left right : InverseZeroFibre observation) : Prop :=
  right = left ∨ right = reversal observation left

theorem reversalPresentationEquivalent_equivalence
    (observation : GeneratedRiemannZeroObservation) :
    Equivalence (ReversalPresentationEquivalent observation) := by
  refine ⟨?_, ?_, ?_⟩
  · intro fibre
    exact Or.inl rfl
  · intro left right equivalent
    rcases equivalent with rfl | reversed
    · exact Or.inl rfl
    · right
      rw [reversed, reversal_reversal]
  · intro left middle right leftMiddle middleRight
    rcases leftMiddle with rfl | middleReversed <;>
      rcases middleRight with rfl | rightReversed
    · exact Or.inl rfl
    · exact Or.inr rightReversed
    · exact Or.inr middleReversed
    · left
      rw [rightReversed, middleReversed, reversal_reversal]

theorem reversalPresentationEquivalent_iff_partnerResidual_eq
    (observation : GeneratedRiemannZeroObservation)
    (left right : InverseZeroFibre observation) :
    ReversalPresentationEquivalent observation left right ↔
      partnerResidual left = partnerResidual right := by
  constructor
  · intro equivalent
    rcases equivalent with rfl | reversed
    · rfl
    · rw [reversed, partnerResidual_reversal]
  · intro residualEq
    have residualDecodeEq :
        forgetChart (decode left) = forgetChart (decode right) := by
      rw [← partnerResidual_eq_forgetChart_decode,
        ← partnerResidual_eq_forgetChart_decode]
      exact residualEq
    cases leftDecode : decode left with
    | inl leftPartner =>
        cases rightDecode : decode right with
        | inl rightPartner =>
            left
            apply (completeEquiv observation).injective
            change decode right = decode left
            rw [rightDecode, leftDecode]
            congr
            rw [leftDecode, rightDecode] at residualDecodeEq
            exact residualDecodeEq.symm
        | inr rightPartner =>
            right
            apply (completeEquiv observation).injective
            change decode right = decode (reversal observation left)
            rw [rightDecode, decode_reversal, leftDecode]
            change Sum.inr rightPartner = Sum.inr leftPartner
            congr
            rw [leftDecode, rightDecode] at residualDecodeEq
            exact residualDecodeEq.symm
    | inr leftPartner =>
        cases rightDecode : decode right with
        | inl rightPartner =>
            right
            apply (completeEquiv observation).injective
            change decode right = decode (reversal observation left)
            rw [rightDecode, decode_reversal, leftDecode]
            change Sum.inl rightPartner = Sum.inl leftPartner
            congr
            rw [leftDecode, rightDecode] at residualDecodeEq
            exact residualDecodeEq.symm
        | inr rightPartner =>
            left
            apply (completeEquiv observation).injective
            change decode right = decode left
            rw [rightDecode, leftDecode]
            congr
            rw [leftDecode, rightDecode] at residualDecodeEq
            exact residualDecodeEq.symm

theorem reversalPresentationEquivalent_iff_kernelPair
    (observation : GeneratedRiemannZeroObservation)
    (left right : InverseZeroFibre observation) :
    ReversalPresentationEquivalent observation left right ↔
      KernelPair partnerResidual left right := by
  rw [reversalPresentationEquivalent_iff_partnerResidual_eq]
  rfl

theorem leftPreimage_zero_ne_one
    (observation : GeneratedRiemannZeroObservation) :
    leftPreimage observation 0 ≠ leftPreimage observation 1 := by
  intro equality
  have decoded := congrArg decode equality
  change Sum.inl (0 : ℂ) = Sum.inl (1 : ℂ) at decoded
  have impossible : (0 : ℂ) = 1 := Sum.inl.inj decoded
  exact zero_ne_one impossible

theorem leftPreimage_zero_not_reversalPresentationEquivalent_one
    (observation : GeneratedRiemannZeroObservation) :
    ¬ReversalPresentationEquivalent observation
      (leftPreimage observation 0) (leftPreimage observation 1) := by
  rw [reversalPresentationEquivalent_iff_partnerResidual_eq]
  simp

/-- No unique centre exists even after the analytic zero is fixed. -/
theorem no_unique_center (observation : GeneratedRiemannZeroObservation) :
    ¬∃ center : InverseZeroFibre observation,
      ∀ candidate, candidate = center := by
  rintro ⟨center, unique⟩
  exact leftPreimage_zero_ne_one observation
    ((unique (leftPreimage observation 0)).trans
      (unique (leftPreimage observation 1)).symm)

/-! Mathlib's paired point is one regression section, never a selector. -/

def mathlibReversalPartner
    (observation : GeneratedRiemannZeroObservation) : ℂ :=
  coordinateReversal observation.coordinate

def mathlibLeftRegressionComponent
    (observation : GeneratedRiemannZeroObservation) :
    InverseZeroFibre observation :=
  leftPreimage observation (mathlibReversalPartner observation)

def mathlibRightRegressionComponent
    (observation : GeneratedRiemannZeroObservation) :
    InverseZeroFibre observation :=
  rightPreimage observation (mathlibReversalPartner observation)

@[simp] theorem mathlibLeftRegressionComponent_partnerResidual
    (observation : GeneratedRiemannZeroObservation) :
    partnerResidual (mathlibLeftRegressionComponent observation) =
      mathlibReversalPartner observation :=
  rfl

@[simp] theorem mathlibRightRegressionComponent_partnerResidual
    (observation : GeneratedRiemannZeroObservation) :
    partnerResidual (mathlibRightRegressionComponent observation) =
      mathlibReversalPartner observation :=
  rfl

theorem mathlibLeftRegressionComponent_point
    (observation : GeneratedRiemannZeroObservation) :
    (mathlibLeftRegressionComponent observation).1.point =
      mathlibZeroPoint observation.coordinate observation.mathlibZero := by
  cases observation
  rfl

theorem mathlibRightRegressionComponent_point
    (observation : GeneratedRiemannZeroObservation) :
    (mathlibRightRegressionComponent observation).1.point =
      (mathlibZeroPoint observation.coordinate
        observation.mathlibZero).reversal := by
  cases observation
  rfl

theorem mathlibRightRegressionComponent_is_reversal
    (observation : GeneratedRiemannZeroObservation) :
    mathlibRightRegressionComponent observation =
      reversal observation (mathlibLeftRegressionComponent observation) := by
  rfl

end InverseZeroFibre

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
