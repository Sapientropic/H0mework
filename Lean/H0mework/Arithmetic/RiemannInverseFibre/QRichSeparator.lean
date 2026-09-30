import H0mework.Arithmetic.RiemannInverseFibre.Disposition
import H0mework.Arithmetic.RiemannLineage.FullRowPairSeparator

/-!
# Branch-normalized q-rich separator on the complete inverse fibre

The universal pair-coefficient full-row separator is specialized only after
one lawful inverse-fibre component is supplied.  Chart orientation contributes
the visible normalization sign; the resulting value depends exactly on the
observer coordinate minus the surviving partner residual and is invariant
under reversal presentation.

This module classifies the separator-zero locus.  It does not assert that the
source-generated analytic component lies in that locus; integral/global
descent remains the producer responsible for such a vanishing theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization
open QRich

noncomputable section

namespace InverseZeroFibre

/-- Reversal-normalized specialization of the source-generated C separator. -/
def branchNormalizedQRichSeparator
    {observation : GeneratedRiemannZeroObservation}
    (fibre : InverseZeroFibre observation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) : ℂ :=
  match fibre.1 with
  | .left point _ => QRich.pointFullRowCSeparatorValue point stage row
  | .right point _ => -QRich.pointFullRowCSeparatorValue point stage row

theorem branchNormalizedQRichSeparator_eq
    {observation : GeneratedRiemannZeroObservation}
    (fibre : InverseZeroFibre observation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    branchNormalizedQRichSeparator fibre stage row =
      -(quotientCoefficient row : ℂ) *
        (observation.coordinate - partnerResidual fibre) := by
  rcases fibre with ⟨incidence, readback⟩
  cases incidence with
  | left point zero =>
      have selected := congrArg
        GeneratedRiemannZeroObservationAt.coordinate readback
      change point.pair.1 = observation.coordinate at selected
      change QRich.pointFullRowCSeparatorValue point stage row = _
      rw [QRich.pointFullRowCSeparatorValue_eq]
      change -(quotientCoefficient row : ℂ) *
          (point.pair.1 - point.pair.2) =
        -(quotientCoefficient row : ℂ) *
          (observation.coordinate - point.pair.2)
      rw [selected]
  | right point zero =>
      have selected := congrArg
        GeneratedRiemannZeroObservationAt.coordinate readback
      change point.pair.2 = observation.coordinate at selected
      change -QRich.pointFullRowCSeparatorValue point stage row = _
      rw [QRich.pointFullRowCSeparatorValue_eq]
      change -(-(quotientCoefficient row : ℂ) *
          (point.pair.1 - point.pair.2)) =
        -(quotientCoefficient row : ℂ) *
          (observation.coordinate - point.pair.1)
      rw [← selected]
      ring

theorem branchNormalizedQRichSeparator_eq_zero_iff
    {observation : GeneratedRiemannZeroObservation}
    (fibre : InverseZeroFibre observation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    branchNormalizedQRichSeparator fibre stage row = 0 ↔
      partnerResidual fibre = observation.coordinate := by
  rw [branchNormalizedQRichSeparator_eq]
  have coefficientNe : (quotientCoefficient row : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (QRich.blockQRichQuotientCoefficient_ne_zero stage row)
  constructor
  · intro zero
    have differenceZero :
        observation.coordinate - partnerResidual fibre = 0 := by
      rcases mul_eq_zero.mp zero with coefficientZero | differenceZero
      · exact False.elim ((neg_ne_zero.mpr coefficientNe) coefficientZero)
      · exact differenceZero
    exact (sub_eq_zero.mp differenceZero).symm
  · intro residualEq
    rw [residualEq, sub_self, mul_zero]

@[simp] theorem branchNormalizedQRichSeparator_reversal
    (observation : GeneratedRiemannZeroObservation)
    (fibre : InverseZeroFibre observation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    branchNormalizedQRichSeparator
        (reversal observation fibre) stage row =
      branchNormalizedQRichSeparator fibre stage row := by
  rw [branchNormalizedQRichSeparator_eq,
    branchNormalizedQRichSeparator_eq,
    partnerResidual_reversal]

theorem branchNormalizedQRichSeparator_eq_of_kernelPair
    {observation : GeneratedRiemannZeroObservation}
    {left right : InverseZeroFibre observation}
    (sameResidual : KernelPair partnerResidual left right)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    branchNormalizedQRichSeparator left stage row =
      branchNormalizedQRichSeparator right stage row := by
  rw [branchNormalizedQRichSeparator_eq,
    branchNormalizedQRichSeparator_eq, sameResidual]

/-- Any two separator-zero candidates are the same reversal-presentation
class.  This is uniqueness of the zero locus, not a proof that an externally
named component belongs to it. -/
theorem separatorZero_reversalPresentationEquivalent
    {observation : GeneratedRiemannZeroObservation}
    {left right : InverseZeroFibre observation}
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (leftZero : branchNormalizedQRichSeparator left stage row = 0)
    (rightZero : branchNormalizedQRichSeparator right stage row = 0) :
    ReversalPresentationEquivalent observation left right := by
  rw [reversalPresentationEquivalent_iff_partnerResidual_eq]
  have leftResidual :=
    (branchNormalizedQRichSeparator_eq_zero_iff left stage row).mp leftZero
  have rightResidual :=
    (branchNormalizedQRichSeparator_eq_zero_iff right stage row).mp rightZero
  exact leftResidual.trans rightResidual.symm

/-- The diagonal conditional preimage witnesses that the separator-zero
presentation class is inhabited without choosing from the fibre. -/
def diagonalSeparatorZeroPreimage
    (observation : GeneratedRiemannZeroObservation) :
    InverseZeroFibre observation :=
  leftPreimage observation observation.coordinate

theorem diagonalSeparatorZeroPreimage_zero
    (observation : GeneratedRiemannZeroObservation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    branchNormalizedQRichSeparator
        (diagonalSeparatorZeroPreimage observation) stage row = 0 := by
  rw [branchNormalizedQRichSeparator_eq_zero_iff]
  rfl

theorem incidentPoint_pair_fixed_of_separator_zero
    {observation : GeneratedRiemannZeroObservation}
    (fibre : InverseZeroFibre observation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (separatorZero : branchNormalizedQRichSeparator fibre stage row = 0) :
    fibre.1.point.pair.1 = fibre.1.point.pair.2 := by
  have residualEq :=
    (branchNormalizedQRichSeparator_eq_zero_iff fibre stage row).mp
      separatorZero
  rcases fibre with ⟨incidence, readback⟩
  cases incidence with
  | left point zero =>
      have selected := congrArg
        GeneratedRiemannZeroObservationAt.coordinate readback
      change point.pair.2 = observation.coordinate at residualEq
      exact selected.trans residualEq.symm
  | right point zero =>
      have selected := congrArg
        GeneratedRiemannZeroObservationAt.coordinate readback
      change point.pair.1 = observation.coordinate at residualEq
      exact residualEq.trans selected.symm

end InverseZeroFibre

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
