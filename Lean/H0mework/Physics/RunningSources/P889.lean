import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.AlphaSpectrum.P888

/-!
# Proposition 889: matrix-block-index producer for the alpha_s threshold zero

P877 made the threshold source a paired spectrum, but the carrier was still
the opaque `Fin 7`.  P888 identifies the real P286 matrix-level block index:

`GaugeProjection.ConcreteBlockDiagonal.SMBlockIndex =
  Fin 3 ⊕ (Fin 2 ⊕ (Fin 1 ⊕ Fin 1))`.

This file lowers the threshold zero to that concrete carrier.  The low-energy
threshold side and the unified threshold side are distinct wrapper fibers over
the same concrete block index, and the pairing is the fiberwise identity.  The
zero is therefore produced by the concrete SU(7) block carrier rather than by a
bare `Fin 7` receipt.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open scoped BigOperators

set_option linter.defProp false

/-! ## Concrete threshold block modes -/

/-- Low-energy threshold modes as a physical wrapper over the concrete P286
matrix block index. -/
structure SU7ThresholdLowEnergyBlockMode where
  idx : SU7BreakingSMBlockIndexMode
  deriving DecidableEq, Repr, FintypeViaProxy

/-- Unified threshold modes as a second physical wrapper over the same concrete
P286 matrix block index. -/
structure SU7ThresholdUnifiedBlockMode where
  idx : SU7BreakingSMBlockIndexMode
  deriving DecidableEq, Repr, FintypeViaProxy

/-- Low-energy threshold wrapper forgets faithfully to the concrete block
index. -/
def SU7ThresholdLowEnergyBlockMode.equivSMBlockIndex :
    SU7ThresholdLowEnergyBlockMode ≃ SU7BreakingSMBlockIndexMode where
  toFun x := x.idx
  invFun i := ⟨i⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro i
    rfl

/-- Unified threshold wrapper forgets faithfully to the concrete block index. -/
def SU7ThresholdUnifiedBlockMode.equivSMBlockIndex :
    SU7ThresholdUnifiedBlockMode ≃ SU7BreakingSMBlockIndexMode where
  toFun x := x.idx
  invFun i := ⟨i⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro i
    rfl

/-- THEOREM 1: the low-energy threshold wrapper has seven modes because the
concrete block index has seven modes. -/
theorem su7ThresholdLowEnergyBlockMode_card_eq_seven :
    Fintype.card SU7ThresholdLowEnergyBlockMode = 7 :=
  (Fintype.card_congr
    SU7ThresholdLowEnergyBlockMode.equivSMBlockIndex).trans
      su7BreakingSMBlockIndexMode_card_eq_seven

/-- THEOREM 2: the unified threshold wrapper has seven modes because the
concrete block index has seven modes. -/
theorem su7ThresholdUnifiedBlockMode_card_eq_seven :
    Fintype.card SU7ThresholdUnifiedBlockMode = 7 :=
  (Fintype.card_congr
    SU7ThresholdUnifiedBlockMode.equivSMBlockIndex).trans
      su7BreakingSMBlockIndexMode_card_eq_seven

/-- Fiberwise threshold pairing between the two physical threshold wrappers. -/
def su7ThresholdSMBlockIndexPair :
    SU7ThresholdLowEnergyBlockMode ≃ SU7ThresholdUnifiedBlockMode where
  toFun x := ⟨x.idx⟩
  invFun x := ⟨x.idx⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-! ## Threshold traces from the concrete block index -/

/-- Low-energy threshold trace generated from the concrete block-index
wrapper. -/
def thresholdSMBlockIndexLowEnergyTrace : ℚ :=
  finiteUnitSpectrumTrace SU7ThresholdLowEnergyBlockMode

/-- Unified threshold trace generated from the concrete block-index wrapper. -/
def thresholdSMBlockIndexUnifiedTrace : ℚ :=
  finiteUnitSpectrumTrace SU7ThresholdUnifiedBlockMode

/-- THEOREM 3: the concrete block-index low-energy threshold trace is seven. -/
theorem thresholdSMBlockIndexLowEnergyTrace_eq_seven :
    thresholdSMBlockIndexLowEnergyTrace = 7 := by
  unfold thresholdSMBlockIndexLowEnergyTrace
  rw [finiteUnitSpectrumTrace_eq_card,
    su7ThresholdLowEnergyBlockMode_card_eq_seven]
  norm_num

/-- THEOREM 4: the concrete block-index unified threshold trace is seven. -/
theorem thresholdSMBlockIndexUnifiedTrace_eq_seven :
    thresholdSMBlockIndexUnifiedTrace = 7 := by
  unfold thresholdSMBlockIndexUnifiedTrace
  rw [finiteUnitSpectrumTrace_eq_card,
    su7ThresholdUnifiedBlockMode_card_eq_seven]
  norm_num

/-- Concrete block-index threshold paired spectrum. -/
def thresholdSMBlockIndexPairedSpectrum :
    PairedRepresentationSpectrum SU7ThresholdLowEnergyBlockMode
      SU7ThresholdUnifiedBlockMode where
  leftWeight := fun _ => 1
  rightWeight := fun _ => 1
  pair := su7ThresholdSMBlockIndexPair
  paired_weight := by
    intro _
    rfl

/-- Concrete block-index threshold imbalance. -/
def thresholdSMBlockIndexPairedSpectrumImbalance : ℚ :=
  thresholdSMBlockIndexPairedSpectrum.imbalance

/-- THEOREM 5: the concrete block-index threshold imbalance is zero. -/
theorem thresholdSMBlockIndexPairedSpectrumImbalance_eq_zero :
    thresholdSMBlockIndexPairedSpectrumImbalance = 0 := by
  unfold thresholdSMBlockIndexPairedSpectrumImbalance
  exact PairedRepresentationSpectrum.imbalance_eq_zero
    thresholdSMBlockIndexPairedSpectrum

/-- THEOREM 6: the concrete block-index threshold imbalance agrees with the
P856 generated threshold imbalance. -/
theorem thresholdSMBlockIndexPairedSpectrumImbalance_eq_generated :
    thresholdSMBlockIndexPairedSpectrumImbalance =
      alphaStrongThresholdGeneratedImbalance := by
  rw [thresholdSMBlockIndexPairedSpectrumImbalance_eq_zero,
    alphaStrongThresholdGeneratedImbalance_eq_zero]

/-- Threshold contribution generated from the concrete block-index paired
spectrum. -/
def thresholdSMBlockIndexPairedSpectrumContribution : ℚ :=
  thresholdSMBlockIndexPairedSpectrumImbalance /
    canonicalAlphaStrongRepresentationSpectrumPacket.resolutionDenominator

/-- THEOREM 7: the concrete block-index threshold contribution is zero. -/
theorem thresholdSMBlockIndexPairedSpectrumContribution_eq_zero :
    thresholdSMBlockIndexPairedSpectrumContribution = 0 := by
  unfold thresholdSMBlockIndexPairedSpectrumContribution
  rw [thresholdSMBlockIndexPairedSpectrumImbalance_eq_zero]
  norm_num

/-- THEOREM 8: the concrete block-index threshold contribution agrees with
P877's paired-spectrum threshold contribution. -/
theorem thresholdSMBlockIndexPairedSpectrumContribution_eq_p877 :
    thresholdSMBlockIndexPairedSpectrumContribution =
      thresholdPairedSpectrumContribution := by
  rw [thresholdSMBlockIndexPairedSpectrumContribution_eq_zero,
    thresholdPairedSpectrumContribution_eq_zero]

/-! ## Alpha_s vector with concrete threshold source -/

/-- Four-source vector whose threshold coordinate is generated by the concrete
matrix-block-index threshold pairing. -/
def alphaStrongSMBlockIndexThresholdFourSourceVector :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking =>
      alphaStrongSMBlockIndexPartitionFourSourceVector .su7Breaking
  | .threshold => thresholdSMBlockIndexPairedSpectrumContribution
  | .threeLoopRG =>
      alphaStrongSMBlockIndexPartitionFourSourceVector .threeLoopRG
  | .higgsExtraRepresentation =>
      alphaStrongSMBlockIndexPartitionFourSourceVector .higgsExtraRepresentation

/-- THEOREM 9: replacing the threshold coordinate by the concrete block-index
threshold producer leaves the P888 vector unchanged. -/
theorem alphaStrongSMBlockIndexThresholdFourSourceVector_eq_p888 :
    alphaStrongSMBlockIndexThresholdFourSourceVector =
      alphaStrongSMBlockIndexPartitionFourSourceVector := by
  funext source
  cases source
  · rfl
  · exact thresholdSMBlockIndexPairedSpectrumContribution_eq_p877
  · rfl
  · rfl

/-- THEOREM 10: the concrete block-index threshold vector transports to the
exact inverse alpha_s residual. -/
theorem alphaStrongSMBlockIndexThresholdFourSourceVector_outputs_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongSMBlockIndexThresholdFourSourceVector s) =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongSMBlockIndexThresholdFourSourceVector_eq_p888]
  exact alphaStrongSMBlockIndexPartitionFourSourceVector_outputs_residual

/-! ## Certificate -/

/-- P889 certificate: the threshold zero source is generated from the actual
matrix-level SU(7) block index carrier rather than from a bare `Fin 7`. -/
structure AlphaStrongSMBlockIndexThresholdProducerCertificate : Prop where
  low_card :
    Fintype.card SU7ThresholdLowEnergyBlockMode = 7
  unified_card :
    Fintype.card SU7ThresholdUnifiedBlockMode = 7
  low_trace :
    thresholdSMBlockIndexLowEnergyTrace = 7
  unified_trace :
    thresholdSMBlockIndexUnifiedTrace = 7
  threshold_zero :
    thresholdSMBlockIndexPairedSpectrumImbalance = 0
  threshold_generated :
    thresholdSMBlockIndexPairedSpectrumImbalance =
      alphaStrongThresholdGeneratedImbalance
  threshold_p877 :
    thresholdSMBlockIndexPairedSpectrumContribution =
      thresholdPairedSpectrumContribution
  vector_p888 :
    alphaStrongSMBlockIndexThresholdFourSourceVector =
      alphaStrongSMBlockIndexPartitionFourSourceVector
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongSMBlockIndexThresholdFourSourceVector s) =
      -((89000 : ℚ) / 128511)

/-- THEOREM 11: canonical concrete threshold producer certificate. -/
def alphaStrongSMBlockIndexThresholdProducerCertificate :
    AlphaStrongSMBlockIndexThresholdProducerCertificate where
  low_card := su7ThresholdLowEnergyBlockMode_card_eq_seven
  unified_card := su7ThresholdUnifiedBlockMode_card_eq_seven
  low_trace := thresholdSMBlockIndexLowEnergyTrace_eq_seven
  unified_trace := thresholdSMBlockIndexUnifiedTrace_eq_seven
  threshold_zero := thresholdSMBlockIndexPairedSpectrumImbalance_eq_zero
  threshold_generated :=
    thresholdSMBlockIndexPairedSpectrumImbalance_eq_generated
  threshold_p877 := thresholdSMBlockIndexPairedSpectrumContribution_eq_p877
  vector_p888 := alphaStrongSMBlockIndexThresholdFourSourceVector_eq_p888
  inverse_residual :=
    alphaStrongSMBlockIndexThresholdFourSourceVector_outputs_residual


end
end StandardModelConstraint
end SaturationMonoid
