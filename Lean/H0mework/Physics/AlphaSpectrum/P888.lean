import H0mework.Physics.Lie.P286
import H0mework.Physics.AlphaSpectrum.P887

/-!
# Proposition 888: matrix-block-index producer for alpha_s breaking sizes

P887 derives the alpha-strong breaking partition sizes from the P461 block
dimension function.  This file lowers the same sizes to the actual P286
matrix-level block-index carrier

`Fin 3 ⊕ (Fin 2 ⊕ (Fin 1 ⊕ Fin 1))`.

Thus the breaking source chain now starts at the concrete block carrier used
by the `diag(C,W,z,z⁻¹)` SU(7) embedding, then produces:

* `|SMBlockIndex| = 7`;
* binary information fields over it, `2^7 = 128`;
* color-adjoint plus photon, `(3^2 - 1) + 1 = 9`;
* unified SU(7) adjoint, `7^2 - 1 = 48`;
* partition complement `(128 + 9) - 48 = 89`;
* the exact alpha-strong inverse residual `-89000/128511`.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open scoped BigOperators

set_option linter.defProp false

/-! ## Concrete block-index carrier -/

/-- The concrete P286 matrix block index carrier. -/
abbrev SU7BreakingSMBlockIndexMode :=
  GaugeProjection.ConcreteBlockDiagonal.SMBlockIndex

/-- THEOREM 1: the concrete block-index carrier has cardinality
`3 + 2 + 1 + 1 = 7`. -/
theorem su7BreakingSMBlockIndexMode_card_eq_seven :
    Fintype.card SU7BreakingSMBlockIndexMode = 7 := by
  change Fintype.card (Fin 3 ⊕ (Fin 2 ⊕ (Fin 1 ⊕ Fin 1))) = 7
  simp

/-- THEOREM 2: the P887 block-dimension scalar is exactly the cardinality of
the concrete P286 block-index carrier. -/
theorem su7BreakingFundamentalBlockDimension_eq_SMBlockIndex_card :
    su7BreakingFundamentalBlockDimension =
      Fintype.card SU7BreakingSMBlockIndexMode := by
  rw [su7BreakingFundamentalBlockDimension_eq_seven,
    su7BreakingSMBlockIndexMode_card_eq_seven]

/-- Binary information fields over the concrete block-index carrier. -/
abbrev SU7BreakingInformationStateFromSMBlockIndex :=
  SU7BreakingSMBlockIndexMode -> Bool

/-- THEOREM 3: binary information fields over the concrete block-index carrier
have cardinality `2^7 = 128`. -/
theorem su7BreakingInformationStateFromSMBlockIndex_card_eq_128 :
    Fintype.card SU7BreakingInformationStateFromSMBlockIndex = 128 := by
  unfold SU7BreakingInformationStateFromSMBlockIndex
  rw [Fintype.card_fun, su7BreakingSMBlockIndexMode_card_eq_seven]
  norm_num

/-- The concrete color block of the matrix block carrier. -/
abbrev SU7BreakingColorBlockIndexMode := Fin 3

/-- Color-adjoint dimension generated from the concrete color block. -/
def su7BreakingColorAdjointDimensionFromSMBlockIndex : ℕ :=
  Fintype.card SU7BreakingColorBlockIndexMode ^ (2 : Nat) - 1

/-- THEOREM 4: the concrete color block produces `3^2 - 1 = 8`. -/
theorem su7BreakingColorAdjointDimensionFromSMBlockIndex_eq_eight :
    su7BreakingColorAdjointDimensionFromSMBlockIndex = 8 := by
  unfold su7BreakingColorAdjointDimensionFromSMBlockIndex
  norm_num

/-- Low-energy visible gauge modes generated from the concrete block index:
color adjoint plus photon. -/
abbrev SU7BreakingLowEnergyVisibleGaugeFromSMBlockIndex :=
  Fin su7BreakingColorAdjointDimensionFromSMBlockIndex ⊕ Fin 1

/-- THEOREM 5: the concrete block-index low-energy visible carrier has
cardinality `9`. -/
theorem su7BreakingLowEnergyVisibleGaugeFromSMBlockIndex_card_eq_nine :
    Fintype.card SU7BreakingLowEnergyVisibleGaugeFromSMBlockIndex = 9 := by
  change
    Fintype.card
      (Fin su7BreakingColorAdjointDimensionFromSMBlockIndex ⊕ Fin 1) = 9
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    su7BreakingColorAdjointDimensionFromSMBlockIndex_eq_eight]

/-- Unified adjoint dimension generated from the concrete block-index carrier.
-/
def su7BreakingUnifiedAdjointDimensionFromSMBlockIndex : ℕ :=
  Fintype.card SU7BreakingSMBlockIndexMode ^ (2 : Nat) - 1

/-- THEOREM 6: the concrete block-index carrier generates `7^2 - 1 = 48`. -/
theorem su7BreakingUnifiedAdjointDimensionFromSMBlockIndex_eq_48 :
    su7BreakingUnifiedAdjointDimensionFromSMBlockIndex = 48 := by
  unfold su7BreakingUnifiedAdjointDimensionFromSMBlockIndex
  rw [su7BreakingSMBlockIndexMode_card_eq_seven]
  norm_num

/-- Unified SU(7) adjoint gauge modes generated from the concrete block-index
carrier. -/
abbrev SU7BreakingAdjointGaugeFromSMBlockIndex :=
  Fin su7BreakingUnifiedAdjointDimensionFromSMBlockIndex

/-- THEOREM 7: the concrete block-index unified adjoint carrier has
cardinality `48`. -/
theorem su7BreakingAdjointGaugeFromSMBlockIndex_card_eq_48 :
    Fintype.card SU7BreakingAdjointGaugeFromSMBlockIndex = 48 := by
  unfold SU7BreakingAdjointGaugeFromSMBlockIndex
  rw [Fintype.card_fin,
    su7BreakingUnifiedAdjointDimensionFromSMBlockIndex_eq_48]

/-! ## Matrix-block-index partition traces -/

/-- Positive breaking partition generated from the concrete block-index
carrier. -/
abbrev SU7BreakingPositivePartitionModeFromSMBlockIndex :=
  Sum SU7BreakingInformationStateFromSMBlockIndex
    SU7BreakingLowEnergyVisibleGaugeFromSMBlockIndex

/-- Negative breaking partition generated from the concrete block-index
carrier. -/
abbrev SU7BreakingNegativePartitionModeFromSMBlockIndex :=
  SU7BreakingAdjointGaugeFromSMBlockIndex

/-- Positive trace generated from the concrete block-index carrier. -/
def su7BreakingPositivePartitionTraceFromSMBlockIndex : ℚ :=
  finiteUnitSpectrumTrace SU7BreakingPositivePartitionModeFromSMBlockIndex

/-- Negative trace generated from the concrete block-index carrier. -/
def su7BreakingNegativePartitionTraceFromSMBlockIndex : ℚ :=
  finiteUnitSpectrumTrace SU7BreakingNegativePartitionModeFromSMBlockIndex

/-- Complement trace generated from the concrete block-index carrier. -/
def su7BreakingPartitionComplementTraceFromSMBlockIndex : ℚ :=
  su7BreakingPositivePartitionTraceFromSMBlockIndex -
    su7BreakingNegativePartitionTraceFromSMBlockIndex

/-- THEOREM 8: the concrete block-index positive trace is `137`. -/
theorem su7BreakingPositivePartitionTraceFromSMBlockIndex_eq_137 :
    su7BreakingPositivePartitionTraceFromSMBlockIndex = 137 := by
  unfold su7BreakingPositivePartitionTraceFromSMBlockIndex
  rw [finiteUnitSpectrumTrace_eq_card]
  have hcard :
      Fintype.card SU7BreakingPositivePartitionModeFromSMBlockIndex =
        Fintype.card SU7BreakingInformationStateFromSMBlockIndex +
          Fintype.card SU7BreakingLowEnergyVisibleGaugeFromSMBlockIndex := by
    unfold SU7BreakingPositivePartitionModeFromSMBlockIndex
    rw [Fintype.card_sum]
  rw [hcard, su7BreakingInformationStateFromSMBlockIndex_card_eq_128,
    su7BreakingLowEnergyVisibleGaugeFromSMBlockIndex_card_eq_nine]
  norm_num

/-- THEOREM 9: the concrete block-index negative trace is `48`. -/
theorem su7BreakingNegativePartitionTraceFromSMBlockIndex_eq_48 :
    su7BreakingNegativePartitionTraceFromSMBlockIndex = 48 := by
  unfold su7BreakingNegativePartitionTraceFromSMBlockIndex
  rw [finiteUnitSpectrumTrace_eq_card,
    su7BreakingAdjointGaugeFromSMBlockIndex_card_eq_48]
  norm_num

/-- THEOREM 10: the concrete block-index complement trace is `89`. -/
theorem su7BreakingPartitionComplementTraceFromSMBlockIndex_eq_89 :
    su7BreakingPartitionComplementTraceFromSMBlockIndex = 89 := by
  unfold su7BreakingPartitionComplementTraceFromSMBlockIndex
  rw [su7BreakingPositivePartitionTraceFromSMBlockIndex_eq_137,
    su7BreakingNegativePartitionTraceFromSMBlockIndex_eq_48]
  norm_num

/-- THEOREM 11: the concrete block-index complement trace is the P887
block-derived trace. -/
theorem su7BreakingPartitionComplementTraceFromSMBlockIndex_eq_p887 :
    su7BreakingPartitionComplementTraceFromSMBlockIndex =
      su7BreakingPartitionComplementTraceFromBlocks := by
  rw [su7BreakingPartitionComplementTraceFromSMBlockIndex_eq_89,
    su7BreakingPartitionComplementTraceFromBlocks_eq_89]

/-! ## Matrix-block-index alpha_s vector -/

/-- Four-source vector whose breaking source is read from the concrete
matrix-block-index partition trace. -/
def alphaStrongSMBlockIndexPartitionFourSourceVector :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking =>
      su7BreakingPartitionComplementTraceFromSMBlockIndex /
        alphaStrongGeneratedResolutionDenominator
  | .threshold => thresholdPairedSpectrumContribution
  | .threeLoopRG => alphaStrongPairedSpectrumCountertermFreeRGCoordinate
  | .higgsExtraRepresentation => higgsExtraPairedSpectrumContribution

/-- THEOREM 12: the concrete block-index breaking coordinate is `89/10000`. -/
theorem alphaStrongSMBlockIndexPartitionFourSourceVector_su7Breaking :
    alphaStrongSMBlockIndexPartitionFourSourceVector .su7Breaking =
      89 / 10000 := by
  unfold alphaStrongSMBlockIndexPartitionFourSourceVector
  rw [su7BreakingPartitionComplementTraceFromSMBlockIndex_eq_89,
    alphaStrongGeneratedResolutionDenominator_eq_10000]

/-- THEOREM 13: the concrete block-index vector is P887's block-derived
vector. -/
theorem alphaStrongSMBlockIndexPartitionFourSourceVector_eq_p887 :
    alphaStrongSMBlockIndexPartitionFourSourceVector =
      alphaStrongBlockDerivedPartitionFourSourceVector := by
  funext source
  cases source
  · calc
      alphaStrongSMBlockIndexPartitionFourSourceVector .su7Breaking =
          89 / 10000 :=
          alphaStrongSMBlockIndexPartitionFourSourceVector_su7Breaking
      _ = alphaStrongBlockDerivedPartitionFourSourceVector
            .su7Breaking := by
          rw [alphaStrongBlockDerivedPartitionFourSourceVector_su7Breaking]
  · rfl
  · rfl
  · rfl

/-- THEOREM 14: the concrete block-index vector transports to the exact
inverse alpha_s residual. -/
theorem alphaStrongSMBlockIndexPartitionFourSourceVector_outputs_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongSMBlockIndexPartitionFourSourceVector s) =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongSMBlockIndexPartitionFourSourceVector_eq_p887]
  exact alphaStrongBlockDerivedPartitionFourSourceVector_outputs_residual

/-! ## Certificate -/

/-- P888 certificate: the alpha-strong breaking source is generated from the
actual matrix-level SU(7) block index carrier used by the concrete block
embedding. -/
structure AlphaStrongSMBlockIndexPartitionProducerCertificate : Prop where
  block_index_card :
    Fintype.card SU7BreakingSMBlockIndexMode = 7
  block_dimension_card :
    su7BreakingFundamentalBlockDimension =
      Fintype.card SU7BreakingSMBlockIndexMode
  information_modes :
    Fintype.card SU7BreakingInformationStateFromSMBlockIndex = 128
  color_adjoint :
    su7BreakingColorAdjointDimensionFromSMBlockIndex = 8
  low_energy_visible :
    Fintype.card SU7BreakingLowEnergyVisibleGaugeFromSMBlockIndex = 9
  unified_adjoint :
    Fintype.card SU7BreakingAdjointGaugeFromSMBlockIndex = 48
  positive_partition :
    su7BreakingPositivePartitionTraceFromSMBlockIndex = 137
  negative_partition :
    su7BreakingNegativePartitionTraceFromSMBlockIndex = 48
  complement_partition :
    su7BreakingPartitionComplementTraceFromSMBlockIndex = 89
  complement_p887 :
    su7BreakingPartitionComplementTraceFromSMBlockIndex =
      su7BreakingPartitionComplementTraceFromBlocks
  source_coordinate :
    alphaStrongSMBlockIndexPartitionFourSourceVector .su7Breaking =
      89 / 10000
  vector_p887 :
    alphaStrongSMBlockIndexPartitionFourSourceVector =
      alphaStrongBlockDerivedPartitionFourSourceVector
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongSMBlockIndexPartitionFourSourceVector s) =
      -((89000 : ℚ) / 128511)

/-- THEOREM 15: canonical concrete block-index partition producer certificate.
-/
def alphaStrongSMBlockIndexPartitionProducerCertificate :
    AlphaStrongSMBlockIndexPartitionProducerCertificate where
  block_index_card := su7BreakingSMBlockIndexMode_card_eq_seven
  block_dimension_card :=
    su7BreakingFundamentalBlockDimension_eq_SMBlockIndex_card
  information_modes := su7BreakingInformationStateFromSMBlockIndex_card_eq_128
  color_adjoint := su7BreakingColorAdjointDimensionFromSMBlockIndex_eq_eight
  low_energy_visible :=
    su7BreakingLowEnergyVisibleGaugeFromSMBlockIndex_card_eq_nine
  unified_adjoint := su7BreakingAdjointGaugeFromSMBlockIndex_card_eq_48
  positive_partition := su7BreakingPositivePartitionTraceFromSMBlockIndex_eq_137
  negative_partition := su7BreakingNegativePartitionTraceFromSMBlockIndex_eq_48
  complement_partition :=
    su7BreakingPartitionComplementTraceFromSMBlockIndex_eq_89
  complement_p887 := su7BreakingPartitionComplementTraceFromSMBlockIndex_eq_p887
  source_coordinate := alphaStrongSMBlockIndexPartitionFourSourceVector_su7Breaking
  vector_p887 := alphaStrongSMBlockIndexPartitionFourSourceVector_eq_p887
  inverse_residual :=
    alphaStrongSMBlockIndexPartitionFourSourceVector_outputs_residual


end
end StandardModelConstraint
end SaturationMonoid
