/-
  Proposition 290: structural origin of the P288 GUT-anchor inputs.

  P288 corrected the GUT inverse-coupling anchor to

      alpha_GUT^{-1} = (2^7 + 5) / 3.

  This file lowers the two non-obvious integer inputs one layer:

  * the denominator `3` is the cardinality of the three P177 primitive slogan
    sectors: source-backed continuity, navigation-only authority, and
    reflexive read/write memory;
  * the `+5` is the cardinality of the gauged fundamental blocks in the P286
    `3+2+1+1` carrier, namely the color `3` plus weak `2`; the two `1` blocks
    are singlets and are recorded separately.

  Boundary: this is a finite-cardinality / bookkeeping theorem.  It does not
  prove the physical beta functions, threshold corrections, or representation
  content.  Its purpose is to ensure the P288 anchor inputs are structural
  finite carriers rather than prose-only numerals.
-/

import H0mework.Realization.Relations.FintypeDerivation
import Mathlib.Tactic
import H0mework.Realization.Relations.P177
import H0mework.Physics.Lie.P286
import H0mework.Physics.SourceContracts.P289

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Primitive slogan-sector carrier -/

/-- The three primitive slogan sectors formalized by P177. -/
inductive PrimitiveSloganSector where
  | sourceBackedContinuity
  | navigationOnlyAuthority
  | reflexiveReadWriteMemory
  deriving DecidableEq, Repr, FintypeViaProxy

/-- THEOREM 1: the P177 primitive slogan-sector carrier has cardinality `3`. -/
theorem primitiveSloganSector_card_eq_three :
    Fintype.card PrimitiveSloganSector = 3 := by
  decide

/-- The sector count read as a scalar. -/
def primitiveSloganSectorCountFromCard
    (K : Type*) [Semiring K] : K :=
  (Fintype.card PrimitiveSloganSector : K)

/-- THEOREM 2: the cardinality sector count is exactly P288's denominator. -/
theorem primitiveSloganSectorCountFromCard_eq_standardModelSloganSectorCount
    (K : Type*) [Semiring K] :
    primitiveSloganSectorCountFromCard K =
      standardModelSloganSectorCount K := by
  norm_num [primitiveSloganSectorCountFromCard,
    primitiveSloganSector_card_eq_three, standardModelSloganSectorCount]

/-! ## P286 block-cardinality inputs -/

/-- The gauged fundamental blocks in the P286 carrier: color `3` plus weak `2`.
-/
abbrev GaugedFundamentalBlock :=
  Fin 3 ⊕ Fin 2

/-- The gauge-transparent singlet blocks in the P286 carrier: `1 + 1`. -/
abbrev GaugeSingletBlock :=
  Fin 1 ⊕ Fin 1

/-- THEOREM 3: the gauged fundamental carrier has cardinality `5`. -/
theorem gaugedFundamentalBlock_card_eq_five :
    Fintype.card GaugedFundamentalBlock = 5 := by
  change Fintype.card (Fin 3 ⊕ Fin 2) = 5
  simp

/-- THEOREM 4: the singlet carrier has cardinality `2`. -/
theorem gaugeSingletBlock_card_eq_two :
    Fintype.card GaugeSingletBlock = 2 := by
  change Fintype.card (Fin 1 ⊕ Fin 1) = 2
  simp

/-- THEOREM 5: the concrete P286 block-index carrier has cardinality `7`. -/
theorem smBlockIndex_card_eq_seven :
    Fintype.card GaugeProjection.ConcreteBlockDiagonal.SMBlockIndex = 7 := by
  change Fintype.card (Fin 3 ⊕ (Fin 2 ⊕ (Fin 1 ⊕ Fin 1))) = 7
  simp

/-- THEOREM 6: the concrete P286 block carrier splits as gauged `5` plus
singlet `2` at the cardinality level. -/
theorem smBlockIndex_card_eq_gauged_plus_singlet :
    Fintype.card GaugeProjection.ConcreteBlockDiagonal.SMBlockIndex =
      Fintype.card GaugedFundamentalBlock + Fintype.card GaugeSingletBlock := by
  rw [smBlockIndex_card_eq_seven, gaugedFundamentalBlock_card_eq_five,
    gaugeSingletBlock_card_eq_two]

/-- The P286 gauged fundamental block dimension read as a scalar. -/
def gaugedFundamentalDimensionFromBlockCard
    (K : Type*) [Semiring K] : K :=
  (Fintype.card GaugedFundamentalBlock : K)

/-- THEOREM 7: the P286 gauged block-cardinality is exactly P288's `+5`. -/
theorem gaugedFundamentalDimensionFromBlockCard_eq_gaugedFundamentalDimension
    (K : Type*) [Semiring K] :
    gaugedFundamentalDimensionFromBlockCard K =
      gaugedFundamentalDimension K := by
  norm_num [gaugedFundamentalDimensionFromBlockCard,
    gaugedFundamentalBlock_card_eq_five, gaugedFundamentalDimension]

/-! ## Reconstructing the P288 anchor from structural cards -/

/-- The corrected GUT inverse anchor reconstructed from structural finite
carriers: seven-facet information states, gauged P286 blocks, and P177 slogan
sectors. -/
def alphaGUTInverseFromStructuralCards
    (K : Type*) [Field K] : K :=
  (sevenFacetInformationStateCount K +
      gaugedFundamentalDimensionFromBlockCard K) /
    primitiveSloganSectorCountFromCard K

/-- THEOREM 8: the structural-cardinality anchor is exactly P288's corrected
sector-normalized anchor. -/
theorem alphaGUTInverseFromStructuralCards_eq_p288_anchor
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaGUTInverseFromStructuralCards K =
      alphaGUTInverseSectorNormalized K := by
  rw [alphaGUTInverseFromStructuralCards,
    gaugedFundamentalDimensionFromBlockCard,
    primitiveSloganSectorCountFromCard,
    alphaGUTInverseSectorNormalized, gaugedFundamentalDimension,
    standardModelSloganSectorCount, gaugedFundamentalBlock_card_eq_five,
    primitiveSloganSector_card_eq_three]
  norm_num [sevenFacetInformationStateCount]

/-- THEOREM 9: the structural-cardinality anchor evaluates to `133/3`. -/
theorem alphaGUTInverseFromStructuralCards_eq_133_div_3
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaGUTInverseFromStructuralCards K = ((133 : K) / (3 : K)) := by
  rw [alphaGUTInverseFromStructuralCards_eq_p288_anchor]
  exact alphaGUTInverseSectorNormalized_eq_133_div_3 K

end StandardModelConstraint
end SaturationMonoid
