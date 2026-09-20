/-
  Proposition 507: full concrete off-block support as canonical support plus
  conjugate mirror.

  P506 proves that the six canonical endpoint pairs are realized by concrete
  off-diagonal matrix positions in the P286 block-index carrier, with total
  canonical support size 17.

  This file closes the orientation bookkeeping one layer lower.  The full
  ordered off-block support of the concrete `3+2+1+1` matrix carrier splits
  into:

      canonical support   : 17 positions,
      conjugate mirror    : 17 positions,
      full off-block total: 34 positions.

  Equivalently, an ordered concrete block pair is off-block iff it is either
  canonical or the reverse of a canonical pair, and these two cases are
  disjoint.  This is still finite matrix-support algebra, not a derivation of
  chirality, charge assignments, anomaly cancellation, or low-energy physics.
-/

import H0mework.Physics.RepresentationSources.P506

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

open RunningSigmaBeta
open GaugeProjection.ConcreteBlockDiagonal

/-! ## The conjugate mirror of the canonical support -/

/-- Concrete ordered matrix positions whose reverse orientation is canonical.
This is the conjugate mirror of `ConcreteCanonicalOffDiagonalIndexPair`. -/
abbrev ConcreteConjugateOffDiagonalIndexPair :=
  {p : SMBlockIndex × SMBlockIndex //
    IsCanonicalOffDiagonalPair
      (blockOfSMBlockIndex p.2)
      (blockOfSMBlockIndex p.1)}

instance concreteConjugateOffDiagonalIndexPairFintype :
    Fintype ConcreteConjugateOffDiagonalIndexPair := by
  exact
    Fintype.subtype
      (Finset.univ.filter
        (fun p : SMBlockIndex × SMBlockIndex =>
          IsCanonicalOffDiagonalPair
            (blockOfSMBlockIndex p.2)
            (blockOfSMBlockIndex p.1)))
      (by
        intro p
        simp)

/-- Swap sends canonical support to its conjugate mirror. -/
def concreteConjugationEquiv :
    ConcreteCanonicalOffDiagonalIndexPair ≃
      ConcreteConjugateOffDiagonalIndexPair where
  toFun p := ⟨(p.1.2, p.1.1), p.2⟩
  invFun p := ⟨(p.1.2, p.1.1), p.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    rfl
  right_inv := by
    intro p
    apply Subtype.ext
    rfl

/-- THEOREM 1: the conjugate mirror has the same support size, `17`. -/
theorem concreteConjugateOffDiagonalIndexPair_card :
    Fintype.card ConcreteConjugateOffDiagonalIndexPair = 17 := by
  have hcard :
      Fintype.card ConcreteCanonicalOffDiagonalIndexPair =
        Fintype.card ConcreteConjugateOffDiagonalIndexPair :=
    Fintype.card_congr concreteConjugationEquiv
  rw [← hcard]
  exact concreteCanonicalOffDiagonalIndexPair_card

/-! ## Full off-block support -/

/-- The full ordered off-block support of the concrete matrix carrier. -/
abbrev ConcreteOffBlockIndexPair :=
  {p : SMBlockIndex × SMBlockIndex //
    blockOfSMBlockIndex p.1 ≠ blockOfSMBlockIndex p.2}

instance concreteOffBlockIndexPairFintype :
    Fintype ConcreteOffBlockIndexPair := by
  exact
    Fintype.subtype
      (Finset.univ.filter
        (fun p : SMBlockIndex × SMBlockIndex =>
          blockOfSMBlockIndex p.1 ≠ blockOfSMBlockIndex p.2))
      (by
        intro p
        simp)

/-- THEOREM 2: off-block ordered pairs are exactly canonical pairs or their
conjugate mirrors. -/
theorem concrete_offBlock_iff_canonical_or_conjugate
    (p : SMBlockIndex × SMBlockIndex) :
    blockOfSMBlockIndex p.1 ≠ blockOfSMBlockIndex p.2 ↔
      IsCanonicalOffDiagonalPair
        (blockOfSMBlockIndex p.1)
        (blockOfSMBlockIndex p.2) ∨
      IsCanonicalOffDiagonalPair
        (blockOfSMBlockIndex p.2)
        (blockOfSMBlockIndex p.1) := by
  constructor
  · intro h
    cases h1 : blockOfSMBlockIndex p.1 <;>
      cases h2 : blockOfSMBlockIndex p.2 <;>
      simp [h1, h2, IsCanonicalOffDiagonalPair,
        SU7CarrierBlock.code] at h ⊢
  · intro h heq
    rcases h with hcanon | hconj
    · unfold IsCanonicalOffDiagonalPair at hcanon
      rw [heq] at hcanon
      exact Nat.lt_irrefl _ hcanon
    · unfold IsCanonicalOffDiagonalPair at hconj
      rw [heq] at hconj
      exact Nat.lt_irrefl _ hconj

/-- THEOREM 3: canonical orientation and conjugate orientation are disjoint. -/
theorem concrete_canonical_conjugate_not_both
    (p : SMBlockIndex × SMBlockIndex) :
    ¬ (IsCanonicalOffDiagonalPair
          (blockOfSMBlockIndex p.1)
          (blockOfSMBlockIndex p.2) ∧
        IsCanonicalOffDiagonalPair
          (blockOfSMBlockIndex p.2)
          (blockOfSMBlockIndex p.1)) := by
  intro h
  unfold IsCanonicalOffDiagonalPair at h
  exact Nat.lt_asymm h.1 h.2

/-- THEOREM 4: the full ordered off-block matrix support has size `34`. -/
theorem concreteOffBlockIndexPair_card :
    Fintype.card ConcreteOffBlockIndexPair = 34 := by
  decide

/-- THEOREM 5: full off-block support is exactly canonical support plus its
conjugate mirror at the cardinality level. -/
theorem concreteFullOffBlockSupport_card_decomposition :
    Fintype.card ConcreteOffBlockIndexPair =
      Fintype.card ConcreteCanonicalOffDiagonalIndexPair +
        Fintype.card ConcreteConjugateOffDiagonalIndexPair := by
  rw [concreteOffBlockIndexPair_card,
    concreteCanonicalOffDiagonalIndexPair_card,
    concreteConjugateOffDiagonalIndexPair_card]

/-- Bundled receipt for the full concrete off-block support decomposition. -/
structure ConcreteFullOffBlockSupportCertificate : Prop where
  canonical_support_card :
    Fintype.card ConcreteCanonicalOffDiagonalIndexPair = 17
  conjugate_support_card :
    Fintype.card ConcreteConjugateOffDiagonalIndexPair = 17
  full_off_block_support_card :
    Fintype.card ConcreteOffBlockIndexPair = 34
  full_support_decomposes :
    Fintype.card ConcreteOffBlockIndexPair =
      Fintype.card ConcreteCanonicalOffDiagonalIndexPair +
        Fintype.card ConcreteConjugateOffDiagonalIndexPair
  off_block_iff_canonical_or_conjugate :
    ∀ p : SMBlockIndex × SMBlockIndex,
      blockOfSMBlockIndex p.1 ≠ blockOfSMBlockIndex p.2 ↔
        IsCanonicalOffDiagonalPair
          (blockOfSMBlockIndex p.1)
          (blockOfSMBlockIndex p.2) ∨
        IsCanonicalOffDiagonalPair
          (blockOfSMBlockIndex p.2)
          (blockOfSMBlockIndex p.1)
  canonical_conjugate_disjoint :
    ∀ p : SMBlockIndex × SMBlockIndex,
      ¬ (IsCanonicalOffDiagonalPair
            (blockOfSMBlockIndex p.1)
            (blockOfSMBlockIndex p.2) ∧
          IsCanonicalOffDiagonalPair
            (blockOfSMBlockIndex p.2)
            (blockOfSMBlockIndex p.1))
  conjugation_equiv :
    Nonempty
      (ConcreteCanonicalOffDiagonalIndexPair ≃
        ConcreteConjugateOffDiagonalIndexPair)
  endpoint_certificate :
    ConcreteBlockSupportEndpointCertificate

/-- THEOREM 6: the complete concrete off-block support is the canonical
information/matter support plus its conjugate mirror. -/
theorem concreteFullOffBlockSupportCertificate :
    ConcreteFullOffBlockSupportCertificate where
  canonical_support_card := concreteCanonicalOffDiagonalIndexPair_card
  conjugate_support_card := concreteConjugateOffDiagonalIndexPair_card
  full_off_block_support_card := concreteOffBlockIndexPair_card
  full_support_decomposes := concreteFullOffBlockSupport_card_decomposition
  off_block_iff_canonical_or_conjugate :=
    concrete_offBlock_iff_canonical_or_conjugate
  canonical_conjugate_disjoint := concrete_canonical_conjugate_not_both
  conjugation_equiv := ⟨concreteConjugationEquiv⟩
  endpoint_certificate := concreteBlockSupportEndpointCertificate

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
