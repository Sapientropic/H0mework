/-
  Proposition 506: concrete block support behind the information/matter
  endpoint carrier.

  P505 proves that any carrier presented by the six canonical `3+2+1+1`
  endpoint pairs is uniquely equivalent to the SU(7) block-incidence carrier.
  This file lowers that presentation one layer: the endpoint carrier is the
  image of the concrete P286 matrix block-index support

      Fin 3 ⊕ (Fin 2 ⊕ (Fin 1 ⊕ Fin 1)).

  The six endpoints are not merely names.  They are the six block projections
  of concrete off-diagonal matrix positions, with fiber multiplicities

      3*2, 3*1, 3*1, 2*1, 2*1, 1*1 = 6,3,3,2,2,1,

  for a total canonical off-diagonal support size of 17.

  Boundary: this is still a finite block-support theorem.  It does not prove
  Higgs breaking, anomaly cancellation, Yukawa values, RG thresholds, or
  low-energy physics.  It does show that the endpoint presentation used by
  P505 is produced by the concrete `diag(C,W,z,z⁻¹)` block carrier.
-/

import H0mework.Physics.RepresentationSources.P505
import H0mework.Physics.Lie.P286

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

open RunningSigmaBeta
open GaugeProjection.ConcreteBlockDiagonal

instance decidableIsCanonicalOffDiagonalPair
    (a b : SU7CarrierBlock) :
    Decidable (IsCanonicalOffDiagonalPair a b) := by
  unfold IsCanonicalOffDiagonalPair
  infer_instance

instance canonicalEndpointFintype : Fintype CanonicalEndpoint := by
  exact
    Fintype.subtype
      (Finset.univ.filter
        (fun p : SU7CarrierBlock × SU7CarrierBlock =>
          IsCanonicalOffDiagonalPair p.1 p.2))
      (by
        intro p
        simp)

instance canonicalEndpointDecidableEq : DecidableEq CanonicalEndpoint := by
  classical
  exact inferInstance

/-! ## Concrete block indices projected to SU(7) carrier blocks -/

/-- The concrete block index of P286 remembers which of the four
`3+2+1+1` carrier blocks an index lies in. -/
def blockOfSMBlockIndex : SMBlockIndex -> SU7CarrierBlock
  | Sum.inl _ => .color
  | Sum.inr (Sum.inl _) => .weak
  | Sum.inr (Sum.inr (Sum.inl _)) => .positiveSinglet
  | Sum.inr (Sum.inr (Sum.inr _)) => .negativeSinglet

/-- The concrete cardinality of each carrier block. -/
def carrierBlockCard : SU7CarrierBlock -> ℕ
  | .color => 3
  | .weak => 2
  | .positiveSinglet => 1
  | .negativeSinglet => 1

/-- THEOREM 1: `carrierBlockCard` is the actual fiber cardinality of the
concrete block-index projection. -/
theorem carrierBlockCard_eq_indexFiber_card
    (b : SU7CarrierBlock) :
    Fintype.card {x : SMBlockIndex // blockOfSMBlockIndex x = b} =
      carrierBlockCard b := by
  cases b <;> decide

/-- A canonical representative index in each block, used only to prove
surjectivity of the endpoint projection. -/
def representativeSMBlockIndex : SU7CarrierBlock -> SMBlockIndex
  | .color => Sum.inl (0 : Fin 3)
  | .weak => Sum.inr (Sum.inl (0 : Fin 2))
  | .positiveSinglet => Sum.inr (Sum.inr (Sum.inl (0 : Fin 1)))
  | .negativeSinglet => Sum.inr (Sum.inr (Sum.inr (0 : Fin 1)))

@[simp]
theorem blockOf_representativeSMBlockIndex
    (b : SU7CarrierBlock) :
    blockOfSMBlockIndex (representativeSMBlockIndex b) = b := by
  cases b <;> rfl

/-! ## Concrete off-diagonal support and endpoint projection -/

/-- Concrete ordered matrix positions whose source/target blocks form a
canonical off-diagonal endpoint pair.  This is the finite support under the
upper-triangular block projection; the opposite orientation is its conjugate
mirror. -/
abbrev ConcreteCanonicalOffDiagonalIndexPair :=
  {p : SMBlockIndex × SMBlockIndex //
    IsCanonicalOffDiagonalPair
      (blockOfSMBlockIndex p.1)
      (blockOfSMBlockIndex p.2)}

instance concreteCanonicalOffDiagonalIndexPairFintype :
    Fintype ConcreteCanonicalOffDiagonalIndexPair := by
  exact
    Fintype.subtype
      (Finset.univ.filter
        (fun p : SMBlockIndex × SMBlockIndex =>
          IsCanonicalOffDiagonalPair
            (blockOfSMBlockIndex p.1)
            (blockOfSMBlockIndex p.2)))
      (by
        intro p
        simp)

/-- Project a concrete off-diagonal matrix position to its canonical endpoint
pair. -/
def concreteEndpointOfIndexPair
    (p : ConcreteCanonicalOffDiagonalIndexPair) : CanonicalEndpoint :=
  ⟨(blockOfSMBlockIndex p.1.1, blockOfSMBlockIndex p.1.2), p.2⟩

/-- THEOREM 2: every canonical endpoint is realized by at least one concrete
matrix off-diagonal position. -/
theorem concreteEndpointOfIndexPair_surjective :
    Function.Surjective concreteEndpointOfIndexPair := by
  intro e
  refine
    ⟨⟨(representativeSMBlockIndex e.1.1,
        representativeSMBlockIndex e.1.2), ?_⟩, ?_⟩
  · simpa using e.2
  · apply Subtype.ext
    simp [concreteEndpointOfIndexPair]

/-- The concrete fiber over a canonical endpoint. -/
abbrev ConcreteEndpointFiber (e : CanonicalEndpoint) :=
  {p : SMBlockIndex × SMBlockIndex //
    blockOfSMBlockIndex p.1 = e.1.1 ∧
      blockOfSMBlockIndex p.2 = e.1.2}

/-- The concrete multiplicity of an endpoint is the number of matrix positions
projecting to it. -/
def concreteEndpointMultiplicity (e : CanonicalEndpoint) : ℕ :=
  Fintype.card (ConcreteEndpointFiber e)

/-- THEOREM 3: the six matter/Higgs endpoint multiplicities are the products
of the concrete block sizes. -/
theorem concreteEndpointMultiplicity_eq_blockCard_product
    (i : SU7BlockIncidence) :
    concreteEndpointMultiplicity (incidenceEndpoint i) =
      carrierBlockCard (SU7BlockIncidence.endpoints i).1 *
        carrierBlockCard (SU7BlockIncidence.endpoints i).2 := by
  cases i <;> decide

/-- THEOREM 4: the endpoint multiplicities are `6,3,3,2,2,1` in the P459
incidence order. -/
theorem concreteEndpointMultiplicity_table :
    concreteEndpointMultiplicity (incidenceEndpoint .colorWeak) = 6 ∧
    concreteEndpointMultiplicity (incidenceEndpoint .colorPositiveSinglet) = 3 ∧
    concreteEndpointMultiplicity (incidenceEndpoint .colorNegativeSinglet) = 3 ∧
    concreteEndpointMultiplicity (incidenceEndpoint .weakPositiveSinglet) = 2 ∧
    concreteEndpointMultiplicity (incidenceEndpoint .weakNegativeSinglet) = 2 ∧
    concreteEndpointMultiplicity (incidenceEndpoint .positiveNegativeSinglet) = 1 := by
  decide

/-- THEOREM 5: the concrete canonical off-diagonal matrix support has total
size `17`. -/
theorem concreteCanonicalOffDiagonalIndexPair_card :
    Fintype.card ConcreteCanonicalOffDiagonalIndexPair = 17 := by
  decide

/-- THEOREM 6: summing the six incidence-ordered endpoint fibers also gives
total support size `17`.  This avoids depending on a particular `Finset.univ`
enumeration of the endpoint subtype. -/
theorem concreteEndpointMultiplicity_incidence_sum :
    concreteEndpointMultiplicity (incidenceEndpoint .colorWeak) +
    concreteEndpointMultiplicity (incidenceEndpoint .colorPositiveSinglet) +
    concreteEndpointMultiplicity (incidenceEndpoint .colorNegativeSinglet) +
    concreteEndpointMultiplicity (incidenceEndpoint .weakPositiveSinglet) +
    concreteEndpointMultiplicity (incidenceEndpoint .weakNegativeSinglet) +
    concreteEndpointMultiplicity (incidenceEndpoint .positiveNegativeSinglet) = 17 := by
  decide

/-- A bundled receipt that the P505 endpoint carrier is the finite block
projection of the concrete P286 matrix support. -/
structure ConcreteBlockSupportEndpointCertificate : Prop where
  endpoint_projection_surjective :
    Function.Surjective concreteEndpointOfIndexPair
  endpoint_multiplicity_product :
    ∀ i : SU7BlockIncidence,
      concreteEndpointMultiplicity (incidenceEndpoint i) =
        carrierBlockCard (SU7BlockIncidence.endpoints i).1 *
          carrierBlockCard (SU7BlockIncidence.endpoints i).2
  endpoint_multiplicity_table :
    concreteEndpointMultiplicity (incidenceEndpoint .colorWeak) = 6 ∧
    concreteEndpointMultiplicity (incidenceEndpoint .colorPositiveSinglet) = 3 ∧
    concreteEndpointMultiplicity (incidenceEndpoint .colorNegativeSinglet) = 3 ∧
    concreteEndpointMultiplicity (incidenceEndpoint .weakPositiveSinglet) = 2 ∧
    concreteEndpointMultiplicity (incidenceEndpoint .weakNegativeSinglet) = 2 ∧
    concreteEndpointMultiplicity (incidenceEndpoint .positiveNegativeSinglet) = 1
  total_concrete_support :
    Fintype.card ConcreteCanonicalOffDiagonalIndexPair = 17
  total_by_incidence_endpoint_fibers :
    concreteEndpointMultiplicity (incidenceEndpoint .colorWeak) +
    concreteEndpointMultiplicity (incidenceEndpoint .colorPositiveSinglet) +
    concreteEndpointMultiplicity (incidenceEndpoint .colorNegativeSinglet) +
    concreteEndpointMultiplicity (incidenceEndpoint .weakPositiveSinglet) +
    concreteEndpointMultiplicity (incidenceEndpoint .weakNegativeSinglet) +
    concreteEndpointMultiplicity (incidenceEndpoint .positiveNegativeSinglet) = 17
  matter_endpoint_equiv_eq_P503 :
    matterEndpointPresentation.incidenceEquiv = informationMatterEquiv

/-- THEOREM 7: the concrete block support supplies the endpoint presentation
used by the information/matter equivalence. -/
theorem concreteBlockSupportEndpointCertificate :
    ConcreteBlockSupportEndpointCertificate where
  endpoint_projection_surjective := concreteEndpointOfIndexPair_surjective
  endpoint_multiplicity_product :=
    concreteEndpointMultiplicity_eq_blockCard_product
  endpoint_multiplicity_table := concreteEndpointMultiplicity_table
  total_concrete_support := concreteCanonicalOffDiagonalIndexPair_card
  total_by_incidence_endpoint_fibers :=
    concreteEndpointMultiplicity_incidence_sum
  matter_endpoint_equiv_eq_P503 :=
    matterEndpointPresentation_incidenceEquiv_eq_informationMatterEquiv

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
