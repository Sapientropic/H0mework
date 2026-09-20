import H0mework.Physics.AlphaSources.P607

/-!
# Proposition 608: no-choice surface for the two main producer objects

P606 removed packet-level freedom from the Yukawa/CKM primitive-card producer.
P607 removed producer-object freedom from the finite `alpha_s` residual
producer.  This file combines those two singleton surfaces into one object-level
surface for the current main producer nails.

The combined candidate carries exactly the two producer objects that are still
active in the current finite Standard-Model line:

* an `AlphaStrongResidualGapProducer`;
* a `YukawaCoefficientPrimitiveCardPacket`.

If both fields satisfy their named source surfaces, the whole pair is forced to
be canonical.  Thus the current finite line has no remaining object-level
choice on the two producer objects: all remaining debt is upstream of this
surface, namely the physical/dynamical derivation of the finite source laws.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Main producer object surface -/

/-- The two current producer objects in the finite Standard-Model line. -/
structure MainProducerObjectCandidate where
  alphaResidual : AlphaStrongResidualGapProducer
  yukawaPacket : YukawaCoefficientPrimitiveCardPacket

/-- The canonical two-object candidate: P581/P597 for `alpha_s`, and P604 for
Yukawa/CKM. -/
def canonicalMainProducerObjectCandidate :
    MainProducerObjectCandidate where
  alphaResidual := alphaStrongSU7BreakingResidualGapProducer
  yukawaPacket := canonicalYukawaCoefficientPrimitiveCardPacket

/-- Source surface for the combined main producer object. -/
def MainProducerObjectSourceSurface
    (M : MainProducerObjectCandidate) : Prop :=
  AlphaStrongResidualProducerFiniteSourceSurface M.alphaResidual ∧
    YukawaPrimitiveCardSourceEquations M.yukawaPacket

/-- THEOREM 1: the canonical combined producer object lies on the source
surface. -/
theorem canonicalMainProducerObjectCandidate_sourceSurface :
    MainProducerObjectSourceSurface
      canonicalMainProducerObjectCandidate := by
  constructor
  · exact alphaStrongSU7BreakingResidualGapProducer_sourceSurface
  · exact canonicalYukawaCoefficientPrimitiveCardPacket_sourceEquations

/-- THEOREM 2: the combined main producer-object source surface is a
singleton. -/
theorem eq_canonicalMainProducerObjectCandidate_of_sourceSurface
    (M : MainProducerObjectCandidate)
    (hM : MainProducerObjectSourceSurface M) :
    M = canonicalMainProducerObjectCandidate := by
  cases M with
  | mk alphaResidual yukawaPacket =>
    rcases hM with ⟨hAlpha, hYukawa⟩
    have hAlphaEq :
        alphaResidual = alphaStrongSU7BreakingResidualGapProducer :=
      eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface
        alphaResidual hAlpha
    have hYukawaEq :
        yukawaPacket = canonicalYukawaCoefficientPrimitiveCardPacket :=
      eq_canonicalYukawaCoefficientPrimitiveCardPacket_of_sourceEquations
        yukawaPacket hYukawa
    subst alphaResidual
    subst yukawaPacket
    rfl

/-- THEOREM 3: membership in the combined source surface is equivalent to
being the canonical combined producer object. -/
theorem mainProducerObjectSourceSurface_iff_eq_canonical
    (M : MainProducerObjectCandidate) :
    MainProducerObjectSourceSurface M ↔
      M = canonicalMainProducerObjectCandidate := by
  constructor
  · intro hM
    exact eq_canonicalMainProducerObjectCandidate_of_sourceSurface M hM
  · intro hM
    rw [hM]
    exact canonicalMainProducerObjectCandidate_sourceSurface

/-- THEOREM 4: any two combined source-surface producer objects are equal. -/
theorem mainProducerObjectSourceSurface_unique
    (M N : MainProducerObjectCandidate)
    (hM : MainProducerObjectSourceSurface M)
    (hN : MainProducerObjectSourceSurface N) :
    M = N := by
  rw [eq_canonicalMainProducerObjectCandidate_of_sourceSurface M hM,
    eq_canonicalMainProducerObjectCandidate_of_sourceSurface N hN]

/-! ## Reading the three main numerical outputs from the no-choice surface -/

/-- THEOREM 5: any combined source-surface object has the exact alpha gap
`89/10000`. -/
theorem mainProducerObjectSourceSurface_alphaGap
    (M : MainProducerObjectCandidate)
    (hM : MainProducerObjectSourceSurface M) :
    M.alphaResidual.producedGap = (89 : ℚ) / 10000 := by
  rw [eq_canonicalMainProducerObjectCandidate_of_sourceSurface M hM]
  exact alphaStrongSU7BreakingResidualGapProducer_gap

/-- THEOREM 6: any combined source-surface object has the exact inverse
residual `-89000/128511`. -/
theorem mainProducerObjectSourceSurface_inverseResidual
    (M : MainProducerObjectCandidate)
    (hM : MainProducerObjectSourceSurface M) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        M.alphaResidual.producedGap =
      -((89000 : ℚ) / 128511) := by
  rw [eq_canonicalMainProducerObjectCandidate_of_sourceSurface M hM]
  change
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongSU7BreakingResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  rw [alphaStrongSU7BreakingResidualGapProducer_inverseCorrection]
  exact alphaStrongResidualInverseCorrectionNeeded_eq ℚ

/-- THEOREM 7: any combined source-surface object generates the documented
nine-depth Yukawa table. -/
theorem mainProducerObjectSourceSurface_yukawaMassOrder
    (M : MainProducerObjectCandidate)
    (hM : MainProducerObjectSourceSurface M) :
    (yukawaProducerInputCandidateOfPrimitiveCardPacket
        M.yukawaPacket).depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  rcases hM with ⟨_, hYukawa⟩
  exact yukawaProducerInputCandidateOfPrimitiveCardPacket_massOrder_eq
    M.yukawaPacket hYukawa

/-- THEOREM 8: any combined source-surface object generates the CKM/Jarlskog
depth sum `386`. -/
theorem mainProducerObjectSourceSurface_ckmDepthSum
    (M : MainProducerObjectCandidate)
    (hM : MainProducerObjectSourceSurface M) :
    ckmDepthSum_fromYukawaDepthTable
        (yukawaProducerInputCandidateOfPrimitiveCardPacket
          M.yukawaPacket).depthTable =
      (ckmCPDepthSum : Int) := by
  rcases hM with ⟨_, hYukawa⟩
  exact yukawaProducerInputCandidateOfPrimitiveCardPacket_ckmDepthSum_eq_386
    M.yukawaPacket hYukawa

/-! ## Receipt -/

/-- Compact no-choice receipt for the combined main producer-object surface. -/
structure MainProducerObjectNoChoiceReceipt where
  canonical_source :
    MainProducerObjectSourceSurface
      canonicalMainProducerObjectCandidate
  iff_canonical :
    ∀ M : MainProducerObjectCandidate,
      MainProducerObjectSourceSurface M ↔
        M = canonicalMainProducerObjectCandidate
  unique :
    ∀ M N : MainProducerObjectCandidate,
      MainProducerObjectSourceSurface M ->
        MainProducerObjectSourceSurface N ->
          M = N
  alpha_gap :
    ∀ M : MainProducerObjectCandidate,
      MainProducerObjectSourceSurface M ->
        M.alphaResidual.producedGap = (89 : ℚ) / 10000
  inverse_residual :
    ∀ M : MainProducerObjectCandidate,
      MainProducerObjectSourceSurface M ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            M.alphaResidual.producedGap =
          -((89000 : ℚ) / 128511)
  yukawa_mass_order :
    ∀ M : MainProducerObjectCandidate,
      MainProducerObjectSourceSurface M ->
        (yukawaProducerInputCandidateOfPrimitiveCardPacket
            M.yukawaPacket).depthTable.massOrder =
          [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum :
    ∀ M : MainProducerObjectCandidate,
      MainProducerObjectSourceSurface M ->
        ckmDepthSum_fromYukawaDepthTable
            (yukawaProducerInputCandidateOfPrimitiveCardPacket
              M.yukawaPacket).depthTable =
          (ckmCPDepthSum : Int)

/-- THEOREM 9: combined no-choice receipt for the current main producer
objects. -/
theorem mainProducerObjectNoChoiceReceipt :
    MainProducerObjectNoChoiceReceipt where
  canonical_source :=
    canonicalMainProducerObjectCandidate_sourceSurface
  iff_canonical :=
    mainProducerObjectSourceSurface_iff_eq_canonical
  unique :=
    mainProducerObjectSourceSurface_unique
  alpha_gap :=
    mainProducerObjectSourceSurface_alphaGap
  inverse_residual :=
    mainProducerObjectSourceSurface_inverseResidual
  yukawa_mass_order :=
    mainProducerObjectSourceSurface_yukawaMassOrder
  ckm_depth_sum :=
    mainProducerObjectSourceSurface_ckmDepthSum

end StandardModelConstraint
end SaturationMonoid
