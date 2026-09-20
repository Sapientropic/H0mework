import Mathlib.Tactic
import H0mework.Physics.AlphaSources.P660

/-!
# Proposition 661: full beta-vector shared-axis three-nail producer

P660 proves that the `alpha_s` residual uses the color projection of the full
Standard-Model incidence beta vector

`(SU(3), SU(2), U(1)) = (7, 19/6, -41/6)`.

P659 proves that the alpha, Yukawa-depth, and CKM/Jarlskog nails all share the
same trace-weighted QCD/Poincare axis.  This file composes the two facts:
the *full beta-vector color projection plus the 4D Poincare slot count* is the
shared axis for all three current producer nails, not only the alpha leg.

Boundary: this still does not derive the universal one-loop QFT weights,
threshold corrections, full CKM matrix, Higgs spectrum, or smooth SU(7)
breaking / consolidation dynamics.  It removes one presentation debt: the
current three-nail spine is now sourced by a full beta-vector carrier before
projecting to the color leg.

The final section adds an input-level product surface: the alpha leg carries
the actual SU7 block-incidence `GaugeTraceOneLoopInput` triple from P660 before
`betaCoeff` projection, then pairs it with the full-beta-vector Yukawa-depth
surface.  This closes the present finite three-nail surface at the trace-input
level on the alpha side, while keeping the remaining smooth dynamics debts
explicit.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open InformationMatterProjection

/-! ## The canonical one-axis producer is the full-vector color projection -/

/-- THEOREM 1: the canonical one-axis producer is the color projection of the
full SM incidence beta vector plus the 4D Poincare slot count. -/
theorem canonicalOneAxisPrimitiveSourceProducer_axis_eq_fullBetaVectorColor :
    canonicalOneAxisPrimitiveSourceProducer.axis =
      standardModelIncidenceBetaVector.color +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
          ℚ) := by
  rw [canonicalOneAxisPrimitiveSourceProducer_axis_eq_traceWeighted,
    traceWeightedAxis_eq_fullBetaVectorColorAxis]

/-- THEOREM 2: the full-vector color/Poincare axis has value `10`. -/
theorem canonicalOneAxisPrimitiveSourceProducer_fullBetaVectorAxis_eq_ten :
    standardModelIncidenceBetaVector.color +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
        ℚ) =
        (10 : ℚ) := by
  exact fullBetaVectorColorPoincareAxis_eq_ten

/-- THEOREM 3: therefore the canonical one-axis producer itself still has
axis `10`, but now through the full beta-vector presentation. -/
theorem canonicalOneAxisPrimitiveSourceProducer_axis_eq_ten_via_fullBetaVector :
    canonicalOneAxisPrimitiveSourceProducer.axis = (10 : ℚ) := by
  rw [canonicalOneAxisPrimitiveSourceProducer_axis_eq_fullBetaVectorColor,
    canonicalOneAxisPrimitiveSourceProducer_fullBetaVectorAxis_eq_ten]

/-! ## Three nails carried by the full-vector shared axis -/

/-- THEOREM 4: the canonical Yukawa packet satisfies the one-axis source law
whose axis is the full-vector color/Poincare axis. -/
theorem fullBetaVectorSharedAxis_canonicalYukawaSourceLaw :
    OneAxisYukawaPrimitiveCardSourceLaw
      canonicalOneAxisPrimitiveSourceProducer
      canonicalYukawaCoefficientPrimitiveCardPacket := by
  exact traceWeightedSharedAxis_canonicalYukawaSourceLaw

/-- THEOREM 5: the same full-vector shared axis implies the primitive-card
Yukawa source equations. -/
theorem fullBetaVectorSharedAxis_canonicalYukawaSourceEquations :
    YukawaPrimitiveCardSourceEquations
      canonicalYukawaCoefficientPrimitiveCardPacket := by
  exact traceWeightedSharedAxis_canonicalYukawaSourceEquations

/-- THEOREM 6: the alpha inverse residual is carried by the full-vector
shared axis. -/
theorem fullBetaVectorSharedAxis_alphaInverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareClosedGap =
      -((89000 : ℚ) / 128511) := by
  exact fullBetaVectorColor_alphaInverseResidual

/-- THEOREM 7: the full-vector shared axis forces the documented Yukawa
mass-order depth list. -/
theorem fullBetaVectorSharedAxis_yukawaMassOrder :
    [ (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .top).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .bottom).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .tau).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .charm).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .muon).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .strange).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .down).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .up).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .electron).toNat
    ] =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  exact traceWeightedSharedAxis_yukawaMassOrder

/-- THEOREM 8: the full-vector shared axis forces the four typed
CKM/Jarlskog depth contributions. -/
theorem fullBetaVectorSharedAxis_ckmFactors :
    CKMJarlskogFactor.depthContribution
        (yukawaPrimitiveCardClosedDepthTableCandidate
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence) .V_us =
        (-226 : Int) ∧
      CKMJarlskogFactor.depthContribution
          (yukawaPrimitiveCardClosedDepthTableCandidate
            canonicalYukawaCoefficientPrimitiveCardPacket
            yukawaSectorInformationIncidence) .V_cb =
          (-143 : Int) ∧
        CKMJarlskogFactor.depthContribution
            (yukawaPrimitiveCardClosedDepthTableCandidate
              canonicalYukawaCoefficientPrimitiveCardPacket
              yukawaSectorInformationIncidence) .V_ub_conj =
            (562 : Int) ∧
          CKMJarlskogFactor.depthContribution
              (yukawaPrimitiveCardClosedDepthTableCandidate
                canonicalYukawaCoefficientPrimitiveCardPacket
                yukawaSectorInformationIncidence) .V_cs_conj =
              (193 : Int) := by
  exact traceWeightedSharedAxis_ckmFactors

/-- THEOREM 9: the full-vector shared axis forces CKM/Jarlskog depth sum
`386`. -/
theorem fullBetaVectorSharedAxis_ckmDepthSum :
    ckmJarlskogFourProductDepthSum
        (yukawaPrimitiveCardClosedDepthTableCandidate
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence) =
      (ckmCPDepthSum : Int) := by
  exact traceWeightedSharedAxis_ckmDepthSum

/-! ## Certificate -/

/-- Compact certificate: the current alpha/Yukawa/CKM producer spine is
sourced by the full SM incidence beta-vector carrier through its color
projection plus the 4D Poincare slots. -/
structure FullBetaVectorSharedAxisThreeNailProducerCertificate where
  full_beta_vector_alpha :
    FullBetaVectorAlphaResidualProducerCertificate
  trace_weighted_three_nail :
    TraceWeightedSharedAxisThreeNailProducerCertificate
  canonical_axis_is_full_vector_color :
    canonicalOneAxisPrimitiveSourceProducer.axis =
      standardModelIncidenceBetaVector.color +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
          ℚ)
  full_vector_axis_eq_ten :
    standardModelIncidenceBetaVector.color +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
        ℚ) =
        (10 : ℚ)
  canonical_axis_eq_ten :
    canonicalOneAxisPrimitiveSourceProducer.axis = (10 : ℚ)
  yukawa_source_law :
    OneAxisYukawaPrimitiveCardSourceLaw
      canonicalOneAxisPrimitiveSourceProducer
      canonicalYukawaCoefficientPrimitiveCardPacket
  yukawa_source_equations :
    YukawaPrimitiveCardSourceEquations
      canonicalYukawaCoefficientPrimitiveCardPacket
  alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareClosedGap =
      -((89000 : ℚ) / 128511)
  yukawa_mass_order :
    [ (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .top).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .bottom).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .tau).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .charm).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .muon).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .strange).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .down).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .up).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .electron).toNat
    ] =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_factors :
    CKMJarlskogFactor.depthContribution
        (yukawaPrimitiveCardClosedDepthTableCandidate
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence) .V_us =
        (-226 : Int) ∧
      CKMJarlskogFactor.depthContribution
          (yukawaPrimitiveCardClosedDepthTableCandidate
            canonicalYukawaCoefficientPrimitiveCardPacket
            yukawaSectorInformationIncidence) .V_cb =
          (-143 : Int) ∧
        CKMJarlskogFactor.depthContribution
            (yukawaPrimitiveCardClosedDepthTableCandidate
              canonicalYukawaCoefficientPrimitiveCardPacket
              yukawaSectorInformationIncidence) .V_ub_conj =
            (562 : Int) ∧
          CKMJarlskogFactor.depthContribution
              (yukawaPrimitiveCardClosedDepthTableCandidate
                canonicalYukawaCoefficientPrimitiveCardPacket
                yukawaSectorInformationIncidence) .V_cs_conj =
              (193 : Int)
  ckm_depth_sum :
    ckmJarlskogFourProductDepthSum
        (yukawaPrimitiveCardClosedDepthTableCandidate
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence) =
      (ckmCPDepthSum : Int)

/-- THEOREM 10: full beta-vector shared-axis three-nail producer certificate.
-/
def fullBetaVectorSharedAxisThreeNailProducerCertificate :
    FullBetaVectorSharedAxisThreeNailProducerCertificate where
  full_beta_vector_alpha := fullBetaVectorAlphaResidualProducerCertificate
  trace_weighted_three_nail := traceWeightedSharedAxisThreeNailProducerCertificate
  canonical_axis_is_full_vector_color :=
    canonicalOneAxisPrimitiveSourceProducer_axis_eq_fullBetaVectorColor
  full_vector_axis_eq_ten :=
    canonicalOneAxisPrimitiveSourceProducer_fullBetaVectorAxis_eq_ten
  canonical_axis_eq_ten :=
    canonicalOneAxisPrimitiveSourceProducer_axis_eq_ten_via_fullBetaVector
  yukawa_source_law := fullBetaVectorSharedAxis_canonicalYukawaSourceLaw
  yukawa_source_equations :=
    fullBetaVectorSharedAxis_canonicalYukawaSourceEquations
  alpha_inverse_residual :=
    fullBetaVectorSharedAxis_alphaInverseResidual
  yukawa_mass_order := fullBetaVectorSharedAxis_yukawaMassOrder
  ckm_factors := fullBetaVectorSharedAxis_ckmFactors
  ckm_depth_sum := fullBetaVectorSharedAxis_ckmDepthSum

/-! ## Full beta-vector Yukawa depth producer surface -/

/-- The full-beta-vector Yukawa source law is the P657 one-axis law, specialized
to the canonical axis that this file identifies with the full beta-vector color
projection plus the 4D Poincare slots. -/
def FullBetaVectorYukawaPrimitiveCardSourceLaw
    (Y : YukawaCoefficientPrimitiveCardPacket) : Prop :=
  OneAxisYukawaPrimitiveCardSourceLaw
    canonicalOneAxisPrimitiveSourceProducer Y

/-- THEOREM 11: the canonical primitive-card packet satisfies the full-beta-vector
Yukawa source law. -/
theorem canonicalYukawaPrimitiveCardPacket_fullBetaVectorSourceLaw :
    FullBetaVectorYukawaPrimitiveCardSourceLaw
      canonicalYukawaCoefficientPrimitiveCardPacket := by
  exact fullBetaVectorSharedAxis_canonicalYukawaSourceLaw

/-- THEOREM 12: the full-beta-vector Yukawa source law implies the primitive-card
source equations from P606. -/
theorem fullBetaVectorYukawaSourceLaw_to_sourceEquations
    (Y : YukawaCoefficientPrimitiveCardPacket)
    (hY : FullBetaVectorYukawaPrimitiveCardSourceLaw Y) :
    YukawaPrimitiveCardSourceEquations Y := by
  exact oneAxisYukawaPrimitiveCardSourceLaw_to_sourceEquations
    canonicalOneAxisPrimitiveSourceProducer Y hY

/-- THEOREM 13: the full-beta-vector Yukawa source-law surface is a singleton at
the primitive-card packet level. -/
theorem eq_canonicalYukawaPrimitiveCardPacket_of_fullBetaVectorSourceLaw
    (Y : YukawaCoefficientPrimitiveCardPacket)
    (hY : FullBetaVectorYukawaPrimitiveCardSourceLaw Y) :
    Y = canonicalYukawaCoefficientPrimitiveCardPacket := by
  exact eq_canonicalYukawaPrimitiveCardPacket_of_oneAxisSourceLaw
    canonicalOneAxisPrimitiveSourceProducer Y hY

/-- A Yukawa depth table is accepted by the full-beta-vector producer surface
when it is generated from a full-beta-vector primitive-card packet and an
endpoint-signature preserving SU(7) sector schedule. -/
def FullBetaVectorYukawaDepthProducerSurface
    (T : YukawaDepthTableCandidate) : Prop :=
  ∃ Y : YukawaCoefficientPrimitiveCardPacket,
    ∃ f : YukawaInteractionSector -> InformationSlot,
      FullBetaVectorYukawaPrimitiveCardSourceLaw Y ∧
        YukawaSectorEndpointSignaturePreservingSchedule f ∧
          T =
            coefficientScheduleYukawaDepthTableCandidate
              (primitiveCardYukawaDepthStencilCoefficientVector Y) f

/-- THEOREM 14: the selected table is accepted by the full-beta-vector Yukawa
depth producer surface. -/
theorem selectedYukawaDepthTableCandidate_fullBetaVectorProducer :
    FullBetaVectorYukawaDepthProducerSurface
      selectedYukawaDepthTableCandidate := by
  refine
    ⟨canonicalYukawaCoefficientPrimitiveCardPacket,
      yukawaSectorInformationIncidence,
      canonicalYukawaPrimitiveCardPacket_fullBetaVectorSourceLaw,
      yukawaSectorInformationIncidence_endpointPreserving, ?_⟩
  ext y
  simp [coefficientScheduleYukawaDepthTableCandidate,
    selectedYukawaDepthTableCandidate]
  simpa [canonicalPrimitiveCardYukawaDepthStencilCoefficientVector] using
    (coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
      canonicalPrimitiveCardYukawaDepthStencilCoefficientVector
      canonicalPrimitiveCardYukawaDepthStencilCoefficientVector_sourceEquations
      yukawaSectorInformationIncidence
      yukawaSectorInformationIncidence_endpointPreserving y).symm

/-- THEOREM 15: the full-beta-vector surface is a refinement of the P645 SU(7)
primitive depth-producer surface. -/
theorem fullBetaVectorYukawaDepthProducerSurface_to_su7Primitive
    (T : YukawaDepthTableCandidate)
    (hT : FullBetaVectorYukawaDepthProducerSurface T) :
    SU7PrimitiveYukawaDepthProducerSurface T := by
  rcases hT with ⟨Y, f, hY, hf, hT⟩
  exact
    ⟨Y, f,
      fullBetaVectorYukawaSourceLaw_to_sourceEquations Y hY,
      hf, hT⟩

/-- THEOREM 16: every accepted full-beta-vector producer table is the selected
nine-depth table. -/
theorem eq_selectedYukawaDepthTableCandidate_of_fullBetaVectorProducer
    (T : YukawaDepthTableCandidate)
    (hT : FullBetaVectorYukawaDepthProducerSurface T) :
    T = selectedYukawaDepthTableCandidate := by
  exact eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer T
    (fullBetaVectorYukawaDepthProducerSurface_to_su7Primitive T hT)

/-- THEOREM 17: the full-beta-vector depth producer surface is exactly the
selected table. -/
theorem fullBetaVectorYukawaDepthProducerSurface_iff_selected
    (T : YukawaDepthTableCandidate) :
    FullBetaVectorYukawaDepthProducerSurface T ↔
      T = selectedYukawaDepthTableCandidate := by
  constructor
  · exact eq_selectedYukawaDepthTableCandidate_of_fullBetaVectorProducer T
  · intro hT
    rw [hT]
    exact selectedYukawaDepthTableCandidate_fullBetaVectorProducer

/-- THEOREM 18: the full-beta-vector surface has no table-level continuous
freedom. -/
theorem fullBetaVectorYukawaDepthProducerSurface_noFree :
    NoContinuousFreeYukawaDepthTableParameters
      FullBetaVectorYukawaDepthProducerSurface := by
  intro T U hT hU
  rw [eq_selectedYukawaDepthTableCandidate_of_fullBetaVectorProducer T hT,
    eq_selectedYukawaDepthTableCandidate_of_fullBetaVectorProducer U hU]

/-- THEOREM 19: any full-beta-vector accepted table has the nine named integer
depths. -/
theorem fullBetaVectorYukawaDepthProducerSurface_namedDepths
    (T : YukawaDepthTableCandidate)
    (hT : FullBetaVectorYukawaDepthProducerSurface T) :
    T.depth .top = 50 ∧
      T.depth .bottom = 346 ∧
      T.depth .tau = 372 ∧
      T.depth .charm = 489 ∧
      T.depth .muon = 583 ∧
      T.depth .strange = 682 ∧
      T.depth .down = 880 ∧
      T.depth .up = 908 ∧
      T.depth .electron = 982 := by
  exact su7PrimitiveYukawaDepthProducerSurface_namedDepths T
    (fullBetaVectorYukawaDepthProducerSurface_to_su7Primitive T hT)

/-- THEOREM 20: any full-beta-vector accepted table has the documented
mass-order depth list. -/
theorem fullBetaVectorYukawaDepthProducerSurface_massOrder_eq
    (T : YukawaDepthTableCandidate)
    (hT : FullBetaVectorYukawaDepthProducerSurface T) :
    T.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  exact su7PrimitiveYukawaDepthProducerSurface_massOrder_eq T
    (fullBetaVectorYukawaDepthProducerSurface_to_su7Primitive T hT)

/-- THEOREM 21: any full-beta-vector accepted table has typed Jarlskog
four-product depth sum `386`. -/
theorem fullBetaVectorYukawaDepthProducerSurface_jarlskog_eq_386
    (T : YukawaDepthTableCandidate)
    (hT : FullBetaVectorYukawaDepthProducerSurface T) :
    ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int) := by
  exact su7PrimitiveYukawaDepthProducerSurface_jarlskog_eq_386 T
    (fullBetaVectorYukawaDepthProducerSurface_to_su7Primitive T hT)

/-- THEOREM 22: the table-level CKM depth sum is also forced to `386` on the
full-beta-vector surface. -/
theorem fullBetaVectorYukawaDepthProducerSurface_ckmTableSum_eq_386
    (T : YukawaDepthTableCandidate)
    (hT : FullBetaVectorYukawaDepthProducerSurface T) :
    ckmDepthSum_fromYukawaDepthTable T = (ckmCPDepthSum : Int) := by
  exact su7PrimitiveYukawaDepthProducerSurface_ckmTableSum_eq_386 T
    (fullBetaVectorYukawaDepthProducerSurface_to_su7Primitive T hT)

/-- Compact certificate: the full beta-vector shared axis now carries a genuine
Yukawa depth producer surface.  Any accepted packet/schedule pair collapses to
the selected nine-depth table and therefore to CKM/Jarlskog depth sum `386`. -/
structure FullBetaVectorYukawaDepthProducerCertificate where
  shared_axis_three_nail :
    FullBetaVectorSharedAxisThreeNailProducerCertificate
  endpoint_orientation :
    YukawaSectorEndpointOrientationUniquenessReceipt
  canonical_source_law :
    FullBetaVectorYukawaPrimitiveCardSourceLaw
      canonicalYukawaCoefficientPrimitiveCardPacket
  source_law_to_source_equations :
    ∀ Y : YukawaCoefficientPrimitiveCardPacket,
      FullBetaVectorYukawaPrimitiveCardSourceLaw Y ->
        YukawaPrimitiveCardSourceEquations Y
  source_law_singleton :
    ∀ Y : YukawaCoefficientPrimitiveCardPacket,
      FullBetaVectorYukawaPrimitiveCardSourceLaw Y ->
        Y = canonicalYukawaCoefficientPrimitiveCardPacket
  selected_surface :
    FullBetaVectorYukawaDepthProducerSurface
      selectedYukawaDepthTableCandidate
  surface_iff_selected :
    ∀ T : YukawaDepthTableCandidate,
      FullBetaVectorYukawaDepthProducerSurface T ↔
        T = selectedYukawaDepthTableCandidate
  no_free :
    NoContinuousFreeYukawaDepthTableParameters
      FullBetaVectorYukawaDepthProducerSurface
  named_depths :
    ∀ T : YukawaDepthTableCandidate,
      FullBetaVectorYukawaDepthProducerSurface T ->
        T.depth .top = 50 ∧
          T.depth .bottom = 346 ∧
          T.depth .tau = 372 ∧
          T.depth .charm = 489 ∧
          T.depth .muon = 583 ∧
          T.depth .strange = 682 ∧
          T.depth .down = 880 ∧
          T.depth .up = 908 ∧
          T.depth .electron = 982
  mass_order :
    ∀ T : YukawaDepthTableCandidate,
      FullBetaVectorYukawaDepthProducerSurface T ->
        T.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982]
  typed_jarlskog_sum :
    ∀ T : YukawaDepthTableCandidate,
      FullBetaVectorYukawaDepthProducerSurface T ->
        ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int)
  table_ckm_sum :
    ∀ T : YukawaDepthTableCandidate,
      FullBetaVectorYukawaDepthProducerSurface T ->
        ckmDepthSum_fromYukawaDepthTable T = (ckmCPDepthSum : Int)

/-- THEOREM 23: full beta-vector Yukawa-depth producer certificate. -/
def fullBetaVectorYukawaDepthProducerCertificate :
    FullBetaVectorYukawaDepthProducerCertificate where
  shared_axis_three_nail :=
    fullBetaVectorSharedAxisThreeNailProducerCertificate
  endpoint_orientation := yukawaSectorEndpointOrientationUniquenessReceipt
  canonical_source_law :=
    canonicalYukawaPrimitiveCardPacket_fullBetaVectorSourceLaw
  source_law_to_source_equations :=
    fullBetaVectorYukawaSourceLaw_to_sourceEquations
  source_law_singleton :=
    eq_canonicalYukawaPrimitiveCardPacket_of_fullBetaVectorSourceLaw
  selected_surface :=
    selectedYukawaDepthTableCandidate_fullBetaVectorProducer
  surface_iff_selected :=
    fullBetaVectorYukawaDepthProducerSurface_iff_selected
  no_free := fullBetaVectorYukawaDepthProducerSurface_noFree
  named_depths := fullBetaVectorYukawaDepthProducerSurface_namedDepths
  mass_order := fullBetaVectorYukawaDepthProducerSurface_massOrder_eq
  typed_jarlskog_sum :=
    fullBetaVectorYukawaDepthProducerSurface_jarlskog_eq_386
  table_ckm_sum :=
    fullBetaVectorYukawaDepthProducerSurface_ckmTableSum_eq_386

/-! ## Product surface for all three current producer nails -/

/-- Product candidate for the current three producer nails: an alpha residual
candidate plus a Yukawa-depth table candidate.  The CKM/Jarlskog nail is read
from the Yukawa table. -/
abbrev FullBetaVectorThreeNailCandidate :=
  FullBetaVectorAlphaResidualCandidate × YukawaDepthTableCandidate

/-- The canonical product candidate for the current three-nail surface. -/
def canonicalFullBetaVectorThreeNailCandidate :
    FullBetaVectorThreeNailCandidate :=
  (canonicalFullBetaVectorAlphaResidualCandidate,
    selectedYukawaDepthTableCandidate)

/-- The product surface for the current finite three-nail producer. -/
def FullBetaVectorThreeNailProducerSurface
    (C : FullBetaVectorThreeNailCandidate) : Prop :=
  FullBetaVectorAlphaResidualProducerSurface C.1 ∧
    FullBetaVectorYukawaDepthProducerSurface C.2

/-- THEOREM 24: the canonical product candidate lies on the three-nail
surface. -/
theorem canonicalFullBetaVectorThreeNailCandidate_surface :
    FullBetaVectorThreeNailProducerSurface
      canonicalFullBetaVectorThreeNailCandidate := by
  exact
    ⟨canonicalFullBetaVectorAlphaResidualCandidate_surface,
      selectedYukawaDepthTableCandidate_fullBetaVectorProducer⟩

/-- THEOREM 25: every accepted three-nail product candidate is canonical. -/
theorem eq_canonicalFullBetaVectorThreeNailCandidate_of_surface
    (C : FullBetaVectorThreeNailCandidate)
    (hC : FullBetaVectorThreeNailProducerSurface C) :
    C = canonicalFullBetaVectorThreeNailCandidate := by
  rcases C with ⟨A, T⟩
  rcases hC with ⟨hA, hT⟩
  rw [eq_canonicalFullBetaVectorAlphaResidualCandidate_of_surface A hA,
    eq_selectedYukawaDepthTableCandidate_of_fullBetaVectorProducer T hT]
  rfl

/-- THEOREM 26: accepted three-nail product candidates are exactly the
canonical product candidate. -/
theorem fullBetaVectorThreeNailProducerSurface_iff_canonical
    (C : FullBetaVectorThreeNailCandidate) :
    FullBetaVectorThreeNailProducerSurface C ↔
      C = canonicalFullBetaVectorThreeNailCandidate := by
  constructor
  · exact eq_canonicalFullBetaVectorThreeNailCandidate_of_surface C
  · intro hC
    rw [hC]
    exact canonicalFullBetaVectorThreeNailCandidate_surface

/-- No-free predicate for the three-nail product surface. -/
def NoContinuousFreeFullBetaVectorThreeNailParameters
    (constraints : FullBetaVectorThreeNailCandidate -> Prop) : Prop :=
  ∀ C D : FullBetaVectorThreeNailCandidate,
    constraints C -> constraints D -> C = D

/-- THEOREM 27: the full beta-vector three-nail product surface is
singleton/no-free. -/
theorem fullBetaVectorThreeNailProducerSurface_noFree :
    NoContinuousFreeFullBetaVectorThreeNailParameters
      FullBetaVectorThreeNailProducerSurface := by
  intro C D hC hD
  rw [eq_canonicalFullBetaVectorThreeNailCandidate_of_surface C hC,
    eq_canonicalFullBetaVectorThreeNailCandidate_of_surface D hD]

/-- Compact certificate: the finite full beta-vector surface jointly forces
the current `alpha_s`, Yukawa-depth, and CKM/Jarlskog producer nails. -/
structure FullBetaVectorThreeNailSurfaceCertificate where
  alpha_surface :
    FullBetaVectorAlphaResidualSurfaceCertificate
  yukawa_surface :
    FullBetaVectorYukawaDepthProducerCertificate
  canonical_surface :
    FullBetaVectorThreeNailProducerSurface
      canonicalFullBetaVectorThreeNailCandidate
  surface_iff_canonical :
    ∀ C : FullBetaVectorThreeNailCandidate,
      FullBetaVectorThreeNailProducerSurface C ↔
        C = canonicalFullBetaVectorThreeNailCandidate
  no_free :
    NoContinuousFreeFullBetaVectorThreeNailParameters
      FullBetaVectorThreeNailProducerSurface
  alpha_inverse_residual :
    ∀ C : FullBetaVectorThreeNailCandidate,
      FullBetaVectorThreeNailProducerSurface C ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.1.producedGap =
          -((89000 : ℚ) / 128511)
  alpha_closes_displayed :
    ∀ C : FullBetaVectorThreeNailCandidate,
      FullBetaVectorThreeNailProducerSurface C ->
        (1 : ℚ) /
            (alphaStrongTwoLoopSMOutputInverse ℚ +
              inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ)
                C.1.producedGap) =
          alphaStrongDisplayed ℚ
  yukawa_mass_order :
    ∀ C : FullBetaVectorThreeNailCandidate,
      FullBetaVectorThreeNailProducerSurface C ->
        C.2.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_jarlskog_sum :
    ∀ C : FullBetaVectorThreeNailCandidate,
      FullBetaVectorThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int)
  ckm_table_sum :
    ∀ C : FullBetaVectorThreeNailCandidate,
      FullBetaVectorThreeNailProducerSurface C ->
        ckmDepthSum_fromYukawaDepthTable C.2 = (ckmCPDepthSum : Int)

/-- THEOREM 28: full beta-vector three-nail product-surface certificate. -/
def fullBetaVectorThreeNailSurfaceCertificate :
    FullBetaVectorThreeNailSurfaceCertificate where
  alpha_surface := fullBetaVectorAlphaResidualSurfaceCertificate
  yukawa_surface := fullBetaVectorYukawaDepthProducerCertificate
  canonical_surface := canonicalFullBetaVectorThreeNailCandidate_surface
  surface_iff_canonical :=
    fullBetaVectorThreeNailProducerSurface_iff_canonical
  no_free := fullBetaVectorThreeNailProducerSurface_noFree
  alpha_inverse_residual := by
    intro C hC
    exact fullBetaVectorAlphaResidualProducerSurface_inverseResidual C.1 hC.1
  alpha_closes_displayed := by
    intro C hC
    exact fullBetaVectorAlphaResidualProducerSurface_closes_displayedAlpha
      C.1 hC.1
  yukawa_mass_order := by
    intro C hC
    exact fullBetaVectorYukawaDepthProducerSurface_massOrder_eq C.2 hC.2
  ckm_jarlskog_sum := by
    intro C hC
    exact fullBetaVectorYukawaDepthProducerSurface_jarlskog_eq_386 C.2 hC.2
  ckm_table_sum := by
    intro C hC
    exact fullBetaVectorYukawaDepthProducerSurface_ckmTableSum_eq_386 C.2 hC.2

/-! ## Input-level product surface for all three current producer nails -/

/-- The one-axis scalar read from a full beta-vector input by projecting to the
color trace input and adding the 4D Poincare pairing slots. -/
def incidenceBetaInputOneAxis
    (I : StandardModelIncidenceBetaVectorInput) : ℚ :=
  betaCoeff I.colorInput +
    (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 : ℚ)

/-- A primitive one-axis producer obtained from a full beta-vector input under
the input source law.  This is the explicit bridge from the trace-input triple
to the one-axis spine used by the Yukawa/CKM side. -/
def oneAxisPrimitiveSourceProducerFromIncidenceBetaInput
    (I : StandardModelIncidenceBetaVectorInput)
    (hI : StandardModelIncidenceBetaVectorInputSourceLaw I) :
    OneAxisPrimitiveSourceProducer where
  qcdInput := I.colorInput
  spacetimeDimension := 4
  axis := incidenceBetaInputOneAxis I
  qcd_input_eq := by
    rcases hI with ⟨hcolor, _hweak, _hhypercharge⟩
    rw [hcolor]
    exact qcdBlockIncidenceOneLoopInput_eq_incidenceCarrierTraceInput.symm
  spacetime_dimension_eq := rfl
  axis_eq_source := rfl

/-- THEOREM 29: any accepted full beta-vector input induces one-axis value
`10`. -/
theorem incidenceBetaInputOneAxis_eq_ten
    (I : StandardModelIncidenceBetaVectorInput)
    (hI : StandardModelIncidenceBetaVectorInputSourceLaw I) :
    incidenceBetaInputOneAxis I = (10 : ℚ) := by
  exact
    oneAxisPrimitiveSourceProducer_axis_eq_ten
      (oneAxisPrimitiveSourceProducerFromIncidenceBetaInput I hI)

/-- THEOREM 30: any accepted full beta-vector input induces the same axis as
the canonical one-axis primitive producer. -/
theorem incidenceBetaInputOneAxis_eq_canonical
    (I : StandardModelIncidenceBetaVectorInput)
    (hI : StandardModelIncidenceBetaVectorInputSourceLaw I) :
    incidenceBetaInputOneAxis I =
      canonicalOneAxisPrimitiveSourceProducer.axis := by
  rw [incidenceBetaInputOneAxis_eq_ten I hI,
    canonicalOneAxisPrimitiveSourceProducer_axis_eq_ten]

/-- Input-level product candidate for the current three producer nails.  The
alpha leg carries the actual `GaugeTraceOneLoopInput` triple from P660 before
projection to the rational beta-vector; the Yukawa/CKM leg is the same
finite-depth table surface as above. -/
abbrev FullBetaVectorInputThreeNailCandidate :=
  FullBetaVectorAlphaResidualInputCandidate × YukawaDepthTableCandidate

/-- The canonical input-level product candidate. -/
def canonicalFullBetaVectorInputThreeNailCandidate :
    FullBetaVectorInputThreeNailCandidate :=
  (canonicalFullBetaVectorAlphaResidualInputCandidate,
    selectedYukawaDepthTableCandidate)

/-- Input-level product surface: the alpha trace inputs must be the SU7
block-incidence inputs, and the Yukawa table must lie on the full-beta-vector
finite producer surface. -/
def FullBetaVectorInputThreeNailProducerSurface
    (C : FullBetaVectorInputThreeNailCandidate) : Prop :=
  FullBetaVectorAlphaResidualInputProducerSurface C.1 ∧
    FullBetaVectorYukawaDepthProducerSurface C.2

/-- THEOREM 31: the canonical input-level product candidate lies on the
three-nail surface. -/
theorem canonicalFullBetaVectorInputThreeNailCandidate_surface :
    FullBetaVectorInputThreeNailProducerSurface
      canonicalFullBetaVectorInputThreeNailCandidate := by
  exact
    ⟨canonicalFullBetaVectorAlphaResidualInputCandidate_surface,
      selectedYukawaDepthTableCandidate_fullBetaVectorProducer⟩

/-- THEOREM 32: every accepted input-level three-nail product candidate is
canonical. -/
theorem eq_canonicalFullBetaVectorInputThreeNailCandidate_of_surface
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C = canonicalFullBetaVectorInputThreeNailCandidate := by
  rcases C with ⟨A, T⟩
  rcases hC with ⟨hA, hT⟩
  rw [eq_canonicalFullBetaVectorAlphaResidualInputCandidate_of_surface A hA,
    eq_selectedYukawaDepthTableCandidate_of_fullBetaVectorProducer T hT]
  rfl

/-- THEOREM 33: accepted input-level three-nail product candidates are exactly
the canonical input product candidate. -/
theorem fullBetaVectorInputThreeNailProducerSurface_iff_canonical
    (C : FullBetaVectorInputThreeNailCandidate) :
    FullBetaVectorInputThreeNailProducerSurface C ↔
      C = canonicalFullBetaVectorInputThreeNailCandidate := by
  constructor
  · exact eq_canonicalFullBetaVectorInputThreeNailCandidate_of_surface C
  · intro hC
    rw [hC]
    exact canonicalFullBetaVectorInputThreeNailCandidate_surface

/-- No-free predicate for the input-level three-nail product surface. -/
def NoContinuousFreeFullBetaVectorInputThreeNailParameters
    (constraints : FullBetaVectorInputThreeNailCandidate -> Prop) : Prop :=
  ∀ C D : FullBetaVectorInputThreeNailCandidate,
    constraints C -> constraints D -> C = D

/-- THEOREM 34: the input-level three-nail product surface is singleton/no-free.
-/
theorem fullBetaVectorInputThreeNailProducerSurface_noFree :
    NoContinuousFreeFullBetaVectorInputThreeNailParameters
      FullBetaVectorInputThreeNailProducerSurface := by
  intro C D hC hD
  rw [eq_canonicalFullBetaVectorInputThreeNailCandidate_of_surface C hC,
    eq_canonicalFullBetaVectorInputThreeNailCandidate_of_surface D hD]

/-- THEOREM 35: any accepted input-level product transports its alpha trace
inputs to the full Standard-Model incidence beta-vector source law. -/
theorem fullBetaVectorInputThreeNailProducerSurface_inputToVectorSourceLaw
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    StandardModelIncidenceBetaVectorSourceLaw
      (betaVectorFromIncidenceInput C.1.betaInput) := by
  exact betaVectorFromIncidenceInput_sourceLaw C.1.betaInput hC.1.1

/-- THEOREM 36: any accepted input-level product induces the shared one-axis
value `10` from its trace-input triple. -/
theorem fullBetaVectorInputThreeNailProducerSurface_inputAxis_eq_ten
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    incidenceBetaInputOneAxis C.1.betaInput = (10 : ℚ) := by
  exact incidenceBetaInputOneAxis_eq_ten C.1.betaInput hC.1.1

/-- THEOREM 37: any accepted input-level product induces the canonical
one-axis value from its trace-input triple. -/
theorem fullBetaVectorInputThreeNailProducerSurface_inputAxis_eq_canonical
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    incidenceBetaInputOneAxis C.1.betaInput =
      canonicalOneAxisPrimitiveSourceProducer.axis := by
  exact incidenceBetaInputOneAxis_eq_canonical C.1.betaInput hC.1.1

/-- THEOREM 38: any accepted input-level product has alpha gap `89/10000`. -/
theorem fullBetaVectorInputThreeNailProducerSurface_alphaGap
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.1.producedGap = (89 : ℚ) / 10000 := by
  exact fullBetaVectorAlphaResidualInputProducerSurface_gap C.1 hC.1

/-- THEOREM 39: any accepted input-level product has the exact inverse residual
`-89000/128511`. -/
theorem fullBetaVectorInputThreeNailProducerSurface_alphaInverseResidual
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        C.1.producedGap =
      -((89000 : ℚ) / 128511) := by
  exact fullBetaVectorAlphaResidualInputProducerSurface_inverseResidual
    C.1 hC.1

/-- THEOREM 40: any accepted input-level product closes the displayed
strong-coupling value. -/
theorem fullBetaVectorInputThreeNailProducerSurface_closesDisplayedAlpha
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.1.producedGap) =
      alphaStrongDisplayed ℚ := by
  exact fullBetaVectorAlphaResidualInputProducerSurface_closes_displayedAlpha
    C.1 hC.1

/-- Compact certificate: the input-level finite full beta-vector surface jointly
forces the current `alpha_s`, Yukawa-depth, and CKM/Jarlskog producer nails.
This is stronger than `FullBetaVectorThreeNailSurfaceCertificate` only on the
alpha leg: it keeps the SU7 block-incidence trace inputs visible instead of
starting from the rational beta-vector. -/
structure FullBetaVectorInputThreeNailSurfaceCertificate where
  input_alpha_surface :
    FullBetaVectorAlphaResidualInputSurfaceCertificate
  vector_three_nail_surface :
    FullBetaVectorThreeNailSurfaceCertificate
  canonical_surface :
    FullBetaVectorInputThreeNailProducerSurface
      canonicalFullBetaVectorInputThreeNailCandidate
  surface_iff_canonical :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ↔
        C = canonicalFullBetaVectorInputThreeNailCandidate
  no_free :
    NoContinuousFreeFullBetaVectorInputThreeNailParameters
      FullBetaVectorInputThreeNailProducerSurface
  input_to_vector_source_law :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        StandardModelIncidenceBetaVectorSourceLaw
          (betaVectorFromIncidenceInput C.1.betaInput)
  input_axis_eq_ten :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        incidenceBetaInputOneAxis C.1.betaInput = (10 : ℚ)
  input_axis_eq_canonical :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        incidenceBetaInputOneAxis C.1.betaInput =
          canonicalOneAxisPrimitiveSourceProducer.axis
  alpha_gap :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.1.producedGap = (89 : ℚ) / 10000
  alpha_inverse_residual :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.1.producedGap =
          -((89000 : ℚ) / 128511)
  alpha_closes_displayed :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (1 : ℚ) /
            (alphaStrongTwoLoopSMOutputInverse ℚ +
              inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ)
                C.1.producedGap) =
          alphaStrongDisplayed ℚ
  yukawa_mass_order :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.2.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_jarlskog_sum :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int)
  ckm_table_sum :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmDepthSum_fromYukawaDepthTable C.2 = (ckmCPDepthSum : Int)

/-- THEOREM 41: input-level full beta-vector three-nail product-surface
certificate. -/
def fullBetaVectorInputThreeNailSurfaceCertificate :
    FullBetaVectorInputThreeNailSurfaceCertificate where
  input_alpha_surface := fullBetaVectorAlphaResidualInputSurfaceCertificate
  vector_three_nail_surface := fullBetaVectorThreeNailSurfaceCertificate
  canonical_surface := canonicalFullBetaVectorInputThreeNailCandidate_surface
  surface_iff_canonical :=
    fullBetaVectorInputThreeNailProducerSurface_iff_canonical
  no_free := fullBetaVectorInputThreeNailProducerSurface_noFree
  input_to_vector_source_law :=
    fullBetaVectorInputThreeNailProducerSurface_inputToVectorSourceLaw
  input_axis_eq_ten :=
    fullBetaVectorInputThreeNailProducerSurface_inputAxis_eq_ten
  input_axis_eq_canonical :=
    fullBetaVectorInputThreeNailProducerSurface_inputAxis_eq_canonical
  alpha_gap := fullBetaVectorInputThreeNailProducerSurface_alphaGap
  alpha_inverse_residual :=
    fullBetaVectorInputThreeNailProducerSurface_alphaInverseResidual
  alpha_closes_displayed :=
    fullBetaVectorInputThreeNailProducerSurface_closesDisplayedAlpha
  yukawa_mass_order := by
    intro C hC
    exact fullBetaVectorYukawaDepthProducerSurface_massOrder_eq C.2 hC.2
  ckm_jarlskog_sum := by
    intro C hC
    exact fullBetaVectorYukawaDepthProducerSurface_jarlskog_eq_386 C.2 hC.2
  ckm_table_sum := by
    intro C hC
    exact fullBetaVectorYukawaDepthProducerSurface_ckmTableSum_eq_386 C.2 hC.2

end StandardModelConstraint
end SaturationMonoid
