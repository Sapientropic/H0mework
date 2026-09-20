import Mathlib.Tactic
import H0mework.Physics.RepresentationSources.P659

/-!
# Proposition 660: full beta-vector projection into the alpha residual nail

P659 welds the three active Standard-Model producer nails onto one shared
axis.  Its alpha leg still names only the color/QCD input explicitly.  This
file connects that color input back to the already-certified full
`SU(3) x SU(2) x U(1)` one-loop carrier from P462:

* the incidence carrier produces the full residual/asymptotic beta vector
  `(7, 19/6, -41/6)`;
* the QCD input used by the alpha residual certificate is exactly the color
  projection of that vector;
* therefore the `-89000/128511` alpha inverse residual is a projection of the
  full beta-vector carrier, not a stand-alone QCD constant.

Boundary: as in P464/P658, the universal one-loop weights are still standard
QFT input.  This proposition removes the color-only presentation artifact; it
does not derive those universal weights from heat-kernel/Feynman analysis or
add threshold / three-loop / Higgs-spectrum dynamics.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open InformationMatterProjection

/-! ## Full incidence beta vector -/

/-- The residual/asymptotic beta-vector coordinates selected by the
`3+2+1+1` SU(7) block-incidence matter carrier. -/
@[ext]
structure StandardModelIncidenceBetaVector where
  color : ℚ
  weak : ℚ
  hypercharge : ℚ

/-- The concrete vector produced by the block-incidence carrier. -/
def standardModelIncidenceBetaVector :
    StandardModelIncidenceBetaVector where
  color := betaCoeff (incidenceCarrierTraceInput .colorSU3)
  weak := betaCoeff (incidenceCarrierTraceInput .weakSU2)
  hypercharge := betaCoeff (incidenceCarrierTraceInput .hyperchargeU1)

/-- THEOREM 1: the color component is `7`. -/
theorem standardModelIncidenceBetaVector_color :
    standardModelIncidenceBetaVector.color = (7 : ℚ) := by
  exact qcd_b0_from_block_incidence_carrier

/-- THEOREM 2: the weak component is `19/6`. -/
theorem standardModelIncidenceBetaVector_weak :
    standardModelIncidenceBetaVector.weak = (19 : ℚ) / 6 := by
  exact weak_b0_from_block_incidence_carrier

/-- THEOREM 3: the hypercharge component is `-41/6` in the residual /
asymptotic convention. -/
theorem standardModelIncidenceBetaVector_hypercharge :
    standardModelIncidenceBetaVector.hypercharge = -((41 : ℚ) / 6) := by
  exact hypercharge_b0_from_block_incidence_carrier

/-! ## The alpha residual uses the color projection -/

/-- THEOREM 4: the QCD block input used by the alpha residual certificate is
the color projection of the full incidence beta vector. -/
theorem qcdBlockInput_betaCoeff_eq_fullBetaVector_color :
    betaCoeff qcdBlockIncidenceOneLoopInput =
      standardModelIncidenceBetaVector.color := by
  rw [qcdBlockIncidenceOneLoopInput_eq_incidenceCarrierTraceInput]
  rfl

/-- THEOREM 5: the trace-weighted presentation of that same QCD input is also
the color projection of the full incidence beta vector. -/
theorem qcdBlockInput_traceWeighted_eq_fullBetaVector_color :
    applyTraceOneLoopWeights
        standardTraceOneLoopUniversalWeights
        qcdBlockIncidenceOneLoopInput =
      standardModelIncidenceBetaVector.color := by
  rw [(alphaStrongQCDInput_betaCoeff_traceWeighted).symm,
    qcdBlockInput_betaCoeff_eq_fullBetaVector_color]

/-- THEOREM 6: the color projection plus the 4D Poincare slot count is the
shared axis `10`. -/
theorem fullBetaVectorColorPoincareAxis_eq_ten :
    standardModelIncidenceBetaVector.color +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
        ℚ) =
        (10 : ℚ) := by
  rw [standardModelIncidenceBetaVector_color,
    AffineRelaxation.GeometryConnection.four_poincarePairingSlotCount_eq_three]
  norm_num

/-- THEOREM 7: rewriting the P659 trace-weighted axis through the full
beta-vector color projection gives the same shared axis. -/
theorem traceWeightedAxis_eq_fullBetaVectorColorAxis :
    applyTraceOneLoopWeights
        standardTraceOneLoopUniversalWeights
        qcdBlockIncidenceOneLoopInput +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
        ℚ) =
      standardModelIncidenceBetaVector.color +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
        ℚ) := by
  rw [qcdBlockInput_traceWeighted_eq_fullBetaVector_color]

/-- THEOREM 8: the full beta-vector color projection transports all the way
to the exact alpha inverse residual. -/
theorem fullBetaVectorColor_alphaInverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareClosedGap =
      -((89000 : ℚ) / 128511) := by
  exact traceWeightedSharedAxis_alphaInverseResidual

/-! ## Certificate -/

/-- Compact certificate: the current alpha residual nail is the color
projection of the full Standard-Model incidence beta-vector carrier. -/
structure FullBetaVectorAlphaResidualProducerCertificate where
  full_one_loop_carrier :
    StandardModelOneLoopCarrierFinalReceipt
  shared_three_nail :
    TraceWeightedSharedAxisThreeNailProducerCertificate
  color_value :
    standardModelIncidenceBetaVector.color = (7 : ℚ)
  weak_value :
    standardModelIncidenceBetaVector.weak = (19 : ℚ) / 6
  hypercharge_value :
    standardModelIncidenceBetaVector.hypercharge = -((41 : ℚ) / 6)
  qcd_is_color_projection :
    betaCoeff qcdBlockIncidenceOneLoopInput =
      standardModelIncidenceBetaVector.color
  trace_weighted_qcd_is_color_projection :
    applyTraceOneLoopWeights
        standardTraceOneLoopUniversalWeights
        qcdBlockIncidenceOneLoopInput =
      standardModelIncidenceBetaVector.color
  color_poincare_axis :
    standardModelIncidenceBetaVector.color +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
        ℚ) =
        (10 : ℚ)
  trace_axis_rewrites_to_full_vector_axis :
    applyTraceOneLoopWeights
        standardTraceOneLoopUniversalWeights
        qcdBlockIncidenceOneLoopInput +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
        ℚ) =
      standardModelIncidenceBetaVector.color +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
        ℚ)
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareClosedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 9: full beta-vector alpha residual producer certificate. -/
def fullBetaVectorAlphaResidualProducerCertificate :
    FullBetaVectorAlphaResidualProducerCertificate where
  full_one_loop_carrier := standardModelOneLoopCarrierFinalReceipt
  shared_three_nail := traceWeightedSharedAxisThreeNailProducerCertificate
  color_value := standardModelIncidenceBetaVector_color
  weak_value := standardModelIncidenceBetaVector_weak
  hypercharge_value := standardModelIncidenceBetaVector_hypercharge
  qcd_is_color_projection := qcdBlockInput_betaCoeff_eq_fullBetaVector_color
  trace_weighted_qcd_is_color_projection :=
    qcdBlockInput_traceWeighted_eq_fullBetaVector_color
  color_poincare_axis := fullBetaVectorColorPoincareAxis_eq_ten
  trace_axis_rewrites_to_full_vector_axis :=
    traceWeightedAxis_eq_fullBetaVectorColorAxis
  inverse_residual := fullBetaVectorColor_alphaInverseResidual

/-! ## Full beta-vector alpha residual surface -/

/-- Source law for a full Standard-Model incidence beta-vector candidate.

This is the finite carrier law P660 exposes: the SU(7) block-incidence matter
carrier selects the residual/asymptotic vector `(7, 19/6, -41/6)`. -/
def StandardModelIncidenceBetaVectorSourceLaw
    (V : StandardModelIncidenceBetaVector) : Prop :=
  V.color = (7 : ℚ) ∧
    V.weak = (19 : ℚ) / 6 ∧
      V.hypercharge = -((41 : ℚ) / 6)

/-- THEOREM 10: the canonical full beta vector satisfies the finite source law.
-/
theorem standardModelIncidenceBetaVector_sourceLaw :
    StandardModelIncidenceBetaVectorSourceLaw
      standardModelIncidenceBetaVector := by
  exact
    ⟨standardModelIncidenceBetaVector_color,
      standardModelIncidenceBetaVector_weak,
      standardModelIncidenceBetaVector_hypercharge⟩

/-- THEOREM 11: the full beta-vector source law is a singleton. -/
theorem eq_standardModelIncidenceBetaVector_of_sourceLaw
    (V : StandardModelIncidenceBetaVector)
    (hV : StandardModelIncidenceBetaVectorSourceLaw V) :
    V = standardModelIncidenceBetaVector := by
  rcases hV with ⟨hcolor, hweak, hhypercharge⟩
  ext
  · rw [hcolor, standardModelIncidenceBetaVector_color]
  · rw [hweak, standardModelIncidenceBetaVector_weak]
  · rw [hhypercharge, standardModelIncidenceBetaVector_hypercharge]

/-! ## Input-level source law for the full beta-vector -/

/-- The actual one-loop trace inputs behind a full beta-vector candidate. -/
@[ext]
structure StandardModelIncidenceBetaVectorInput where
  colorInput : GaugeTraceOneLoopInput
  weakInput : GaugeTraceOneLoopInput
  hyperchargeInput : GaugeTraceOneLoopInput

/-- The canonical trace-input triple selected by the SU7 block-incidence
matter carrier. -/
def standardModelIncidenceBetaVectorInput :
    StandardModelIncidenceBetaVectorInput where
  colorInput := incidenceCarrierTraceInput .colorSU3
  weakInput := incidenceCarrierTraceInput .weakSU2
  hyperchargeInput := incidenceCarrierTraceInput .hyperchargeU1

/-- Input-level source law: the three trace inputs are precisely the three
SU7 block-incidence carrier projections. -/
def StandardModelIncidenceBetaVectorInputSourceLaw
    (I : StandardModelIncidenceBetaVectorInput) : Prop :=
  I.colorInput = incidenceCarrierTraceInput .colorSU3 ∧
    I.weakInput = incidenceCarrierTraceInput .weakSU2 ∧
      I.hyperchargeInput = incidenceCarrierTraceInput .hyperchargeU1

/-- The beta-vector read from an input triple by the standard coefficient
function. -/
def betaVectorFromIncidenceInput
    (I : StandardModelIncidenceBetaVectorInput) :
    StandardModelIncidenceBetaVector where
  color := betaCoeff I.colorInput
  weak := betaCoeff I.weakInput
  hypercharge := betaCoeff I.hyperchargeInput

/-- THEOREM 12a: the canonical input triple satisfies the input-level source
law. -/
theorem standardModelIncidenceBetaVectorInput_sourceLaw :
    StandardModelIncidenceBetaVectorInputSourceLaw
      standardModelIncidenceBetaVectorInput := by
  exact ⟨rfl, rfl, rfl⟩

/-- THEOREM 12b: the input-level source law is a singleton. -/
theorem eq_standardModelIncidenceBetaVectorInput_of_sourceLaw
    (I : StandardModelIncidenceBetaVectorInput)
    (hI : StandardModelIncidenceBetaVectorInputSourceLaw I) :
    I = standardModelIncidenceBetaVectorInput := by
  rcases hI with ⟨hcolor, hweak, hhypercharge⟩
  ext
  · exact hcolor
  · exact hweak
  · exact hhypercharge

/-- THEOREM 12c: a source-law input triple reads to the canonical full
beta-vector. -/
theorem betaVectorFromIncidenceInput_eq_standard
    (I : StandardModelIncidenceBetaVectorInput)
    (hI : StandardModelIncidenceBetaVectorInputSourceLaw I) :
    betaVectorFromIncidenceInput I = standardModelIncidenceBetaVector := by
  rw [eq_standardModelIncidenceBetaVectorInput_of_sourceLaw I hI]
  rfl

/-- THEOREM 12d: a source-law input triple satisfies the beta-vector source
law after applying the coefficient function. -/
theorem betaVectorFromIncidenceInput_sourceLaw
    (I : StandardModelIncidenceBetaVectorInput)
    (hI : StandardModelIncidenceBetaVectorInputSourceLaw I) :
    StandardModelIncidenceBetaVectorSourceLaw
      (betaVectorFromIncidenceInput I) := by
  rw [betaVectorFromIncidenceInput_eq_standard I hI]
  exact standardModelIncidenceBetaVector_sourceLaw

/-- The closed alpha gap read directly from a full beta-vector candidate:
only the color projection enters the current alpha leg, and the 4D Poincare
slot count supplies the other part of the shared axis. -/
def alphaStrongGapFromFullBetaVector
    (V : StandardModelIncidenceBetaVector) : ℚ :=
  let a : ℚ :=
    V.color +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
        ℚ)
  ((((2 : ℚ) ^ 7 + (a - 1)) - ((7 : ℚ) ^ 2 - 1)) /
    (a ^ alphaStrongResidualResolutionExponent))

/-- Candidate object for the full beta-vector alpha residual producer surface.
-/
@[ext]
structure FullBetaVectorAlphaResidualCandidate where
  betaVector : StandardModelIncidenceBetaVector
  producedGap : ℚ

/-- The canonical full beta-vector alpha residual candidate. -/
def canonicalFullBetaVectorAlphaResidualCandidate :
    FullBetaVectorAlphaResidualCandidate where
  betaVector := standardModelIncidenceBetaVector
  producedGap := alphaStrongGapFromFullBetaVector standardModelIncidenceBetaVector

/-- Full beta-vector alpha residual producer surface: the beta vector satisfies
the finite carrier source law, and the produced gap is read from the color
projection plus the 4D Poincare slot count. -/
def FullBetaVectorAlphaResidualProducerSurface
    (C : FullBetaVectorAlphaResidualCandidate) : Prop :=
  StandardModelIncidenceBetaVectorSourceLaw C.betaVector ∧
    C.producedGap = alphaStrongGapFromFullBetaVector C.betaVector

/-- THEOREM 12: the canonical candidate lies on the full beta-vector alpha
residual producer surface. -/
theorem canonicalFullBetaVectorAlphaResidualCandidate_surface :
    FullBetaVectorAlphaResidualProducerSurface
      canonicalFullBetaVectorAlphaResidualCandidate := by
  exact ⟨standardModelIncidenceBetaVector_sourceLaw, rfl⟩

/-- THEOREM 13: a source-law full beta vector has the shared alpha axis `10`.
-/
theorem fullBetaVectorSourceLaw_axis_eq_ten
    (V : StandardModelIncidenceBetaVector)
    (hV : StandardModelIncidenceBetaVectorSourceLaw V) :
    V.color +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
        ℚ) =
      (10 : ℚ) := by
  rcases hV with ⟨hcolor, _, _⟩
  rw [hcolor,
    AffineRelaxation.GeometryConnection.four_poincarePairingSlotCount_eq_three]
  norm_num

/-- THEOREM 14: any source-law full beta vector produces alpha gap `89/10000`.
-/
theorem alphaStrongGapFromFullBetaVector_eq_89_div_10000
    (V : StandardModelIncidenceBetaVector)
    (hV : StandardModelIncidenceBetaVectorSourceLaw V) :
    alphaStrongGapFromFullBetaVector V = (89 : ℚ) / 10000 := by
  unfold alphaStrongGapFromFullBetaVector
  rw [fullBetaVectorSourceLaw_axis_eq_ten V hV]
  norm_num [alphaStrongResidualResolutionExponent]

/-- THEOREM 15: every accepted full beta-vector alpha candidate is canonical.
-/
theorem eq_canonicalFullBetaVectorAlphaResidualCandidate_of_surface
    (C : FullBetaVectorAlphaResidualCandidate)
    (hC : FullBetaVectorAlphaResidualProducerSurface C) :
    C = canonicalFullBetaVectorAlphaResidualCandidate := by
  rcases C with ⟨V, producedGap⟩
  rcases hC with ⟨hV, hgap⟩
  have hVeq :
      V = standardModelIncidenceBetaVector :=
    eq_standardModelIncidenceBetaVector_of_sourceLaw V hV
  subst V
  simp [canonicalFullBetaVectorAlphaResidualCandidate] at hgap ⊢
  exact hgap

/-- No-free predicate for full beta-vector alpha residual candidates. -/
def NoContinuousFreeFullBetaVectorAlphaResidualParameters
    (constraints : FullBetaVectorAlphaResidualCandidate -> Prop) : Prop :=
  ∀ C D : FullBetaVectorAlphaResidualCandidate,
    constraints C -> constraints D -> C = D

/-- THEOREM 16: the full beta-vector alpha residual producer surface is a
singleton/no-free surface. -/
theorem fullBetaVectorAlphaResidualProducerSurface_noFree :
    NoContinuousFreeFullBetaVectorAlphaResidualParameters
      FullBetaVectorAlphaResidualProducerSurface := by
  intro C D hC hD
  rw [eq_canonicalFullBetaVectorAlphaResidualCandidate_of_surface C hC,
    eq_canonicalFullBetaVectorAlphaResidualCandidate_of_surface D hD]

/-- THEOREM 17: any accepted candidate has alpha gap `89/10000`. -/
theorem fullBetaVectorAlphaResidualProducerSurface_gap
    (C : FullBetaVectorAlphaResidualCandidate)
    (hC : FullBetaVectorAlphaResidualProducerSurface C) :
    C.producedGap = (89 : ℚ) / 10000 := by
  rcases hC with ⟨hV, hgap⟩
  rw [hgap]
  exact alphaStrongGapFromFullBetaVector_eq_89_div_10000 C.betaVector hV

/-- THEOREM 18: any accepted candidate transports to the exact inverse residual
`-89000/128511`. -/
theorem fullBetaVectorAlphaResidualProducerSurface_inverseResidual
    (C : FullBetaVectorAlphaResidualCandidate)
    (hC : FullBetaVectorAlphaResidualProducerSurface C) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        C.producedGap =
      -((89000 : ℚ) / 128511) := by
  rw [fullBetaVectorAlphaResidualProducerSurface_gap C hC]
  rw [← alphaStrongQCDPoincareClosedGap_eq_89_div_10000]
  exact alphaStrongQCDPoincareClosedGap_inverseCorrection

/-- THEOREM 19: any accepted candidate closes the displayed direct
strong-coupling value. -/
theorem fullBetaVectorAlphaResidualProducerSurface_closes_displayedAlpha
    (C : FullBetaVectorAlphaResidualCandidate)
    (hC : FullBetaVectorAlphaResidualProducerSurface C) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.producedGap) =
      alphaStrongDisplayed ℚ := by
  rw [fullBetaVectorAlphaResidualProducerSurface_gap C hC]
  rw [← alphaStrongQCDPoincareClosedGap_eq_89_div_10000]
  exact alphaStrongQCDPoincareClosedGap_closes_displayedAlpha

/-! ## Full beta-vector alpha residual surface certificate -/

/-- Compact certificate: the full beta-vector alpha residual producer surface
has no candidate-level freedom.  The finite source law fixes the whole beta
vector, the color/Poincare formula fixes the gap, and that gap is exactly the
inverse residual `-89000/128511`. -/
structure FullBetaVectorAlphaResidualSurfaceCertificate where
  full_vector_alpha :
    FullBetaVectorAlphaResidualProducerCertificate
  canonical_surface :
    FullBetaVectorAlphaResidualProducerSurface
      canonicalFullBetaVectorAlphaResidualCandidate
  source_law_singleton :
    ∀ V : StandardModelIncidenceBetaVector,
      StandardModelIncidenceBetaVectorSourceLaw V ->
        V = standardModelIncidenceBetaVector
  axis :
    ∀ V : StandardModelIncidenceBetaVector,
      StandardModelIncidenceBetaVectorSourceLaw V ->
        V.color +
          (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
            ℚ) =
          (10 : ℚ)
  no_free :
    NoContinuousFreeFullBetaVectorAlphaResidualParameters
      FullBetaVectorAlphaResidualProducerSurface
  gap :
    ∀ C : FullBetaVectorAlphaResidualCandidate,
      FullBetaVectorAlphaResidualProducerSurface C ->
        C.producedGap = (89 : ℚ) / 10000
  inverse_residual :
    ∀ C : FullBetaVectorAlphaResidualCandidate,
      FullBetaVectorAlphaResidualProducerSurface C ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.producedGap =
          -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    ∀ C : FullBetaVectorAlphaResidualCandidate,
      FullBetaVectorAlphaResidualProducerSurface C ->
        (1 : ℚ) /
            (alphaStrongTwoLoopSMOutputInverse ℚ +
              inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ)
                C.producedGap) =
          alphaStrongDisplayed ℚ

/-- THEOREM 20: full beta-vector alpha residual surface certificate. -/
def fullBetaVectorAlphaResidualSurfaceCertificate :
    FullBetaVectorAlphaResidualSurfaceCertificate where
  full_vector_alpha := fullBetaVectorAlphaResidualProducerCertificate
  canonical_surface := canonicalFullBetaVectorAlphaResidualCandidate_surface
  source_law_singleton :=
    eq_standardModelIncidenceBetaVector_of_sourceLaw
  axis := fullBetaVectorSourceLaw_axis_eq_ten
  no_free := fullBetaVectorAlphaResidualProducerSurface_noFree
  gap := fullBetaVectorAlphaResidualProducerSurface_gap
  inverse_residual :=
    fullBetaVectorAlphaResidualProducerSurface_inverseResidual
  closes_displayed_alpha :=
    fullBetaVectorAlphaResidualProducerSurface_closes_displayedAlpha

/-! ## Input-level full beta-vector alpha residual surface -/

/-- Candidate object for the input-level alpha residual surface.  Its beta
data are three actual trace inputs, not merely three already-evaluated
rational coordinates. -/
@[ext]
structure FullBetaVectorAlphaResidualInputCandidate where
  betaInput : StandardModelIncidenceBetaVectorInput
  producedGap : ℚ

/-- The canonical input-level alpha residual candidate. -/
def canonicalFullBetaVectorAlphaResidualInputCandidate :
    FullBetaVectorAlphaResidualInputCandidate where
  betaInput := standardModelIncidenceBetaVectorInput
  producedGap :=
    alphaStrongGapFromFullBetaVector
      (betaVectorFromIncidenceInput standardModelIncidenceBetaVectorInput)

/-- Input-level producer surface: the trace inputs must be exactly the SU7
block-incidence carrier inputs, and the gap must be read from those inputs
through the full beta-vector coefficient map. -/
def FullBetaVectorAlphaResidualInputProducerSurface
    (C : FullBetaVectorAlphaResidualInputCandidate) : Prop :=
  StandardModelIncidenceBetaVectorInputSourceLaw C.betaInput ∧
    C.producedGap =
      alphaStrongGapFromFullBetaVector
        (betaVectorFromIncidenceInput C.betaInput)

/-- THEOREM 21: the canonical input-level candidate lies on the surface. -/
theorem canonicalFullBetaVectorAlphaResidualInputCandidate_surface :
    FullBetaVectorAlphaResidualInputProducerSurface
      canonicalFullBetaVectorAlphaResidualInputCandidate := by
  exact ⟨standardModelIncidenceBetaVectorInput_sourceLaw, rfl⟩

/-- THEOREM 22: every accepted input-level alpha candidate is canonical. -/
theorem eq_canonicalFullBetaVectorAlphaResidualInputCandidate_of_surface
    (C : FullBetaVectorAlphaResidualInputCandidate)
    (hC : FullBetaVectorAlphaResidualInputProducerSurface C) :
    C = canonicalFullBetaVectorAlphaResidualInputCandidate := by
  rcases C with ⟨I, producedGap⟩
  rcases hC with ⟨hI, hgap⟩
  have hIeq :
      I = standardModelIncidenceBetaVectorInput :=
    eq_standardModelIncidenceBetaVectorInput_of_sourceLaw I hI
  subst I
  simp [canonicalFullBetaVectorAlphaResidualInputCandidate] at hgap ⊢
  exact hgap

/-- No-free predicate for input-level alpha residual candidates. -/
def NoContinuousFreeFullBetaVectorAlphaResidualInputParameters
    (constraints : FullBetaVectorAlphaResidualInputCandidate -> Prop) : Prop :=
  ∀ C D : FullBetaVectorAlphaResidualInputCandidate,
    constraints C -> constraints D -> C = D

/-- THEOREM 23: the input-level alpha residual surface is singleton/no-free.
-/
theorem fullBetaVectorAlphaResidualInputProducerSurface_noFree :
    NoContinuousFreeFullBetaVectorAlphaResidualInputParameters
      FullBetaVectorAlphaResidualInputProducerSurface := by
  intro C D hC hD
  rw [eq_canonicalFullBetaVectorAlphaResidualInputCandidate_of_surface C hC,
    eq_canonicalFullBetaVectorAlphaResidualInputCandidate_of_surface D hD]

/-- THEOREM 24: any input-level accepted candidate has alpha gap `89/10000`.
-/
theorem fullBetaVectorAlphaResidualInputProducerSurface_gap
    (C : FullBetaVectorAlphaResidualInputCandidate)
    (hC : FullBetaVectorAlphaResidualInputProducerSurface C) :
    C.producedGap = (89 : ℚ) / 10000 := by
  rcases hC with ⟨hI, hgap⟩
  rw [hgap]
  exact alphaStrongGapFromFullBetaVector_eq_89_div_10000
    (betaVectorFromIncidenceInput C.betaInput)
    (betaVectorFromIncidenceInput_sourceLaw C.betaInput hI)

/-- THEOREM 25: any input-level accepted candidate transports to the exact
inverse residual `-89000/128511`. -/
theorem fullBetaVectorAlphaResidualInputProducerSurface_inverseResidual
    (C : FullBetaVectorAlphaResidualInputCandidate)
    (hC : FullBetaVectorAlphaResidualInputProducerSurface C) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        C.producedGap =
      -((89000 : ℚ) / 128511) := by
  rw [fullBetaVectorAlphaResidualInputProducerSurface_gap C hC]
  rw [← alphaStrongQCDPoincareClosedGap_eq_89_div_10000]
  exact alphaStrongQCDPoincareClosedGap_inverseCorrection

/-- THEOREM 26: any input-level accepted candidate closes the displayed direct
strong-coupling value. -/
theorem fullBetaVectorAlphaResidualInputProducerSurface_closes_displayedAlpha
    (C : FullBetaVectorAlphaResidualInputCandidate)
    (hC : FullBetaVectorAlphaResidualInputProducerSurface C) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.producedGap) =
      alphaStrongDisplayed ℚ := by
  rw [fullBetaVectorAlphaResidualInputProducerSurface_gap C hC]
  rw [← alphaStrongQCDPoincareClosedGap_eq_89_div_10000]
  exact alphaStrongQCDPoincareClosedGap_closes_displayedAlpha

/-- Compact certificate: the alpha residual is forced already at the
trace-input layer.  The accepted inputs are the three SU7 block-incidence
carrier projections, and evaluating them gives the same no-free alpha surface.
-/
structure FullBetaVectorAlphaResidualInputSurfaceCertificate where
  vector_surface :
    FullBetaVectorAlphaResidualSurfaceCertificate
  canonical_surface :
    FullBetaVectorAlphaResidualInputProducerSurface
      canonicalFullBetaVectorAlphaResidualInputCandidate
  input_source_law_singleton :
    ∀ I : StandardModelIncidenceBetaVectorInput,
      StandardModelIncidenceBetaVectorInputSourceLaw I ->
        I = standardModelIncidenceBetaVectorInput
  input_to_vector :
    ∀ I : StandardModelIncidenceBetaVectorInput,
      StandardModelIncidenceBetaVectorInputSourceLaw I ->
        betaVectorFromIncidenceInput I = standardModelIncidenceBetaVector
  input_to_vector_source_law :
    ∀ I : StandardModelIncidenceBetaVectorInput,
      StandardModelIncidenceBetaVectorInputSourceLaw I ->
        StandardModelIncidenceBetaVectorSourceLaw
          (betaVectorFromIncidenceInput I)
  no_free :
    NoContinuousFreeFullBetaVectorAlphaResidualInputParameters
      FullBetaVectorAlphaResidualInputProducerSurface
  gap :
    ∀ C : FullBetaVectorAlphaResidualInputCandidate,
      FullBetaVectorAlphaResidualInputProducerSurface C ->
        C.producedGap = (89 : ℚ) / 10000
  inverse_residual :
    ∀ C : FullBetaVectorAlphaResidualInputCandidate,
      FullBetaVectorAlphaResidualInputProducerSurface C ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.producedGap =
          -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    ∀ C : FullBetaVectorAlphaResidualInputCandidate,
      FullBetaVectorAlphaResidualInputProducerSurface C ->
        (1 : ℚ) /
            (alphaStrongTwoLoopSMOutputInverse ℚ +
              inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ)
                C.producedGap) =
          alphaStrongDisplayed ℚ

/-- THEOREM 27: input-level full beta-vector alpha residual certificate. -/
def fullBetaVectorAlphaResidualInputSurfaceCertificate :
    FullBetaVectorAlphaResidualInputSurfaceCertificate where
  vector_surface := fullBetaVectorAlphaResidualSurfaceCertificate
  canonical_surface :=
    canonicalFullBetaVectorAlphaResidualInputCandidate_surface
  input_source_law_singleton :=
    eq_standardModelIncidenceBetaVectorInput_of_sourceLaw
  input_to_vector := betaVectorFromIncidenceInput_eq_standard
  input_to_vector_source_law := betaVectorFromIncidenceInput_sourceLaw
  no_free := fullBetaVectorAlphaResidualInputProducerSurface_noFree
  gap := fullBetaVectorAlphaResidualInputProducerSurface_gap
  inverse_residual :=
    fullBetaVectorAlphaResidualInputProducerSurface_inverseResidual
  closes_displayed_alpha :=
    fullBetaVectorAlphaResidualInputProducerSurface_closes_displayedAlpha

end StandardModelConstraint
end SaturationMonoid
