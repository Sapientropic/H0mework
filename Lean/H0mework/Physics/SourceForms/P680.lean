import H0mework.Physics.JointSources.P679

/-!
# Proposition 680: input-output finite bridge singleton

P679 proves that the finite source-law output surface is a singleton.  This
file welds that output singleton back to the accepted input-level
full-beta-vector three-nail surface.

The projection is intentionally field-reading, not merely receipt-reading:

* the output axis is read from the trace-input beta vector;
* the alpha_s inverse residual is read from the input-produced gap;
* the Yukawa mass-order display is read from the input depth table;
* the CKM/Jarlskog sum is read from the input depth table.

Lean then proves that every accepted input projects to the canonical finite
output, and that the paired input-output bridge surface is itself a singleton.
This removes another bookkeeping split: the accepted input surface and the
finite output surface are two faces of one canonical pair.

Boundary: this remains the finite bridge theorem.  It still does not derive the
smooth Standard Model dynamics, universal one-loop QFT weights, threshold /
three-loop / Higgs corrections, full CKM matrix entries, Goldbach, RH, or the
final Euler/RH adapter range.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Field-reading input-to-output projection -/

/-- The finite output record read directly from an input-level full-beta-vector
three-nail candidate. -/
def finiteOutputOfFullBetaVectorInput
    (C : FullBetaVectorInputThreeNailCandidate) :
    SourceLawFinitePhysicalOutput where
  axis := incidenceBetaInputOneAxis C.1.betaInput
  alphaInverseResidual :=
    inverseCorrectionFromAlphaGap
      (alphaStrongTwoLoopSMOutput ℚ)
      C.1.producedGap
  yukawaMassOrder := C.2.massOrder.map (fun n : Nat => (n : ℚ))
  ckmDepthSum := (ckmJarlskogFourProductDepthSum C.2 : ℚ)

/-- THEOREM 1: accepted inputs project onto the source-law finite output
surface. -/
theorem finiteOutputOfFullBetaVectorInput_surface
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    SourceLawFinitePhysicalOutputSurface
      (finiteOutputOfFullBetaVectorInput C) := by
  have hsource :
      OneAxisFiniteSourceLaw (incidenceBetaInputOneAxis C.1.betaInput) :=
    fullBetaVectorInputThreeNailProducerSurface_to_oneAxisSourceLaw C hC
  refine ⟨hsource, ?_, ?_, ?_⟩
  · have hgap_input :
        C.1.producedGap = (89 : ℚ) / 10000 :=
      fullBetaVectorInputThreeNailProducerSurface_alphaGap C hC
    have hgap_axis :
        oneAxisAlphaStrongGap (incidenceBetaInputOneAxis C.1.betaInput) =
          (89 : ℚ) / 10000 :=
      oneAxisAlphaStrongGap_eq_89_div_10000_of_sourceLaw hsource
    simp [finiteOutputOfFullBetaVectorInput, hgap_input, hgap_axis]
  · have hmass_nat :
        C.2.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
      fullBetaVectorInputThreeNailSurfaceCertificate.yukawa_mass_order C hC
    have hmass_axis :
        rationalGridMassOrder
            (gridOfStencil
              (oneAxisYukawaRationalStencil
                (incidenceBetaInputOneAxis C.1.betaInput))) =
          [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
      oneAxisYukawaMassOrder_eq_of_sourceLaw hsource
    calc
      C.2.massOrder.map (fun n : Nat => (n : ℚ)) =
          ([50, 346, 372, 489, 583, 682, 880, 908, 982] :
            List Nat).map (fun n : Nat => (n : ℚ)) := by
            rw [hmass_nat]
      _ = ([50, 346, 372, 489, 583, 682, 880, 908, 982] : List ℚ) := by
            norm_num
      _ =
          rationalGridMassOrder
            (gridOfStencil
              (oneAxisYukawaRationalStencil
                (incidenceBetaInputOneAxis C.1.betaInput))) := hmass_axis.symm
  · have hckm_input :
        ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int) :=
      fullBetaVectorInputThreeNailSurfaceCertificate.ckm_jarlskog_sum C hC
    have hckm_axis :
        2 * oneAxisCKMSectorGap (incidenceBetaInputOneAxis C.1.betaInput) =
          (386 : ℚ) :=
      oneAxisCKMDepthSum_eq_386_of_sourceLaw hsource
    calc
      (ckmJarlskogFourProductDepthSum C.2 : ℚ) = (386 : ℚ) := by
        rw [hckm_input]
        norm_num [ckmCPDepthSum]
      _ =
          2 * oneAxisCKMSectorGap
            (incidenceBetaInputOneAxis C.1.betaInput) := hckm_axis.symm

/-- THEOREM 2: accepted inputs project to the canonical finite output. -/
theorem finiteOutputOfFullBetaVectorInput_eq_canonical
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    finiteOutputOfFullBetaVectorInput C =
      canonicalSourceLawFinitePhysicalOutput :=
  eq_canonicalSourceLawFinitePhysicalOutput_of_surface
    (finiteOutputOfFullBetaVectorInput C)
    (finiteOutputOfFullBetaVectorInput_surface C hC)

/-- THEOREM 3: the canonical input projects to the canonical finite output. -/
theorem canonicalInput_finiteOutput_eq_canonical :
    finiteOutputOfFullBetaVectorInput
        canonicalFullBetaVectorInputThreeNailCandidate =
      canonicalSourceLawFinitePhysicalOutput :=
  finiteOutputOfFullBetaVectorInput_eq_canonical
    canonicalFullBetaVectorInputThreeNailCandidate
    canonicalFullBetaVectorInputThreeNailCandidate_surface

/-! ## Paired input-output bridge surface -/

/-- The paired bridge surface: an accepted input and the finite output read from
that same input. -/
def InputOutputFiniteBridgeSurface
    (P : FullBetaVectorInputThreeNailCandidate ×
      SourceLawFinitePhysicalOutput) : Prop :=
  FullBetaVectorInputThreeNailProducerSurface P.1 ∧
    P.2 = finiteOutputOfFullBetaVectorInput P.1

/-- The canonical input-output pair. -/
def canonicalInputOutputFiniteBridgePair :
    FullBetaVectorInputThreeNailCandidate ×
      SourceLawFinitePhysicalOutput :=
  (canonicalFullBetaVectorInputThreeNailCandidate,
    canonicalSourceLawFinitePhysicalOutput)

/-- THEOREM 4: the canonical pair lies on the input-output bridge surface. -/
theorem canonicalInputOutputFiniteBridgePair_surface :
    InputOutputFiniteBridgeSurface
      canonicalInputOutputFiniteBridgePair := by
  refine ⟨canonicalFullBetaVectorInputThreeNailCandidate_surface, ?_⟩
  exact canonicalInput_finiteOutput_eq_canonical.symm

/-- THEOREM 5: every input-output bridge pair is the canonical pair. -/
theorem eq_canonicalInputOutputFiniteBridgePair_of_surface
    (P : FullBetaVectorInputThreeNailCandidate ×
      SourceLawFinitePhysicalOutput)
    (hP : InputOutputFiniteBridgeSurface P) :
    P = canonicalInputOutputFiniteBridgePair := by
  rcases P with ⟨C, O⟩
  rcases hP with ⟨hC, hO⟩
  change FullBetaVectorInputThreeNailProducerSurface C at hC
  change O = finiteOutputOfFullBetaVectorInput C at hO
  have hCcanon :
      C = canonicalFullBetaVectorInputThreeNailCandidate :=
    eq_canonicalFullBetaVectorInputThreeNailCandidate_of_surface C hC
  have hOcanon :
      O = canonicalSourceLawFinitePhysicalOutput := by
    rw [hO]
    exact finiteOutputOfFullBetaVectorInput_eq_canonical C hC
  cases hCcanon
  cases hOcanon
  rfl

/-- THEOREM 6: input-output bridge pairs are exactly the canonical pair. -/
theorem inputOutputFiniteBridgeSurface_iff_canonical
    (P : FullBetaVectorInputThreeNailCandidate ×
      SourceLawFinitePhysicalOutput) :
    InputOutputFiniteBridgeSurface P ↔
      P = canonicalInputOutputFiniteBridgePair := by
  constructor
  · exact eq_canonicalInputOutputFiniteBridgePair_of_surface P
  · intro hP
    rw [hP]
    exact canonicalInputOutputFiniteBridgePair_surface

/-- No-free predicate for finite input-output bridge pairs. -/
def NoContinuousFreeInputOutputFiniteBridgePairs
    (constraints :
      FullBetaVectorInputThreeNailCandidate ×
        SourceLawFinitePhysicalOutput -> Prop) : Prop :=
  ∀ P Q : FullBetaVectorInputThreeNailCandidate ×
      SourceLawFinitePhysicalOutput,
    constraints P -> constraints Q -> P = Q

/-- THEOREM 7: the input-output finite bridge surface is singleton/no-free. -/
theorem inputOutputFiniteBridgeSurface_noFree :
    NoContinuousFreeInputOutputFiniteBridgePairs
      InputOutputFiniteBridgeSurface := by
  intro P Q hP hQ
  rw [eq_canonicalInputOutputFiniteBridgePair_of_surface P hP,
    eq_canonicalInputOutputFiniteBridgePair_of_surface Q hQ]

/-- P680 certificate: accepted input surface and finite output surface are welded
as one canonical input-output pair. -/
structure InputOutputFiniteBridgeNoFreeCertificate where
  p679_output_no_free :
    SourceLawFinitePhysicalOutputNoFreeCertificate
  canonical_surface :
    InputOutputFiniteBridgeSurface
      canonicalInputOutputFiniteBridgePair
  surface_iff_canonical :
    ∀ P : FullBetaVectorInputThreeNailCandidate ×
      SourceLawFinitePhysicalOutput,
      InputOutputFiniteBridgeSurface P ↔
        P = canonicalInputOutputFiniteBridgePair
  no_free :
    NoContinuousFreeInputOutputFiniteBridgePairs
      InputOutputFiniteBridgeSurface
  input_to_output_surface :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        SourceLawFinitePhysicalOutputSurface
          (finiteOutputOfFullBetaVectorInput C)
  input_to_canonical_output :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        finiteOutputOfFullBetaVectorInput C =
          canonicalSourceLawFinitePhysicalOutput

/-- DEFINITION 1: canonical input-output bridge no-free certificate. -/
def inputOutputFiniteBridgeNoFreeCertificate :
    InputOutputFiniteBridgeNoFreeCertificate where
  p679_output_no_free := sourceLawFinitePhysicalOutputNoFreeCertificate
  canonical_surface := canonicalInputOutputFiniteBridgePair_surface
  surface_iff_canonical := inputOutputFiniteBridgeSurface_iff_canonical
  no_free := inputOutputFiniteBridgeSurface_noFree
  input_to_output_surface := finiteOutputOfFullBetaVectorInput_surface
  input_to_canonical_output := finiteOutputOfFullBetaVectorInput_eq_canonical

end StandardModelConstraint

namespace GrandUnification

open AffineRelaxation
open StandardModelConstraint

universe u

/-! ## Grand root -/

/-- P680 grand root: the P679 no-free output root plus the singleton/no-free
input-output bridge surface. -/
structure InputOutputBridgeUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p679_root :
    SourceLawNoFreeUnifiedRootCertificate E
  input_output_bridge :
    InputOutputFiniteBridgeNoFreeCertificate
  bridge_surface_iff_canonical :
    ∀ P : FullBetaVectorInputThreeNailCandidate ×
      SourceLawFinitePhysicalOutput,
      InputOutputFiniteBridgeSurface P ↔
        P = canonicalInputOutputFiniteBridgePair
  no_continuous_free_bridge_pairs :
    NoContinuousFreeInputOutputFiniteBridgePairs
      InputOutputFiniteBridgeSurface
  input_to_canonical_output :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        finiteOutputOfFullBetaVectorInput C =
          canonicalSourceLawFinitePhysicalOutput

/-- THEOREM 8: the input-output bridge unified root is inhabited. -/
def inputOutputBridgeUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    InputOutputBridgeUnifiedRootCertificate E where
  p679_root := sourceLawNoFreeUnifiedRootCertificate (E := E)
  input_output_bridge := inputOutputFiniteBridgeNoFreeCertificate
  bridge_surface_iff_canonical :=
    inputOutputFiniteBridgeSurface_iff_canonical
  no_continuous_free_bridge_pairs :=
    inputOutputFiniteBridgeSurface_noFree
  input_to_canonical_output :=
    finiteOutputOfFullBetaVectorInput_eq_canonical

end GrandUnification
end SaturationMonoid
