import H0mework.Physics.AlphaSources.P782

/-!
# Proposition 783: no-free alpha_s residual source normal form

P607 proves that the finite alpha residual source surface is a singleton.
P782 proves that the structural QCD/Poincare producer is object-equal to the
current unified-axis producer.

This file fuses those two statements into the stronger producer theorem needed
for the numerical chain: on the accepted finite source surface there is no
independent threshold / three-loop-RG / Higgs-extra freedom.  Every accepted
alpha producer is the structural QCD/Poincare producer; the only active source
is SU(7) breaking; the alpha-level gap is the structural formula; and inverse
transport gives `-89000/128511`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

/-! ## Any accepted alpha producer is the structural producer -/

/-- THEOREM 1: every finite-source-surface alpha producer is exactly the
structural QCD/Poincare producer. -/
theorem alphaStrong_sourceSurface_eq_structuralProducer
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P =
      alphaStrongQCDPoincareResidualGapProducer
        unifiedGaugeIntoAlphaEMStructural := by
  calc
    P = alphaStrongQCDPoincareUnifiedAxisResidualGapProducer := by
      rw [eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface P hP]
      exact alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_eq_canonical.symm
    _ = alphaStrongQCDPoincareResidualGapProducer
        unifiedGaugeIntoAlphaEMStructural := by
      exact alphaStrongQCDPoincareStructuralProducer_eq_unifiedAxis.symm

/-- THEOREM 2: the structural producer is the unique inhabitant of the finite
source surface. -/
theorem alphaStrong_sourceSurface_iff_eq_structuralProducer
    (P : AlphaStrongResidualGapProducer) :
    AlphaStrongResidualProducerFiniteSourceSurface P ↔
      P =
        alphaStrongQCDPoincareResidualGapProducer
          unifiedGaugeIntoAlphaEMStructural := by
  constructor
  · intro hP
    exact alphaStrong_sourceSurface_eq_structuralProducer P hP
  · intro hP
    rw [hP]
    exact alphaStrongQCDPoincareStructuralProducer_sourceSurface

/-! ## No-free decomposition: non-SU7 branches vanish -/

/-- THEOREM 3: any accepted alpha producer has the pointwise structural
component normal form. -/
theorem alphaStrong_sourceSurface_componentNormalForm
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    AlphaStrongSU7ComponentNormalForm P.contribution :=
  (alphaStrongResidualProducerFiniteSourceSurface_iff_componentNormalForm P).mp hP

/-- THEOREM 4: threshold, three-loop-RG, and Higgs-extra branches have zero
contribution on every accepted alpha producer. -/
theorem alphaStrong_sourceSurface_nonStructuralBranches_zero
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.contribution .threshold = 0 ∧
      P.contribution .threeLoopRG = 0 ∧
        P.contribution .higgsExtraRepresentation = 0 := by
  have hnormal := alphaStrong_sourceSurface_componentNormalForm P hP
  exact
    ⟨hnormal .threshold, hnormal .threeLoopRG,
      hnormal .higgsExtraRepresentation⟩

/-- THEOREM 5: active support on every accepted alpha producer is the singleton
`su7Breaking`. -/
theorem alphaStrong_sourceSurface_activeSupport_iff_structuralSU7
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P)
    (s : AlphaStrongResidualSource) :
    AlphaStrongResidualActiveSourceSupport P.contribution s ↔
      s = .su7Breaking :=
  alphaStrongResidualProducer_sourceSurface_activeSupport_iff P hP s

/-- THEOREM 6: positive support on every accepted alpha producer is also the
singleton `su7Breaking`. -/
theorem alphaStrong_sourceSurface_positiveSupport_iff_structuralSU7
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P)
    (s : AlphaStrongResidualSource) :
    AlphaStrongResidualPositiveSourceSupport P.contribution s ↔
      s = .su7Breaking :=
  alphaStrongResidualProducer_sourceSurface_positiveSupport_iff P hP s

/-! ## Structural readout of the gap and inverse residual -/

/-- THEOREM 7: every accepted alpha producer's produced gap is the structural
QCD/Poincare formula. -/
theorem alphaStrong_sourceSurface_producedGap_eq_structuralFormula
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.producedGap =
      (alphaStrongQCDPoincareStructuralAlphaEMDenominator -
          su7GaugeFreedomDimension ℚ) /
        (alphaStrongQCDPoincareResolutionAxis ^
          alphaStrongResidualResolutionExponent) := by
  rw [alphaStrong_sourceSurface_eq_structuralProducer P hP]
  rw [alphaStrongQCDPoincareStructuralProducer_eq_unifiedAxis]
  exact alphaStrongUnifiedAxis_producedGap_eq_structuralFormula

/-- THEOREM 8: every accepted alpha producer transports to the exact inverse
residual `-89000/128511`. -/
theorem alphaStrong_sourceSurface_structuralFormula_inverseResidual
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        P.producedGap =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrong_sourceSurface_producedGap_eq_structuralFormula P hP]
  exact alphaStrongStructuralAxisFormula_inverseResidual

/-! ## Bundled no-free producer certificate -/

/-- One certificate saying the accepted finite alpha source surface has no
remaining finite producer freedom: every accepted object is the structural
QCD/Poincare producer, with zero non-SU7 branches and the fixed inverse
residual. -/
structure AlphaStrongNoFreeStructuralSourceCertificate : Prop where
  structural_normal_form :
    AlphaStrongStructuralProducerNormalFormCertificate
  source_surface_iff_structural :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ↔
        P =
          alphaStrongQCDPoincareResidualGapProducer
            unifiedGaugeIntoAlphaEMStructural
  component_normal_form :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        AlphaStrongSU7ComponentNormalForm P.contribution
  non_structural_branches_zero :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P.contribution .threshold = 0 ∧
          P.contribution .threeLoopRG = 0 ∧
            P.contribution .higgsExtraRepresentation = 0
  active_support :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        ∀ s : AlphaStrongResidualSource,
          AlphaStrongResidualActiveSourceSupport P.contribution s ↔
            s = .su7Breaking
  positive_support :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        ∀ s : AlphaStrongResidualSource,
          AlphaStrongResidualPositiveSourceSupport P.contribution s ↔
            s = .su7Breaking
  produced_gap_structural :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P.producedGap =
          (alphaStrongQCDPoincareStructuralAlphaEMDenominator -
              su7GaugeFreedomDimension ℚ) /
            (alphaStrongQCDPoincareResolutionAxis ^
              alphaStrongResidualResolutionExponent)
  inverse_residual :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            P.producedGap =
          -((89000 : ℚ) / 128511)

/-- THEOREM 9: no-free structural source certificate for the alpha leg. -/
theorem alphaStrongNoFreeStructuralSourceCertificate :
    AlphaStrongNoFreeStructuralSourceCertificate where
  structural_normal_form :=
    alphaStrongStructuralProducerNormalFormCertificate
  source_surface_iff_structural :=
    alphaStrong_sourceSurface_iff_eq_structuralProducer
  component_normal_form :=
    alphaStrong_sourceSurface_componentNormalForm
  non_structural_branches_zero :=
    alphaStrong_sourceSurface_nonStructuralBranches_zero
  active_support :=
    alphaStrong_sourceSurface_activeSupport_iff_structuralSU7
  positive_support :=
    alphaStrong_sourceSurface_positiveSupport_iff_structuralSU7
  produced_gap_structural :=
    alphaStrong_sourceSurface_producedGap_eq_structuralFormula
  inverse_residual :=
    alphaStrong_sourceSurface_structuralFormula_inverseResidual

end StandardModelConstraint
end SaturationMonoid
