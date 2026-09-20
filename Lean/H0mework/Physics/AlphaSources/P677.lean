import H0mework.Physics.AlphaSources.P647
import H0mework.Arithmetic.PrimeShadow.P676

/-!
# Proposition 677: alpha_s active-source normal form

P676 packages the final Goldbach/H¹ range/injectivity side as an explicit
source object.  This file performs the analogous tightening on the alpha_s
finite residual side.

P607 already proves that the finite SU(7)-breaking source surface is a
singleton on full residual-producer objects.  P647 identifies the current
finite physical producer with that singleton.  P677 extracts the operational
normal form that matters for the physical producer debt: on the finite source
surface, the active-source predicate is exactly `s = su7Breaking`.

Thus the current finite alpha_s layer is not a four-source tuning surface.  It
has one active source, it carries the entire `89/10000` alpha-level gap, and
that gap transports to the exact inverse residual `-89000/128511`.

Boundary: this still does not compute the smooth threshold / three-loop RG /
Higgs-extra-spectrum dynamics.  It proves that any such smooth producer, once
specialized to the current finite source surface, must collapse to this unique
active-source normal form.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Active-source predicate -/

/-- A residual source is active when its alpha-level contribution is nonzero. -/
def AlphaStrongActiveResidualSource
    (P : AlphaStrongResidualGapProducer)
    (s : AlphaStrongResidualSource) : Prop :=
  P.contribution s ≠ 0

/-- THEOREM 1: the finite SU(7)-breaking alpha gap is nonzero. -/
theorem alphaStrongSU7BreakingAlphaGap_ne_zero :
    alphaStrongSU7BreakingAlphaGap ℚ ≠ 0 := by
  rw [alphaStrongSU7BreakingAlphaGap_eq_89_div_10000]
  norm_num

/-! ## Source-surface contribution normal form -/

/-- THEOREM 2: on the finite source surface, the SU(7)-breaking source carries
the finite SU(7) alpha gap. -/
theorem alphaStrong_sourceSurface_su7_contribution
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.contribution .su7Breaking = alphaStrongSU7BreakingAlphaGap ℚ :=
  hP.1

/-- THEOREM 3: on the finite source surface, the SU(7)-breaking source carries
the displayed alpha-level gap `89/10000`. -/
theorem alphaStrong_sourceSurface_su7_contribution_eq_89_div_10000
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.contribution .su7Breaking = (89 : ℚ) / 10000 := by
  rw [alphaStrong_sourceSurface_su7_contribution P hP,
    alphaStrongSU7BreakingAlphaGap_eq_89_div_10000]

/-- THEOREM 4: on the finite source surface, the three non-SU7 residual
sources carry zero contribution. -/
theorem alphaStrong_sourceSurface_non_su7_zero
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.contribution .threshold = 0 ∧
      P.contribution .threeLoopRG = 0 ∧
        P.contribution .higgsExtraRepresentation = 0 := by
  exact ⟨hP.2.1, hP.2.2.1, hP.2.2.2⟩

/-- THEOREM 5: on the finite source surface, the active-source predicate is
exactly the singleton source `.su7Breaking`. -/
theorem alphaStrong_sourceSurface_activeSource_iff_su7Breaking
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P)
    (s : AlphaStrongResidualSource) :
    AlphaStrongActiveResidualSource P s ↔ s = .su7Breaking := by
  cases s
  · constructor
    · intro _h
      rfl
    · intro _h
      rw [AlphaStrongActiveResidualSource,
        alphaStrong_sourceSurface_su7_contribution P hP]
      exact alphaStrongSU7BreakingAlphaGap_ne_zero
  · constructor
    · intro h
      have hzero : P.contribution .threshold = 0 :=
        (alphaStrong_sourceSurface_non_su7_zero P hP).1
      exact False.elim (h hzero)
    · intro h
      cases h
  · constructor
    · intro h
      have hzero : P.contribution .threeLoopRG = 0 :=
        (alphaStrong_sourceSurface_non_su7_zero P hP).2.1
      exact False.elim (h hzero)
    · intro h
      cases h
  · constructor
    · intro h
      have hzero : P.contribution .higgsExtraRepresentation = 0 :=
        (alphaStrong_sourceSurface_non_su7_zero P hP).2.2
      exact False.elim (h hzero)
    · intro h
      cases h

/-- THEOREM 6: every finite-source-surface producer has a unique active
source. -/
theorem alphaStrong_sourceSurface_existsUnique_activeSource
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    ∃! s : AlphaStrongResidualSource, AlphaStrongActiveResidualSource P s := by
  refine ⟨.su7Breaking, ?_, ?_⟩
  · exact
      (alphaStrong_sourceSurface_activeSource_iff_su7Breaking
        P hP .su7Breaking).mpr rfl
  · intro s hs
    exact
      (alphaStrong_sourceSurface_activeSource_iff_su7Breaking
        P hP s).mp hs

/-- THEOREM 7: on the finite source surface, the unique active source carries
the whole produced alpha gap. -/
theorem alphaStrong_sourceSurface_su7_contribution_eq_producedGap
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.contribution .su7Breaking = P.producedGap := by
  rw [AlphaStrongResidualGapProducer.producedGap,
    (alphaStrong_sourceSurface_non_su7_zero P hP).1,
    (alphaStrong_sourceSurface_non_su7_zero P hP).2.1,
    (alphaStrong_sourceSurface_non_su7_zero P hP).2.2]
  ring

/-! ## Packaged active-source normal form -/

/-- P677 certificate: the finite alpha_s source surface has a unique active
source and that source is exactly SU(7)-breaking. -/
structure AlphaStrongActiveSourceNormalFormCertificate where
  p607_source_surface :
    AlphaStrongResidualProducerSourceSurfaceReceipt
  gap_nonzero :
    alphaStrongSU7BreakingAlphaGap ℚ ≠ 0
  su7_source_gap :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P.contribution .su7Breaking = (89 : ℚ) / 10000
  non_su7_sources_zero :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P.contribution .threshold = 0 ∧
          P.contribution .threeLoopRG = 0 ∧
            P.contribution .higgsExtraRepresentation = 0
  active_source_iff_su7 :
    ∀ (P : AlphaStrongResidualGapProducer)
      (_hP : AlphaStrongResidualProducerFiniteSourceSurface P)
      (s : AlphaStrongResidualSource),
        AlphaStrongActiveResidualSource P s ↔ s = .su7Breaking
  unique_active_source :
    ∀ (P : AlphaStrongResidualGapProducer)
      (_hP : AlphaStrongResidualProducerFiniteSourceSurface P),
        ∃! s : AlphaStrongResidualSource,
          AlphaStrongActiveResidualSource P s
  active_source_carries_gap :
    ∀ (P : AlphaStrongResidualGapProducer)
      (_hP : AlphaStrongResidualProducerFiniteSourceSurface P),
        P.contribution .su7Breaking = P.producedGap
  inverse_residual :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            P.producedGap =
          -((89000 : ℚ) / 128511)

/-- THEOREM 8: canonical active-source normal-form certificate for the
current finite alpha_s layer. -/
theorem alphaStrongActiveSourceNormalFormCertificate :
    AlphaStrongActiveSourceNormalFormCertificate where
  p607_source_surface :=
    alphaStrongResidualProducerSourceSurfaceReceipt
  gap_nonzero :=
    alphaStrongSU7BreakingAlphaGap_ne_zero
  su7_source_gap :=
    alphaStrong_sourceSurface_su7_contribution_eq_89_div_10000
  non_su7_sources_zero :=
    alphaStrong_sourceSurface_non_su7_zero
  active_source_iff_su7 :=
    alphaStrong_sourceSurface_activeSource_iff_su7Breaking
  unique_active_source :=
    alphaStrong_sourceSurface_existsUnique_activeSource
  active_source_carries_gap :=
    alphaStrong_sourceSurface_su7_contribution_eq_producedGap
  inverse_residual :=
    alphaStrongResidualProducer_sourceSurface_inverseCorrection

end StandardModelConstraint

namespace GrandUnification

open AffineRelaxation
open StandardModelConstraint

universe u

/-- The current unified root with P676's even support-code source object and
P677's alpha_s active-source normal form welded together. -/
structure AlphaStrongActiveSourceUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p676_root :
    EvenSupportCodeSourceUnifiedRootCertificate E
  alpha_finite_closure :
    AlphaStrongFiniteProducerDebtClosureCertificate
  alpha_active_source_normal_form :
    AlphaStrongActiveSourceNormalFormCertificate
  active_source_iff_su7 :
    ∀ (P : AlphaStrongResidualGapProducer)
      (_hP : AlphaStrongResidualProducerFiniteSourceSurface P)
      (s : AlphaStrongResidualSource),
        AlphaStrongActiveResidualSource P s ↔ s = .su7Breaking
  alpha_s_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 8: the central root with alpha_s active-source normal form. -/
def alphaStrongActiveSourceUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    AlphaStrongActiveSourceUnifiedRootCertificate E where
  p676_root := evenSupportCodeSourceUnifiedRootCertificate (E := E)
  alpha_finite_closure :=
    alphaStrongFiniteProducerDebtClosureCertificate
  alpha_active_source_normal_form :=
    alphaStrongActiveSourceNormalFormCertificate
  active_source_iff_su7 :=
    alphaStrong_sourceSurface_activeSource_iff_su7Breaking
  alpha_s_residual :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection

end GrandUnification
end SaturationMonoid
