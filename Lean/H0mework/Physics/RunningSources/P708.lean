import H0mework.Physics.JointSources.P707
import H0mework.Physics.AlphaSources.P677

/-!
# Proposition 708: coordinate-spine energy package with alpha_s active source

P707 puts the P662/P698 Hamiltonian/SAT same-carrier energy package on the
P475/P476 running-σ coordinate-action spine.  P677 separately proves that the
current finite `alpha_s` residual producer has a unique active source:
`su7Breaking`, carrying the whole alpha-level residual.

This file welds those two roots.  The canonical finite output used by the
Hamiltonian/SAT coordinate-spine package has the same inverse residual as the
QCD/Poincare unified-axis residual producer, and that producer has the
SU(7)-breaking singleton active-source normal form.  So, at the certified
finite layer, the same carrier now exposes:

* Hamiltonian energy and SAT Lyapunov energy on one residual-square producer;
* the Energy/Information/Mathematics/Physics diagonal;
* the running-σ inverse-coordinate action;
* the finite `alpha_s` producer-debt closure with unique active source
  `su7Breaking`;
* the Yukawa depth list and CKM/Jarlskog depth sum inherited from P706/P707.

Boundary: this is still the finite source-law / active-source carrier.  It
does not derive smooth SU(7) threshold dynamics, universal QFT loop weights,
three-loop RG, Higgs spectra, arbitrary physical Hamiltonians, Goldbach/RH,
polynomial SAT, or `P = NP`.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open ComplexityProjection
open StandardModelConstraint

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## Alpha active source attached to the P707 finite output -/

/-- THEOREM 1: the QCD/Poincare unified-axis alpha producer lies on the
finite SU(7)-breaking source surface. -/
theorem alphaStrongQCDPoincareUnifiedAxis_sourceSurface :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer := by
  rw [alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_eq_canonical]
  exact alphaStrongSU7BreakingResidualGapProducer_sourceSurface

/-- THEOREM 2: the unified-axis producer has active-source predicate exactly
`s = su7Breaking`. -/
theorem alphaStrongQCDPoincareUnifiedAxis_activeSource_iff_su7Breaking
    (s : AlphaStrongResidualSource) :
    AlphaStrongActiveResidualSource
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
      s = .su7Breaking :=
  alphaStrong_sourceSurface_activeSource_iff_su7Breaking
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
    alphaStrongQCDPoincareUnifiedAxis_sourceSurface
    s

/-- THEOREM 3: the unified-axis producer has a unique active source. -/
theorem alphaStrongQCDPoincareUnifiedAxis_uniqueActiveSource :
    ∃! s : AlphaStrongResidualSource,
      AlphaStrongActiveResidualSource
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s :=
  alphaStrong_sourceSurface_existsUnique_activeSource
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
    alphaStrongQCDPoincareUnifiedAxis_sourceSurface

/-- THEOREM 4: the canonical P707 finite-output alpha coordinate is exactly
the inverse-coordinate image of the unified-axis producer's active-source
residual. -/
theorem canonicalCoordinateSpineOutput_alpha_eq_unifiedAxisResidual :
    canonicalSourceLawFinitePhysicalOutput.alphaInverseResidual =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap := by
  rw [alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection]
  rfl

/-- THEOREM 5: the canonical P706/P707 package's finite-output alpha
coordinate is the same unified-axis active-source residual. -/
theorem canonicalHamiltonianSATPhysicalProducerPair_alpha_eq_unifiedAxisResidual
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    (canonicalHamiltonianSATPhysicalProducerPair Clause Var).2.2.alphaInverseResidual =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap := by
  exact canonicalCoordinateSpineOutput_alpha_eq_unifiedAxisResidual

/-! ## The P707 package plus P677 active-source normal form -/

/-- The accepted coordinate-spine package strengthened by requiring the
finite alpha producer to be on the SU(7)-breaking active-source surface. -/
def HamiltonianSATCoordinateSpineActiveSourceSurface
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var) : Prop :=
  HamiltonianSATCoordinateSpinePhysicalProducerSurface R X ∧
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer ∧
    X.2.2.alphaInverseResidual =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap

/-- THEOREM 6: adding the active-source obligation still leaves exactly the
canonical P707 package. -/
theorem hamiltonianSATCoordinateSpineActiveSourceSurface_iff_canonical
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var) :
    HamiltonianSATCoordinateSpineActiveSourceSurface R X ↔
      X = canonicalHamiltonianSATPhysicalProducerPair Clause Var := by
  constructor
  · intro hX
    exact
      (hamiltonianSATCoordinateSpinePhysicalProducerSurface_iff_canonical
        R X).1 hX.1
  · intro hX
    rw [hX]
    refine ⟨?_, ?_, ?_⟩
    · exact
        (hamiltonianSATCoordinateSpinePhysicalProducerSurface_iff_canonical
          R (canonicalHamiltonianSATPhysicalProducerPair Clause Var)).2 rfl
    · exact alphaStrongQCDPoincareUnifiedAxis_sourceSurface
    · exact
        canonicalHamiltonianSATPhysicalProducerPair_alpha_eq_unifiedAxisResidual
          Clause Var

/-- The subtype of P707 packages whose alpha residual producer is also on the
SU(7)-breaking active-source surface. -/
def HamiltonianSATCoordinateSpineActiveSourceSubtype
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    Type (max v w) :=
  { X : HamiltonianSATPhysicalProducerPair Clause Var //
    HamiltonianSATCoordinateSpineActiveSourceSurface R X }

/-- The canonical accepted coordinate-spine / active-source package. -/
def canonicalHamiltonianSATCoordinateSpineActiveSourceSubtype
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    HamiltonianSATCoordinateSpineActiveSourceSubtype Clause Var R :=
  ⟨canonicalHamiltonianSATPhysicalProducerPair Clause Var,
    (hamiltonianSATCoordinateSpineActiveSourceSurface_iff_canonical
      R (canonicalHamiltonianSATPhysicalProducerPair Clause Var)).2 rfl⟩

/-- THEOREM 7: every accepted coordinate-spine / active-source package is
canonical. -/
theorem hamiltonianSATCoordinateSpineActiveSourceSubtype_eq_canonical
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATCoordinateSpineActiveSourceSubtype Clause Var R) :
    X =
      canonicalHamiltonianSATCoordinateSpineActiveSourceSubtype
        Clause Var R := by
  cases X with
  | mk X hX =>
      apply Subtype.ext
      exact
        (hamiltonianSATCoordinateSpineActiveSourceSurface_iff_canonical
          R X).1 hX

/-- THEOREM 8: the coordinate-spine / active-source package subtype is a unit
object. -/
def hamiltonianSATCoordinateSpineActiveSourceSubtypeEquivUnit
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    HamiltonianSATCoordinateSpineActiveSourceSubtype Clause Var R ≃ Unit where
  toFun _ := ()
  invFun _ :=
    canonicalHamiltonianSATCoordinateSpineActiveSourceSubtype Clause Var R
  left_inv := by
    intro X
    exact
      (hamiltonianSATCoordinateSpineActiveSourceSubtype_eq_canonical
        R X).symm
  right_inv := by
    intro x
    cases x
    rfl

/-! ## Packaged root certificate -/

/-- P708 root: P707's coordinate-spine Hamiltonian/SAT producer package with
P677's finite alpha_s active-source normal form attached to the same finite
output coordinate. -/
structure HamiltonianSATCoordinateSpineActiveSourceUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause] where
  p707_root :
    HamiltonianSATCoordinateSpinePhysicalProducerUnifiedRootCertificate.{u, v, w, z}
      E Clause Var
  p677_active_source_root :
    AlphaStrongActiveSourceUnifiedRootCertificate E
  finite_debt_closure :
    AlphaStrongFiniteProducerDebtClosureCertificate
  unified_axis_source_surface :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
  active_source_iff_su7 :
    ∀ s : AlphaStrongResidualSource,
      AlphaStrongActiveResidualSource
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
        s = .su7Breaking
  unique_active_source :
    ∃! s : AlphaStrongResidualSource,
      AlphaStrongActiveResidualSource
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s
  canonical_output_alpha_eq_unified_axis :
    canonicalSourceLawFinitePhysicalOutput.alphaInverseResidual =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap
  package_surface_iff_canonical :
    ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
      HamiltonianSATCoordinateSpineActiveSourceSurface.{u, v, w, z}
        p707_root.p706_root.p705_full_diagonal_root.p703_grand_root X ↔
        X = canonicalHamiltonianSATPhysicalProducerPair Clause Var
  package_subtype_equiv_unit :
    HamiltonianSATCoordinateSpineActiveSourceSubtype.{u, v, w, z}
      Clause Var p707_root.p706_root.p705_full_diagonal_root.p703_grand_root ≃
        Unit

/-- THEOREM 9: the P708 coordinate-spine / active-source unified root is
inhabited. -/
def hamiltonianSATCoordinateSpineActiveSourceUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause] :
    HamiltonianSATCoordinateSpineActiveSourceUnifiedRootCertificate
      E Clause Var where
  p707_root :=
    hamiltonianSATCoordinateSpinePhysicalProducerUnifiedRootCertificate.{u, v, w, z}
      (E := E) Clause Var
  p677_active_source_root :=
    alphaStrongActiveSourceUnifiedRootCertificate (E := E)
  finite_debt_closure :=
    alphaStrongFiniteProducerDebtClosureCertificate
  unified_axis_source_surface :=
    alphaStrongQCDPoincareUnifiedAxis_sourceSurface
  active_source_iff_su7 :=
    alphaStrongQCDPoincareUnifiedAxis_activeSource_iff_su7Breaking
  unique_active_source :=
    alphaStrongQCDPoincareUnifiedAxis_uniqueActiveSource
  canonical_output_alpha_eq_unified_axis :=
    canonicalCoordinateSpineOutput_alpha_eq_unifiedAxisResidual
  package_surface_iff_canonical := by
    intro X
    exact
      hamiltonianSATCoordinateSpineActiveSourceSurface_iff_canonical
        ((hamiltonianSATCoordinateSpinePhysicalProducerUnifiedRootCertificate.{u, v, w, z}
          (E := E) Clause Var).p706_root.p705_full_diagonal_root.p703_grand_root)
        X
  package_subtype_equiv_unit :=
    hamiltonianSATCoordinateSpineActiveSourceSubtypeEquivUnit Clause Var
      ((hamiltonianSATCoordinateSpinePhysicalProducerUnifiedRootCertificate.{u, v, w, z}
        (E := E) Clause Var).p706_root.p705_full_diagonal_root.p703_grand_root)

end GrandUnification
end SaturationMonoid
