import H0mework.Realization.FibreLinear.P555

/-!
# Proposition 556: sigma-zero fibers preserve completeness

P555 pulled module, normed-space, and inner-product structure back along the
zero-fiber forgetful map.  This file closes the strict Hilbert-space boundary:
if the carrier is complete, then the sigma-zero fiber is complete as well.

The proof is intentionally short.  Completeness is transported by the same
isometry already proved in P554/P555, so a Hilbert carrier remains a Hilbert
carrier at the sigma-zero fiber.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Generic completeness transfer -/

theorem sigmaZeroRelaxedMetricCompleteSpaceInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [MetricSpace X] [CompleteSpace X] : by
      letI := sigmaZeroRelaxedMetricSpaceInst K X H
      exact CompleteSpace (SigmaRelaxedObject K X H (0 : K)) := by
  letI := sigmaZeroRelaxedMetricSpaceInst K X H
  exact (sigmaZeroRelaxedIsometryEquiv K X H).completeSpace_iff.mpr inferInstance

/-- THEOREM 1: a complete normed carrier has a complete sigma-zero fiber. -/
theorem sigmaZeroRelaxedNormedCompleteSpaceInst
    (K : Type u) [Zero K] (𝕜 : Type*) [NormedField 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] : by
      letI := sigmaZeroRelaxedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
      exact CompleteSpace (SigmaRelaxedObject K X H (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
  exact
    (sigmaZeroRelaxedLinearIsometryEquiv K 𝕜 X H).toIsometryEquiv.completeSpace_iff.mpr
      inferInstance

/-- Compact generic certificate: a Hilbert-valued carrier remains Hilbert at
the sigma-zero fiber. -/
structure SigmaZeroRelaxedHilbertCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [RCLike 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X] where
  linear_geometry :
    SigmaZeroRelaxedLinearGeometryCertificate K 𝕜 X H
  complete_space_inst :
    letI := linear_geometry.add_comm_group_inst
    letI := linear_geometry.module_inst
    letI := linear_geometry.normed_group_inst
    letI := linear_geometry.normed_space_inst
    CompleteSpace (SigmaRelaxedObject K X H (0 : K))
  linear_isometry_equiv :
    letI := linear_geometry.add_comm_group_inst
    letI := linear_geometry.module_inst
    letI := linear_geometry.normed_group_inst
    letI := linear_geometry.normed_space_inst
    SigmaRelaxedObject K X H (0 : K) ≃ₗᵢ[𝕜] X

/-- THEOREM 2: the generic Hilbert certificate is inhabited. -/
def sigmaZeroRelaxedHilbertCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [RCLike 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X] :
    SigmaZeroRelaxedHilbertCertificate K 𝕜 X H where
  linear_geometry := sigmaZeroRelaxedLinearGeometryCertificate K 𝕜 X H
  complete_space_inst := by
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
    exact sigmaZeroRelaxedNormedCompleteSpaceInst K 𝕜 X H
  linear_isometry_equiv := by
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
    exact sigmaZeroRelaxedLinearIsometryEquiv K 𝕜 X H

end AffineRelaxation

open AffineRelaxation

/-! ## Core-object completeness table -/

theorem coreObjectSigmaZeroCompleteSpaceInst
    (O : CoreMathematicalObject18)
    [MetricSpace (CoreObjectCarrier O)]
    [CompleteSpace (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroMetricSpaceInst O
      exact CompleteSpace (CoreObjectSigmaZeroFiber O) := by
  letI := coreObjectSigmaZeroMetricSpaceInst O
  exact sigmaZeroRelaxedMetricCompleteSpaceInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

theorem coreObjectSigmaZeroNormedCompleteSpaceInst
    (𝕜 : Type*) [NormedField 𝕜]
    (O : CoreMathematicalObject18)
    [NormedAddCommGroup (CoreObjectCarrier O)]
    [NormedSpace 𝕜 (CoreObjectCarrier O)]
    [CompleteSpace (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroAddCommGroupInst O
      letI := coreObjectSigmaZeroModuleInst 𝕜 O
      letI := coreObjectSigmaZeroNormedAddCommGroupInst O
      letI := coreObjectSigmaZeroNormedSpaceInst 𝕜 O
      exact CompleteSpace (CoreObjectSigmaZeroFiber O) := by
  letI := coreObjectSigmaZeroAddCommGroupInst O
  letI := coreObjectSigmaZeroModuleInst 𝕜 O
  letI := coreObjectSigmaZeroNormedAddCommGroupInst O
  letI := coreObjectSigmaZeroNormedSpaceInst 𝕜 O
  exact sigmaZeroRelaxedNormedCompleteSpaceInst
    ℝ 𝕜 (CoreObjectCarrier O) CoreObjectHeadroom

/-- Table certificate: every Hilbert-valued core carrier has a complete
linear-geometric sigma-zero fiber. -/
structure CoreObjectSigmaZeroHilbertTableCertificate
    (𝕜 : Type*) [RCLike 𝕜] where
  linear_geometry_table :
    CoreObjectSigmaZeroLinearGeometryTableCertificate 𝕜
  complete_space_inst :
    ∀ (O : CoreMathematicalObject18)
      [NormedAddCommGroup (CoreObjectCarrier O)]
      [NormedSpace 𝕜 (CoreObjectCarrier O)]
      [CompleteSpace (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroAddCommGroupInst O
      letI := coreObjectSigmaZeroModuleInst 𝕜 O
      letI := coreObjectSigmaZeroNormedAddCommGroupInst O
      letI := coreObjectSigmaZeroNormedSpaceInst 𝕜 O
      CompleteSpace (CoreObjectSigmaZeroFiber O)
  hilbert_certificate :
    ∀ (O : CoreMathematicalObject18)
      [NormedAddCommGroup (CoreObjectCarrier O)]
      [InnerProductSpace 𝕜 (CoreObjectCarrier O)]
      [CompleteSpace (CoreObjectCarrier O)],
      SigmaZeroRelaxedHilbertCertificate
        ℝ 𝕜 (CoreObjectCarrier O) CoreObjectHeadroom

/-- THEOREM 3: the core-object Hilbert table is inhabited. -/
def coreObjectSigmaZeroHilbertTableCertificate
    (𝕜 : Type*) [RCLike 𝕜] :
    CoreObjectSigmaZeroHilbertTableCertificate 𝕜 where
  linear_geometry_table := coreObjectSigmaZeroLinearGeometryTableCertificate 𝕜
  complete_space_inst := by
    intro O _normed _space _complete
    exact coreObjectSigmaZeroNormedCompleteSpaceInst 𝕜 O
  hilbert_certificate := by
    intro O _normed _inner _complete
    exact sigmaZeroRelaxedHilbertCertificate
      ℝ 𝕜 (CoreObjectCarrier O) CoreObjectHeadroom

end SaturationMonoid
