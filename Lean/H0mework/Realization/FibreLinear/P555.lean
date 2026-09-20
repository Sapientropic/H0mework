import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Algebra.Module.TransferInstance
import H0mework.Realization.Fibres.P554

/-!
# Proposition 555: sigma-zero fibers preserve linear and inner-product geometry

P551--P554 showed that the sigma-zero fiber preserves algebra, topology, and
metric structure.  This file pushes the same zero-fiber theorem through the
linear-geometric layer:

* module structure is transported across the forgetful equivalence;
* the forgetful map is a `LinearEquiv`;
* normed additive and normed-space structure are induced by the same map;
* inner products are pulled back exactly;
* the forgetful map is a `LinearIsometryEquiv`.

This is the Hilbert-form face of the sigma-relaxation thesis: a linear or
inner-product carrier is not an external add-on to the saturation construction;
at `σ = 0` it is the standard projection of the relaxed fiber.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Generic module and linear-equivalence transfer -/

@[reducible] def sigmaZeroRelaxedModuleInst
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X] : by
      letI := sigmaZeroRelaxedAddCommMonoidInst K X H
      exact Module 𝕜 (SigmaRelaxedObject K X H (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X H
  exact AddEquiv.module 𝕜 (sigmaZeroRelaxedAddMonoidAddEquiv K X H)

/-- THEOREM 1: a module-valued zero fiber is linearly equivalent to its
standard carrier. -/
def sigmaZeroRelaxedLinearEquiv
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X] : by
      letI := sigmaZeroRelaxedAddCommMonoidInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      exact SigmaRelaxedObject K X H (0 : K) ≃ₗ[𝕜] X := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  exact AddEquiv.linearEquiv 𝕜 (sigmaZeroRelaxedAddMonoidAddEquiv K X H)

@[simp] theorem sigmaZeroRelaxedLinearEquiv_apply
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    sigmaZeroRelaxedLinearEquiv K 𝕜 X H z =
      sigmaZeroForget (K := K) (X := X) (H := H) z :=
  rfl

@[simp] theorem sigmaZeroRelaxedLinearEquiv_map_smul
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X]
    (a : 𝕜) (z : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    sigmaZeroRelaxedLinearEquiv K 𝕜 X H (a • z) =
      a • sigmaZeroRelaxedLinearEquiv K 𝕜 X H z := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  exact map_smul (sigmaZeroRelaxedLinearEquiv K 𝕜 X H) a z

/-! ## Generic normed and inner-product transfer -/

@[reducible] def sigmaZeroRelaxedNormedAddCommGroupInst
    (K : Type u) [Zero K]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] : by
      letI := sigmaZeroRelaxedAddCommGroupInst K X H
      exact NormedAddCommGroup (SigmaRelaxedObject K X H (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X H
  exact NormedAddCommGroup.induced
    (SigmaRelaxedObject K X H (0 : K)) X
    (sigmaZeroRelaxedAddGroupAddEquiv K X H)
    (sigmaZeroRelaxedAddGroupAddEquiv K X H).injective

/-- THEOREM 2: the zero-fiber norm is exactly carrier norm after forgetting
headroom. -/
@[simp] theorem sigmaZeroRelaxed_norm_eq
    (K : Type u) [Zero K]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
    ‖z‖ = ‖sigmaZeroForget (K := K) (X := X) (H := H) z‖ :=
  rfl

@[reducible] def sigmaZeroRelaxedNormedSpaceInst
    (K : Type u) [Zero K] (𝕜 : Type*) [NormedField 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : by
      letI := sigmaZeroRelaxedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
      exact NormedSpace 𝕜 (SigmaRelaxedObject K X H (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
  constructor
  intro a z
  change
    ‖(sigmaZeroRelaxedLinearEquiv K 𝕜 X H) (a • z)‖ ≤
      ‖a‖ * ‖(sigmaZeroRelaxedLinearEquiv K 𝕜 X H) z‖
  rw [map_smul]
  exact norm_smul_le a ((sigmaZeroRelaxedLinearEquiv K 𝕜 X H) z)

/-- THEOREM 3: the zero-fiber forgetful map is a linear isometry. -/
def sigmaZeroRelaxedLinearIsometryEquiv
    (K : Type u) [Zero K] (𝕜 : Type*) [NormedField 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : by
      letI := sigmaZeroRelaxedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
      exact SigmaRelaxedObject K X H (0 : K) ≃ₗᵢ[𝕜] X := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
  exact
    { toLinearEquiv := sigmaZeroRelaxedLinearEquiv K 𝕜 X H
      norm_map' := by
        intro z
        rfl }

@[simp] theorem sigmaZeroRelaxedLinearIsometryEquiv_apply
    (K : Type u) [Zero K] (𝕜 : Type*) [NormedField 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
    sigmaZeroRelaxedLinearIsometryEquiv K 𝕜 X H z =
      sigmaZeroForget (K := K) (X := X) (H := H) z :=
  rfl

@[reducible] def sigmaZeroRelaxedInnerProductSpaceInst
    (K : Type u) [Zero K] (𝕜 : Type*) [RCLike 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] : by
      letI := sigmaZeroRelaxedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
      exact InnerProductSpace 𝕜 (SigmaRelaxedObject K X H (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
  exact InnerProductSpace.induced
    (((sigmaZeroRelaxedLinearEquiv K 𝕜 X H).toLinearMap) :
      SigmaRelaxedObject K X H (0 : K) →ₗ[𝕜] X)

/-- THEOREM 4: the zero-fiber inner product is exactly carrier inner product
after forgetting headroom. -/
@[simp] theorem sigmaZeroRelaxed_inner_eq
    (K : Type u) [Zero K] (𝕜 : Type*) [RCLike 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    (z₁ z₂ : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedInnerProductSpaceInst K 𝕜 X H
    inner 𝕜 z₁ z₂ =
      inner 𝕜
        (sigmaZeroForget (K := K) (X := X) (H := H) z₁)
        (sigmaZeroForget (K := K) (X := X) (H := H) z₂) :=
  rfl

/-- Compact generic linear-geometric certificate for the sigma-zero fiber. -/
structure SigmaZeroRelaxedLinearGeometryCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [RCLike 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] where
  add_comm_group_inst :
    AddCommGroup (SigmaRelaxedObject K X H (0 : K))
  module_inst :
    letI := add_comm_group_inst
    Module 𝕜 (SigmaRelaxedObject K X H (0 : K))
  normed_group_inst :
    letI := add_comm_group_inst
    NormedAddCommGroup (SigmaRelaxedObject K X H (0 : K))
  normed_space_inst :
    letI := add_comm_group_inst
    letI := module_inst
    letI := normed_group_inst
    NormedSpace 𝕜 (SigmaRelaxedObject K X H (0 : K))
  inner_product_inst :
    letI := add_comm_group_inst
    letI := module_inst
    letI := normed_group_inst
    letI := normed_space_inst
    InnerProductSpace 𝕜 (SigmaRelaxedObject K X H (0 : K))
  linear_isometry_equiv :
    letI := add_comm_group_inst
    letI := module_inst
    letI := normed_group_inst
    letI := normed_space_inst
    SigmaRelaxedObject K X H (0 : K) ≃ₗᵢ[𝕜] X
  inner_eq :
    letI := add_comm_group_inst
    letI := module_inst
    letI := normed_group_inst
    letI := inner_product_inst
    ∀ z₁ z₂ : SigmaRelaxedObject K X H (0 : K),
      inner 𝕜 z₁ z₂ =
        inner 𝕜
          (sigmaZeroForget (K := K) (X := X) (H := H) z₁)
          (sigmaZeroForget (K := K) (X := X) (H := H) z₂)

/-- THEOREM 5: the generic linear-geometric certificate is inhabited. -/
def sigmaZeroRelaxedLinearGeometryCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [RCLike 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] :
    SigmaZeroRelaxedLinearGeometryCertificate K 𝕜 X H where
  add_comm_group_inst := sigmaZeroRelaxedAddCommGroupInst K X H
  module_inst := by
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    exact sigmaZeroRelaxedModuleInst K 𝕜 X H
  normed_group_inst := by
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    exact sigmaZeroRelaxedNormedAddCommGroupInst K X H
  normed_space_inst := by
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
    exact sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
  inner_product_inst := by
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
    exact sigmaZeroRelaxedInnerProductSpaceInst K 𝕜 X H
  linear_isometry_equiv := by
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
    exact sigmaZeroRelaxedLinearIsometryEquiv K 𝕜 X H
  inner_eq := by
    intro z₁ z₂
    rfl

end AffineRelaxation

open AffineRelaxation

/-! ## Core-object linear-geometric table -/

@[reducible] def coreObjectSigmaZeroAddCommMonoidInst
    (O : CoreMathematicalObject18) [AddCommMonoid (CoreObjectCarrier O)] :
    AddCommMonoid (CoreObjectSigmaZeroFiber O) :=
  sigmaZeroRelaxedAddCommMonoidInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[reducible] def coreObjectSigmaZeroAddCommGroupInst
    (O : CoreMathematicalObject18) [AddCommGroup (CoreObjectCarrier O)] :
    AddCommGroup (CoreObjectSigmaZeroFiber O) :=
  sigmaZeroRelaxedAddCommGroupInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[reducible] def coreObjectSigmaZeroModuleInst
    (𝕜 : Type*) [Semiring 𝕜]
    (O : CoreMathematicalObject18)
    [AddCommMonoid (CoreObjectCarrier O)]
    [Module 𝕜 (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroAddCommMonoidInst O
      exact Module 𝕜 (CoreObjectSigmaZeroFiber O) := by
  letI := coreObjectSigmaZeroAddCommMonoidInst O
  exact sigmaZeroRelaxedModuleInst
    ℝ 𝕜 (CoreObjectCarrier O) CoreObjectHeadroom

/-- THEOREM 6: every module-valued core object's zero fiber is linearly
equivalent to its carrier. -/
def coreObjectSigmaZeroLinearEquiv
    (𝕜 : Type*) [Semiring 𝕜]
    (O : CoreMathematicalObject18)
    [AddCommMonoid (CoreObjectCarrier O)]
    [Module 𝕜 (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroAddCommMonoidInst O
      letI := coreObjectSigmaZeroModuleInst 𝕜 O
      exact CoreObjectSigmaZeroFiber O ≃ₗ[𝕜] CoreObjectCarrier O := by
  letI := coreObjectSigmaZeroAddCommMonoidInst O
  letI := coreObjectSigmaZeroModuleInst 𝕜 O
  exact sigmaZeroRelaxedLinearEquiv
    ℝ 𝕜 (CoreObjectCarrier O) CoreObjectHeadroom

@[reducible] def coreObjectSigmaZeroNormedAddCommGroupInst
    (O : CoreMathematicalObject18)
    [NormedAddCommGroup (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroAddCommGroupInst O
      exact NormedAddCommGroup (CoreObjectSigmaZeroFiber O) := by
  letI := coreObjectSigmaZeroAddCommGroupInst O
  exact sigmaZeroRelaxedNormedAddCommGroupInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[reducible] def coreObjectSigmaZeroNormedSpaceInst
    (𝕜 : Type*) [NormedField 𝕜]
    (O : CoreMathematicalObject18)
    [NormedAddCommGroup (CoreObjectCarrier O)]
    [NormedSpace 𝕜 (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroAddCommGroupInst O
      letI := coreObjectSigmaZeroModuleInst 𝕜 O
      letI := coreObjectSigmaZeroNormedAddCommGroupInst O
      exact NormedSpace 𝕜 (CoreObjectSigmaZeroFiber O) := by
  letI := coreObjectSigmaZeroAddCommGroupInst O
  letI := coreObjectSigmaZeroModuleInst 𝕜 O
  letI := coreObjectSigmaZeroNormedAddCommGroupInst O
  exact sigmaZeroRelaxedNormedSpaceInst
    ℝ 𝕜 (CoreObjectCarrier O) CoreObjectHeadroom

def coreObjectSigmaZeroLinearIsometryEquiv
    (𝕜 : Type*) [NormedField 𝕜]
    (O : CoreMathematicalObject18)
    [NormedAddCommGroup (CoreObjectCarrier O)]
    [NormedSpace 𝕜 (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroAddCommGroupInst O
      letI := coreObjectSigmaZeroModuleInst 𝕜 O
      letI := coreObjectSigmaZeroNormedAddCommGroupInst O
      letI := coreObjectSigmaZeroNormedSpaceInst 𝕜 O
      exact CoreObjectSigmaZeroFiber O ≃ₗᵢ[𝕜] CoreObjectCarrier O := by
  letI := coreObjectSigmaZeroAddCommGroupInst O
  letI := coreObjectSigmaZeroModuleInst 𝕜 O
  letI := coreObjectSigmaZeroNormedAddCommGroupInst O
  letI := coreObjectSigmaZeroNormedSpaceInst 𝕜 O
  exact sigmaZeroRelaxedLinearIsometryEquiv
    ℝ 𝕜 (CoreObjectCarrier O) CoreObjectHeadroom

@[reducible] def coreObjectSigmaZeroInnerProductSpaceInst
    (𝕜 : Type*) [RCLike 𝕜]
    (O : CoreMathematicalObject18)
    [NormedAddCommGroup (CoreObjectCarrier O)]
    [InnerProductSpace 𝕜 (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroAddCommGroupInst O
      letI := coreObjectSigmaZeroModuleInst 𝕜 O
      letI := coreObjectSigmaZeroNormedAddCommGroupInst O
      letI := coreObjectSigmaZeroNormedSpaceInst 𝕜 O
      exact InnerProductSpace 𝕜 (CoreObjectSigmaZeroFiber O) := by
  letI := coreObjectSigmaZeroAddCommGroupInst O
  letI := coreObjectSigmaZeroModuleInst 𝕜 O
  letI := coreObjectSigmaZeroNormedAddCommGroupInst O
  letI := coreObjectSigmaZeroNormedSpaceInst 𝕜 O
  exact sigmaZeroRelaxedInnerProductSpaceInst
    ℝ 𝕜 (CoreObjectCarrier O) CoreObjectHeadroom

@[simp] theorem coreObjectSigmaZero_inner_eq
    (𝕜 : Type*) [RCLike 𝕜]
    (O : CoreMathematicalObject18)
    [NormedAddCommGroup (CoreObjectCarrier O)]
    [InnerProductSpace 𝕜 (CoreObjectCarrier O)]
    (z₁ z₂ : CoreObjectSigmaZeroFiber O) :
    letI := coreObjectSigmaZeroAddCommGroupInst O
    letI := coreObjectSigmaZeroModuleInst 𝕜 O
    letI := coreObjectSigmaZeroNormedAddCommGroupInst O
    letI := coreObjectSigmaZeroInnerProductSpaceInst 𝕜 O
    inner 𝕜 z₁ z₂ =
      inner 𝕜
        (coreObjectSigmaZeroForget O z₁)
        (coreObjectSigmaZeroForget O z₂) :=
  rfl

/-- Table certificate: every inner-product-valued core carrier has a
linear-geometric sigma-zero fiber. -/
structure CoreObjectSigmaZeroLinearGeometryTableCertificate
    (𝕜 : Type*) [RCLike 𝕜] where
  metric_table :
    CoreObjectSigmaZeroMetricTableCertificate
  module_inst :
    ∀ (O : CoreMathematicalObject18)
      [AddCommMonoid (CoreObjectCarrier O)]
      [Module 𝕜 (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroAddCommMonoidInst O
      Module 𝕜 (CoreObjectSigmaZeroFiber O)
  linear_equiv :
    ∀ (O : CoreMathematicalObject18)
      [AddCommMonoid (CoreObjectCarrier O)]
      [Module 𝕜 (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroAddCommMonoidInst O
      letI := coreObjectSigmaZeroModuleInst 𝕜 O
      CoreObjectSigmaZeroFiber O ≃ₗ[𝕜] CoreObjectCarrier O
  normed_inst :
    ∀ (O : CoreMathematicalObject18)
      [NormedAddCommGroup (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroAddCommGroupInst O
      NormedAddCommGroup (CoreObjectSigmaZeroFiber O)
  linear_isometry_equiv :
    ∀ (O : CoreMathematicalObject18)
      [NormedAddCommGroup (CoreObjectCarrier O)]
      [NormedSpace 𝕜 (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroAddCommGroupInst O
      letI := coreObjectSigmaZeroModuleInst 𝕜 O
      letI := coreObjectSigmaZeroNormedAddCommGroupInst O
      letI := coreObjectSigmaZeroNormedSpaceInst 𝕜 O
      CoreObjectSigmaZeroFiber O ≃ₗᵢ[𝕜] CoreObjectCarrier O
  inner_product_inst :
    ∀ (O : CoreMathematicalObject18)
      [NormedAddCommGroup (CoreObjectCarrier O)]
      [InnerProductSpace 𝕜 (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroAddCommGroupInst O
      letI := coreObjectSigmaZeroModuleInst 𝕜 O
      letI := coreObjectSigmaZeroNormedAddCommGroupInst O
      letI := coreObjectSigmaZeroNormedSpaceInst 𝕜 O
      InnerProductSpace 𝕜 (CoreObjectSigmaZeroFiber O)
  inner_eq :
    ∀ (O : CoreMathematicalObject18)
      [NormedAddCommGroup (CoreObjectCarrier O)]
      [InnerProductSpace 𝕜 (CoreObjectCarrier O)]
      (z₁ z₂ : CoreObjectSigmaZeroFiber O),
      letI := coreObjectSigmaZeroAddCommGroupInst O
      letI := coreObjectSigmaZeroModuleInst 𝕜 O
      letI := coreObjectSigmaZeroNormedAddCommGroupInst O
      letI := coreObjectSigmaZeroInnerProductSpaceInst 𝕜 O
      inner 𝕜 z₁ z₂ =
        inner 𝕜
          (coreObjectSigmaZeroForget O z₁)
          (coreObjectSigmaZeroForget O z₂)

/-- THEOREM 7: the core-object linear-geometric table is inhabited. -/
def coreObjectSigmaZeroLinearGeometryTableCertificate
    (𝕜 : Type*) [RCLike 𝕜] :
    CoreObjectSigmaZeroLinearGeometryTableCertificate 𝕜 where
  metric_table := coreObjectSigmaZeroMetricTableCertificate
  module_inst := by
    intro O _add _module
    exact coreObjectSigmaZeroModuleInst 𝕜 O
  linear_equiv := by
    intro O _add _module
    exact coreObjectSigmaZeroLinearEquiv 𝕜 O
  normed_inst := by
    intro O _normed
    exact coreObjectSigmaZeroNormedAddCommGroupInst O
  linear_isometry_equiv := by
    intro O _normed _space
    exact coreObjectSigmaZeroLinearIsometryEquiv 𝕜 O
  inner_product_inst := by
    intro O _normed _inner
    exact coreObjectSigmaZeroInnerProductSpaceInst 𝕜 O
  inner_eq := by
    intro O _normed _inner z₁ z₂
    rfl

end SaturationMonoid
