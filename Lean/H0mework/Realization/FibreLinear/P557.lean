import H0mework.Realization.Fibres.P556
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Proposition 557: sigma-zero fibers are functorial on linear operators

P555/P556 closed the object side for linear, inner-product, and Hilbert
carriers.  This file closes the operator side needed by physics-facing
applications: a linear map, continuous linear map, or endomorphism on standard
carriers has a canonical sigma-zero lift, and the lift commutes strictly with
the forgetful projection.

The key point is functoriality:

* identity maps lift to identity maps;
* composition lifts to composition;
* for continuous linear maps, the lift is continuous because the zero-fiber
  forgetful maps are linear isometries.

Thus Hamiltonians, RG linearizations, and bounded field operators can be moved
across the sigma-zero projection without adding an external adapter.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w x y z t

/-! ## Linear maps -/

/-- Lift a standard linear map to the sigma-zero fibers by conjugating through
the forgetful linear equivalences. -/
def sigmaZeroLiftLinearMap
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (f : X →ₗ[𝕜] Y) : by
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      exact
        SigmaRelaxedObject K X HX (0 : K) →ₗ[𝕜]
          SigmaRelaxedObject K Y HY (0 : K) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  exact ((sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).symm.toLinearMap).comp
    (f.comp (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).toLinearMap)

/-- THEOREM 1: lifting a linear map commutes strictly with forgetting the
headroom coordinate. -/
@[simp] theorem sigmaZeroForget_liftLinearMap
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (f : X →ₗ[𝕜] Y) (z : SigmaRelaxedObject K X HX (0 : K)) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    sigmaZeroForget (K := K) (X := Y) (H := HY)
        (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f z) =
      f (sigmaZeroForget (K := K) (X := X) (H := HX) z) :=
  rfl

/-- THEOREM 2: the sigma-zero linear lift preserves identities. -/
@[simp] theorem sigmaZeroLiftLinearMap_id
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (HX : Type x)
    [Inhabited HX] [AddCommMonoid X] [Module 𝕜 X] :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    sigmaZeroLiftLinearMap K 𝕜 X X HX HX (LinearMap.id : X →ₗ[𝕜] X) =
      LinearMap.id := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  apply LinearMap.ext
  intro z
  apply (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).injective
  rfl

/-- THEOREM 3: the sigma-zero linear lift preserves composition. -/
@[simp] theorem sigmaZeroLiftLinearMap_comp
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (Y : Type w) (Z : Type z)
    (HX : Type x) (HY : Type y) (HZ : Type t)
    [Inhabited HX] [Inhabited HY] [Inhabited HZ]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z]
    (f : X →ₗ[𝕜] Y) (g : Y →ₗ[𝕜] Z) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
    sigmaZeroLiftLinearMap K 𝕜 X Z HX HZ (g.comp f) =
      (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g).comp
        (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
  apply LinearMap.ext
  intro z
  apply (sigmaZeroRelaxedLinearEquiv K 𝕜 Z HZ).injective
  rfl

/-! ## Continuous linear maps -/

/-- Lift a bounded/continuous linear map to the sigma-zero fibers.  The
operator norm of the source map gives the continuity bound after conjugation by
linear isometries. -/
def sigmaZeroLiftContinuousLinearMap
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) : by
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
      exact
        SigmaRelaxedObject K X HX (0 : K) →L[𝕜]
          SigmaRelaxedObject K Y HY (0 : K) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  let L := sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f.toLinearMap
  exact L.mkContinuous ‖f‖ (by
    intro z
    change
      ‖f ((sigmaZeroRelaxedLinearEquiv K 𝕜 X HX) z)‖ ≤
        ‖f‖ * ‖(sigmaZeroRelaxedLinearEquiv K 𝕜 X HX) z‖
    exact f.le_opNorm ((sigmaZeroRelaxedLinearEquiv K 𝕜 X HX) z))

/-- THEOREM 4: lifting a continuous linear map commutes strictly with the
forgetful projection. -/
@[simp] theorem sigmaZeroForget_liftContinuousLinearMap
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) (z : SigmaRelaxedObject K X HX (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
    sigmaZeroForget (K := K) (X := Y) (H := HY)
        (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z) =
      f (sigmaZeroForget (K := K) (X := X) (H := HX) z) :=
  rfl

/-- THEOREM 5: the sigma-zero continuous-linear lift preserves identities. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_id
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (HX : Type x)
    [Inhabited HX] [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX
        (ContinuousLinearMap.id 𝕜 X) =
      ContinuousLinearMap.id 𝕜 (SigmaRelaxedObject K X HX (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  apply ContinuousLinearMap.ext
  intro z
  apply (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).injective
  rfl

/-- THEOREM 6: the sigma-zero continuous-linear lift preserves composition. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_comp
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (Z : Type z)
    (HX : Type x) (HY : Type y) (HZ : Type t)
    [Inhabited HX] [Inhabited HY] [Inhabited HZ]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (f : X →L[𝕜] Y) (g : Y →L[𝕜] Z) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedAddCommGroupInst K Z HZ
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K Z HZ
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Z HZ
    sigmaZeroLiftContinuousLinearMap K 𝕜 X Z HX HZ (g.comp f) =
      (sigmaZeroLiftContinuousLinearMap K 𝕜 Y Z HY HZ g).comp
        (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedAddCommGroupInst K Z HZ
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Z HZ
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Z HZ
  apply ContinuousLinearMap.ext
  intro z
  apply (sigmaZeroRelaxedLinearEquiv K 𝕜 Z HZ).injective
  rfl

/-- Compact certificate for the sigma-zero operator functor on bounded linear
maps. -/
structure SigmaZeroOperatorFunctorCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [RCLike 𝕜]
    (X : Type v) (HX : Type x)
    [Inhabited HX] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] where
  hilbert_ready :
    SigmaZeroRelaxedLinearGeometryCertificate K 𝕜 X HX
  lift_endomorphism :
    (X →L[𝕜] X) →
      letI := hilbert_ready.add_comm_group_inst
      letI := hilbert_ready.module_inst
      letI := hilbert_ready.normed_group_inst
      letI := hilbert_ready.normed_space_inst
      SigmaRelaxedObject K X HX (0 : K) →L[𝕜]
        SigmaRelaxedObject K X HX (0 : K)
  lift_id :
    letI := hilbert_ready.add_comm_group_inst
    letI := hilbert_ready.module_inst
    letI := hilbert_ready.normed_group_inst
    letI := hilbert_ready.normed_space_inst
    lift_endomorphism (ContinuousLinearMap.id 𝕜 X) =
      ContinuousLinearMap.id 𝕜 (SigmaRelaxedObject K X HX (0 : K))
  lift_comp :
    letI := hilbert_ready.add_comm_group_inst
    letI := hilbert_ready.module_inst
    letI := hilbert_ready.normed_group_inst
    letI := hilbert_ready.normed_space_inst
    ∀ f g : X →L[𝕜] X,
      lift_endomorphism (g.comp f) =
        (lift_endomorphism g).comp (lift_endomorphism f)

/-- THEOREM 7: the bounded-operator sigma-zero functor certificate is
inhabited. -/
def sigmaZeroOperatorFunctorCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [RCLike 𝕜]
    (X : Type v) (HX : Type x)
    [Inhabited HX] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] :
    SigmaZeroOperatorFunctorCertificate K 𝕜 X HX where
  hilbert_ready := sigmaZeroRelaxedLinearGeometryCertificate K 𝕜 X HX
  lift_endomorphism := by
    intro f
    exact sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX f
  lift_id := by
    exact sigmaZeroLiftContinuousLinearMap_id K 𝕜 X HX
  lift_comp := by
    intro f g
    exact sigmaZeroLiftContinuousLinearMap_comp K 𝕜 X X X HX HX HX f g

end AffineRelaxation

open AffineRelaxation

/-! ## Core-object linear-operator table -/

def coreObjectSigmaZeroLiftLinearMap
    (𝕜 : Type*) [Semiring 𝕜]
    (O₁ O₂ : CoreMathematicalObject18)
    [AddCommMonoid (CoreObjectCarrier O₁)]
    [Module 𝕜 (CoreObjectCarrier O₁)]
    [AddCommMonoid (CoreObjectCarrier O₂)]
    [Module 𝕜 (CoreObjectCarrier O₂)]
    (f : CoreObjectCarrier O₁ →ₗ[𝕜] CoreObjectCarrier O₂) : by
      letI := coreObjectSigmaZeroAddCommMonoidInst O₁
      letI := coreObjectSigmaZeroModuleInst 𝕜 O₁
      letI := coreObjectSigmaZeroAddCommMonoidInst O₂
      letI := coreObjectSigmaZeroModuleInst 𝕜 O₂
      exact CoreObjectSigmaZeroFiber O₁ →ₗ[𝕜] CoreObjectSigmaZeroFiber O₂ := by
  letI := coreObjectSigmaZeroAddCommMonoidInst O₁
  letI := coreObjectSigmaZeroModuleInst 𝕜 O₁
  letI := coreObjectSigmaZeroAddCommMonoidInst O₂
  letI := coreObjectSigmaZeroModuleInst 𝕜 O₂
  exact sigmaZeroLiftLinearMap
    ℝ 𝕜 (CoreObjectCarrier O₁) (CoreObjectCarrier O₂)
      CoreObjectHeadroom CoreObjectHeadroom f

@[simp] theorem coreObjectSigmaZeroForget_liftLinearMap
    (𝕜 : Type*) [Semiring 𝕜]
    (O₁ O₂ : CoreMathematicalObject18)
    [AddCommMonoid (CoreObjectCarrier O₁)]
    [Module 𝕜 (CoreObjectCarrier O₁)]
    [AddCommMonoid (CoreObjectCarrier O₂)]
    [Module 𝕜 (CoreObjectCarrier O₂)]
    (f : CoreObjectCarrier O₁ →ₗ[𝕜] CoreObjectCarrier O₂)
    (z : CoreObjectSigmaZeroFiber O₁) :
    letI := coreObjectSigmaZeroAddCommMonoidInst O₁
    letI := coreObjectSigmaZeroModuleInst 𝕜 O₁
    letI := coreObjectSigmaZeroAddCommMonoidInst O₂
    letI := coreObjectSigmaZeroModuleInst 𝕜 O₂
    coreObjectSigmaZeroForget O₂
        (coreObjectSigmaZeroLiftLinearMap 𝕜 O₁ O₂ f z) =
      f (coreObjectSigmaZeroForget O₁ z) :=
  rfl

end SaturationMonoid
