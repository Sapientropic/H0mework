import H0mework.Realization.FibreLinear.P557

/-!
# Proposition 558: sigma-zero fibers are fully faithful on linear homs

P557 proved that standard linear and bounded-linear operators have canonical
sigma-zero lifts.  This file proves the converse: every sigma-zero linear
operator descends uniquely to the standard carrier.  The lift and descend maps
are inverse equivalences on Hom types.

Thus the sigma-zero projection is not merely an object equivalence and not
merely a one-way operator adapter.  At the linear and bounded-linear levels it
is full and faithful: the operator algebra seen at the zero fiber is exactly
the standard operator algebra in transported coordinates.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w x y

/-! ## Linear hom equivalence -/

/-- Descend a sigma-zero linear map back to the standard carriers by conjugating
through the forgetful linear equivalences. -/
def sigmaZeroDescendLinearMap
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (F : by
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      exact
        SigmaRelaxedObject K X HX (0 : K) →ₗ[𝕜]
          SigmaRelaxedObject K Y HY (0 : K)) :
    X →ₗ[𝕜] Y := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  exact ((sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).toLinearMap).comp
    (F.comp (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).symm.toLinearMap)

/-- THEOREM 1: descending a lifted standard linear map returns the original
linear map. -/
@[simp] theorem sigmaZeroDescendLinearMap_lift
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (f : X →ₗ[𝕜] Y) :
    sigmaZeroDescendLinearMap K 𝕜 X Y HX HY
        (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) = f := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  apply LinearMap.ext
  intro x
  rfl

/-- THEOREM 2: lifting a descended sigma-zero linear map returns the original
sigma-zero linear map. -/
@[simp] theorem sigmaZeroLiftLinearMap_descend
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (F : by
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      exact
        SigmaRelaxedObject K X HX (0 : K) →ₗ[𝕜]
          SigmaRelaxedObject K Y HY (0 : K)) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    sigmaZeroLiftLinearMap K 𝕜 X Y HX HY
        (sigmaZeroDescendLinearMap K 𝕜 X Y HX HY F) = F := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  apply LinearMap.ext
  intro z
  apply (sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).injective
  simp [sigmaZeroLiftLinearMap, sigmaZeroDescendLinearMap]
  have hz :
      (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).symm
          (sigmaZeroForget (K := K) (X := X) (H := HX) z) = z := by
    simpa using (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).symm_apply_apply z
  rw [hz]

/-- THEOREM 3: Hom equivalence for standard linear maps and sigma-zero
linear maps. -/
def sigmaZeroLinearMapEquiv
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] :
    (X →ₗ[𝕜] Y) ≃ (by
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      exact
        SigmaRelaxedObject K X HX (0 : K) →ₗ[𝕜]
          SigmaRelaxedObject K Y HY (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  exact
    { toFun := sigmaZeroLiftLinearMap K 𝕜 X Y HX HY
      invFun := sigmaZeroDescendLinearMap K 𝕜 X Y HX HY
      left_inv := sigmaZeroDescendLinearMap_lift K 𝕜 X Y HX HY
      right_inv := sigmaZeroLiftLinearMap_descend K 𝕜 X Y HX HY }

/-! ## Continuous linear hom equivalence -/

/-- Descend a sigma-zero bounded linear map back to the standard carriers. -/
def sigmaZeroDescendContinuousLinearMap
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (F : by
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
          SigmaRelaxedObject K Y HY (0 : K)) :
    X →L[𝕜] Y := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  let L := sigmaZeroDescendLinearMap K 𝕜 X Y HX HY F.toLinearMap
  exact L.mkContinuous ‖F‖ (by
    intro x
    change
      ‖F ((sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).symm x)‖ ≤
        ‖F‖ * ‖x‖
    convert F.le_opNorm ((sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).symm x) using 2
    rfl)

/-- THEOREM 4: descending a lifted standard bounded linear map returns the
original bounded linear map. -/
@[simp] theorem sigmaZeroDescendContinuousLinearMap_lift
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) :
    sigmaZeroDescendContinuousLinearMap K 𝕜 X Y HX HY
        (sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f) = f := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- THEOREM 5: lifting a descended sigma-zero bounded linear map returns the
original sigma-zero bounded linear map. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_descend
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (F : by
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
          SigmaRelaxedObject K Y HY (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
    sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY
        (sigmaZeroDescendContinuousLinearMap K 𝕜 X Y HX HY F) = F := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  apply ContinuousLinearMap.ext
  intro z
  apply (sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).injective
  simp [sigmaZeroLiftContinuousLinearMap, sigmaZeroLiftLinearMap,
    sigmaZeroDescendContinuousLinearMap, sigmaZeroDescendLinearMap]
  have hz :
      (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).symm
          (sigmaZeroForget (K := K) (X := X) (H := HX) z) = z := by
    simpa using (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).symm_apply_apply z
  rw [hz]

/-- THEOREM 6: Hom equivalence for standard bounded linear maps and
sigma-zero bounded linear maps. -/
def sigmaZeroContinuousLinearMapEquiv
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] :
    (X →L[𝕜] Y) ≃ (by
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
          SigmaRelaxedObject K Y HY (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  exact
    { toFun := sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY
      invFun := sigmaZeroDescendContinuousLinearMap K 𝕜 X Y HX HY
      left_inv := sigmaZeroDescendContinuousLinearMap_lift K 𝕜 X Y HX HY
      right_inv := sigmaZeroLiftContinuousLinearMap_descend K 𝕜 X Y HX HY }

/-- Compact certificate: the sigma-zero operator bridge is full and faithful
on linear and bounded-linear Hom types. -/
structure SigmaZeroHomEquivalenceCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] where
  linear_hom_equiv :
    (X →ₗ[𝕜] Y) ≃ (by
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      exact
        SigmaRelaxedObject K X HX (0 : K) →ₗ[𝕜]
          SigmaRelaxedObject K Y HY (0 : K))
  continuous_linear_hom_equiv :
    (X →L[𝕜] Y) ≃ (by
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
          SigmaRelaxedObject K Y HY (0 : K))

/-- THEOREM 7: the Hom-equivalence certificate is inhabited. -/
def sigmaZeroHomEquivalenceCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] :
    SigmaZeroHomEquivalenceCertificate K 𝕜 X Y HX HY where
  linear_hom_equiv := sigmaZeroLinearMapEquiv K 𝕜 X Y HX HY
  continuous_linear_hom_equiv :=
    sigmaZeroContinuousLinearMapEquiv K 𝕜 X Y HX HY

end AffineRelaxation

open AffineRelaxation

/-! ## Core-object linear Hom equivalence -/

def coreObjectSigmaZeroLinearMapEquiv
    (𝕜 : Type*) [Semiring 𝕜]
    (O₁ O₂ : CoreMathematicalObject18)
    [AddCommMonoid (CoreObjectCarrier O₁)]
    [Module 𝕜 (CoreObjectCarrier O₁)]
    [AddCommMonoid (CoreObjectCarrier O₂)]
    [Module 𝕜 (CoreObjectCarrier O₂)] :
    (CoreObjectCarrier O₁ →ₗ[𝕜] CoreObjectCarrier O₂) ≃ (by
      letI := coreObjectSigmaZeroAddCommMonoidInst O₁
      letI := coreObjectSigmaZeroModuleInst 𝕜 O₁
      letI := coreObjectSigmaZeroAddCommMonoidInst O₂
      letI := coreObjectSigmaZeroModuleInst 𝕜 O₂
      exact CoreObjectSigmaZeroFiber O₁ →ₗ[𝕜] CoreObjectSigmaZeroFiber O₂) := by
  letI := coreObjectSigmaZeroAddCommMonoidInst O₁
  letI := coreObjectSigmaZeroModuleInst 𝕜 O₁
  letI := coreObjectSigmaZeroAddCommMonoidInst O₂
  letI := coreObjectSigmaZeroModuleInst 𝕜 O₂
  exact sigmaZeroLinearMapEquiv
    ℝ 𝕜 (CoreObjectCarrier O₁) (CoreObjectCarrier O₂)
      CoreObjectHeadroom CoreObjectHeadroom

end SaturationMonoid
