import H0mework.Realization.FibreLinear.P569

/-!
# Proposition 570: the sigma-zero Hom equivalence respects identities and composition

P557 proved that sigma-zero lifting preserves identities and composition.
P558 proved that the lifted Hom type is equivalent to the ordinary Hom type.
This file puts those two facts together: the Hom equivalence itself is
operation-preserving.

So the sigma-zero carrier is not just object-equivalent to ordinary linear
algebra, and not just Hom-equivalent.  It is fully faithful in the computational
sense that identity maps and linear pipelines are transported on the nose.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v₁ v₂ v₃ w₁ w₂ w₃

/-! ## Hom equivalence compatibility with category operations -/

/-- THEOREM 1: the sigma-zero linear Hom equivalence sends identity to
identity. -/
@[simp] theorem sigmaZeroLinearMapEquiv_apply_id
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    [AddCommMonoid X] [Module 𝕜 X] :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    sigmaZeroLinearMapEquiv K 𝕜 X X HX HX
        (LinearMap.id : X →ₗ[𝕜] X) =
      (LinearMap.id :
        SigmaRelaxedObject K X HX (0 : K) →ₗ[𝕜]
          SigmaRelaxedObject K X HX (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  exact sigmaZeroLiftLinearMap_id K 𝕜 X HX

/-- THEOREM 2: the sigma-zero linear Hom equivalence sends composition to
composition. -/
@[simp] theorem sigmaZeroLinearMapEquiv_apply_comp
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
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
    sigmaZeroLinearMapEquiv K 𝕜 X Z HX HZ (g.comp f) =
      (sigmaZeroLinearMapEquiv K 𝕜 Y Z HY HZ g).comp
        (sigmaZeroLinearMapEquiv K 𝕜 X Y HX HY f) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
  exact sigmaZeroLiftLinearMap_comp K 𝕜 X Y Z HX HY HZ f g

/-- THEOREM 3: the inverse Hom equivalence sends the zero-fiber identity back
to the standard identity. -/
@[simp] theorem sigmaZeroLinearMapEquiv_symm_apply_id
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    [AddCommMonoid X] [Module 𝕜 X] :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    (sigmaZeroLinearMapEquiv K 𝕜 X X HX HX).symm
      (LinearMap.id :
        SigmaRelaxedObject K X HX (0 : K) →ₗ[𝕜]
          SigmaRelaxedObject K X HX (0 : K)) =
      (LinearMap.id : X →ₗ[𝕜] X) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  apply Equiv.injective (sigmaZeroLinearMapEquiv K 𝕜 X X HX HX)
  simp [sigmaZeroLinearMapEquiv_apply_id]

/-- A compact certificate: for a fixed headroom coordinate, the zero-fiber
linear Hom equivalence is fully faithful and operation-preserving across
ordinary linear carriers in one universe. -/
structure SigmaZeroLinearFullyFaithfulCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (H : Type w₁) [Inhabited H] where
  hom_equiv :
    ∀ (X Y : Type v₁)
      [AddCommMonoid X] [Module 𝕜 X]
      [AddCommMonoid Y] [Module 𝕜 Y],
      (X →ₗ[𝕜] Y) ≃ (by
        letI := sigmaZeroRelaxedAddCommMonoidInst K X H
        letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
        letI := sigmaZeroRelaxedAddCommMonoidInst K Y H
        letI := sigmaZeroRelaxedModuleInst K 𝕜 Y H
        exact
          SigmaRelaxedObject K X H (0 : K) →ₗ[𝕜]
            SigmaRelaxedObject K Y H (0 : K))
  map_id :
    ∀ (X : Type v₁)
      [AddCommMonoid X] [Module 𝕜 X],
      letI := sigmaZeroRelaxedAddCommMonoidInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      hom_equiv X X (LinearMap.id : X →ₗ[𝕜] X) =
        (LinearMap.id :
          SigmaRelaxedObject K X H (0 : K) →ₗ[𝕜]
            SigmaRelaxedObject K X H (0 : K))
  map_comp :
    ∀ (X Y Z : Type v₁)
      [AddCommMonoid X] [Module 𝕜 X]
      [AddCommMonoid Y] [Module 𝕜 Y]
      [AddCommMonoid Z] [Module 𝕜 Z]
      (f : X →ₗ[𝕜] Y) (g : Y →ₗ[𝕜] Z),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y H
      letI := sigmaZeroRelaxedAddCommMonoidInst K Z H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Z H
      hom_equiv X Z (g.comp f) =
        (hom_equiv Y Z g).comp (hom_equiv X Y f)

/-- THEOREM 4: the canonical fully-faithful, operation-preserving certificate.
This is a `def` because the certificate packages actual equivalence data. -/
def sigmaZeroLinearFullyFaithfulCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (H : Type w₁) [Inhabited H] :
    SigmaZeroLinearFullyFaithfulCertificate K 𝕜 H where
  hom_equiv := by
    intro X Y _ _ _ _
    exact sigmaZeroLinearMapEquiv K 𝕜 X Y H H
  map_id := by
    intro X _ _
    exact sigmaZeroLinearMapEquiv_apply_id K 𝕜 X H
  map_comp := by
    intro X Y Z _ _ _ _ _ _ f g
    exact sigmaZeroLinearMapEquiv_apply_comp K 𝕜 X H Y H Z H f g


end AffineRelaxation
end SaturationMonoid
