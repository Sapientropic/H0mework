import H0mework.Realization.FibreLinear.P570

/-!
# Proposition 571: bounded operators are fully faithful at the sigma-zero fiber

P570 closed the ordinary linear Hom side.  Physical and analytic applications
usually need bounded/continuous operators: Hamiltonians in the bounded toy
layer, contraction witnesses, and linearized runtime maps all live at this
interface.

This file proves the same operation-preserving Hom equivalence for continuous
linear maps.  At `σ = 0`, adding the relaxed headroom coordinate does not change
bounded operator pipelines: identities and compositions are transported on the
nose.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Continuous Hom equivalence compatibility with category operations -/

/-- THEOREM 1: the sigma-zero bounded-linear Hom equivalence sends identity to
identity. -/
@[simp] theorem sigmaZeroContinuousLinearMapEquiv_apply_id
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    sigmaZeroContinuousLinearMapEquiv K 𝕜 X X HX HX
        (ContinuousLinearMap.id 𝕜 X) =
      ContinuousLinearMap.id 𝕜 (SigmaRelaxedObject K X HX (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  exact sigmaZeroLiftContinuousLinearMap_id K 𝕜 X HX

/-- THEOREM 2: the sigma-zero bounded-linear Hom equivalence sends composition
to composition. -/
@[simp] theorem sigmaZeroContinuousLinearMapEquiv_apply_comp
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X Y Z : Type v)
    (HX HY HZ : Type w) [Inhabited HX] [Inhabited HY] [Inhabited HZ]
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
    sigmaZeroContinuousLinearMapEquiv K 𝕜 X Z HX HZ (g.comp f) =
      (sigmaZeroContinuousLinearMapEquiv K 𝕜 Y Z HY HZ g).comp
        (sigmaZeroContinuousLinearMapEquiv K 𝕜 X Y HX HY f) := by
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
  exact sigmaZeroLiftContinuousLinearMap_comp K 𝕜 X Y Z HX HY HZ f g

/-- THEOREM 3: the inverse bounded-linear Hom equivalence sends the zero-fiber
identity back to the standard identity. -/
@[simp] theorem sigmaZeroContinuousLinearMapEquiv_symm_apply_id
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    (sigmaZeroContinuousLinearMapEquiv K 𝕜 X X HX HX).symm
        (ContinuousLinearMap.id 𝕜 (SigmaRelaxedObject K X HX (0 : K))) =
      ContinuousLinearMap.id 𝕜 X := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  apply Equiv.injective (sigmaZeroContinuousLinearMapEquiv K 𝕜 X X HX HX)
  simp [sigmaZeroContinuousLinearMapEquiv_apply_id]

/-- For a fixed headroom coordinate, bounded operators on ordinary normed
spaces and bounded operators on sigma-zero fibers are equivalent in an
operation-preserving way. -/
structure SigmaZeroContinuousLinearFullyFaithfulCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (H : Type w) [Inhabited H] where
  hom_equiv :
    ∀ (X Y : Type v)
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
      (X →L[𝕜] Y) ≃ (by
        letI := sigmaZeroRelaxedAddCommGroupInst K X H
        letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
        letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
        letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
        letI := sigmaZeroRelaxedAddCommGroupInst K Y H
        letI := sigmaZeroRelaxedModuleInst K 𝕜 Y H
        letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y H
        letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y H
        exact
          SigmaRelaxedObject K X H (0 : K) →L[𝕜]
            SigmaRelaxedObject K Y H (0 : K))
  map_id :
    ∀ (X : Type v)
      [NormedAddCommGroup X] [NormedSpace 𝕜 X],
      letI := sigmaZeroRelaxedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
      hom_equiv X X (ContinuousLinearMap.id 𝕜 X) =
        ContinuousLinearMap.id 𝕜 (SigmaRelaxedObject K X H (0 : K))
  map_comp :
    ∀ (X Y Z : Type v)
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
      (f : X →L[𝕜] Y) (g : Y →L[𝕜] Z),
      letI := sigmaZeroRelaxedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X H
      letI := sigmaZeroRelaxedAddCommGroupInst K Y H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y H
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y H
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y H
      letI := sigmaZeroRelaxedAddCommGroupInst K Z H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Z H
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K Z H
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Z H
      hom_equiv X Z (g.comp f) =
        (hom_equiv Y Z g).comp (hom_equiv X Y f)

/-- THEOREM 4: the canonical bounded-operator fully-faithful certificate.
This is a `def` because it packages equivalence data. -/
def sigmaZeroContinuousLinearFullyFaithfulCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (H : Type w) [Inhabited H] :
    SigmaZeroContinuousLinearFullyFaithfulCertificate K 𝕜 H where
  hom_equiv := by
    intro X Y _ _ _ _
    exact sigmaZeroContinuousLinearMapEquiv K 𝕜 X Y H H
  map_id := by
    intro X _ _
    exact sigmaZeroContinuousLinearMapEquiv_apply_id K 𝕜 X H
  map_comp := by
    intro X Y Z _ _ _ _ _ _ f g
    exact sigmaZeroContinuousLinearMapEquiv_apply_comp K 𝕜 X Y Z H H H f g


end AffineRelaxation
end SaturationMonoid
