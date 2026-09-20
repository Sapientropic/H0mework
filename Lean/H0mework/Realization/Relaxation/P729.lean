import H0mework.Realization.RelaxationAlgebra.P728

/-!
# Proposition 729: relaxation-preserving maps are exactly affine maps

P728 proved the hard converse:

`g (relaxModule target sigma x) =
  relaxModule (g target) sigma (g x)`

forces `g` to be affine-linear over real module carriers.

This file closes the classification.  The forward direction is also true:
every affine-linear map commutes with every relaxation operation.  Therefore
the homomorphisms of the target-general relaxation algebra are exactly affine
maps.  In the bijective case, the linear part is bijective, so relaxation
automorphisms have no hidden nonlinear coordinate freedom.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u v

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup F] [Module ℝ F]

/-! ## Affine maps -/

/-- A real affine map is a linear map plus a constant translation. -/
def IsAffineRealMap (g : E -> F) : Prop :=
  ∃ (L : E →ₗ[ℝ] F) (b : F), ∀ x : E, g x = L x + b

/-- A real affine equivalence-shaped map is an affine map whose linear part is
bijective.  This avoids any API dependence on `LinearEquiv` while retaining
the exact mathematical content needed by the carrier classification. -/
def IsAffineRealEquivalenceMap (g : E -> F) : Prop :=
  ∃ (L : E →ₗ[ℝ] F), Function.Bijective L ∧
    ∃ b : F, ∀ x : E, g x = L x + b

/-! ## Affine maps preserve relaxation -/

/-- THEOREM 1: every affine-linear map commutes with every real relaxation
operation. -/
theorem affineRealMap_commutesWithRelaxModule
    (g : E -> F)
    (haff : IsAffineRealMap g) :
    CommutesWithRealRelaxModule g := by
  rcases haff with ⟨L, b, hg⟩
  intro target sigma x
  rw [hg (relaxModule target sigma x), hg target, hg x]
  rw [linearMap_relaxModule_commute (K := ℝ) L target x sigma]
  unfold relaxModule
  module

/-! ## Relaxation-preserving maps are affine -/

/-- THEOREM 2: every relaxation-preserving map is affine-linear. -/
theorem affineRealMap_of_commutesWithRelaxModule
    (g : E -> F)
    (hcomm : CommutesWithRealRelaxModule g) :
    IsAffineRealMap g := by
  exact ⟨centeredLinearMapOfRelaxCommuting g hcomm, g 0,
    relaxCommuting_observer_eq_linear_plus_base g hcomm⟩

/-- THEOREM 3: target-general relaxation homomorphisms are exactly affine
maps. -/
theorem commutesWithRelaxModule_iff_affineRealMap
    (g : E -> F) :
    CommutesWithRealRelaxModule g ↔ IsAffineRealMap g := by
  constructor
  · exact affineRealMap_of_commutesWithRelaxModule g
  · exact affineRealMap_commutesWithRelaxModule g

/-! ## Bijective maps: automorphism-shaped classification -/

/-- THEOREM 4: if a relaxation-preserving map is bijective, its reconstructed
linear part is bijective. -/
theorem centeredLinearMap_bijective_of_commutesWithRelaxModule_bijective
    (g : E -> F)
    (hcomm : CommutesWithRealRelaxModule g)
    (hbij : Function.Bijective g) :
    Function.Bijective (centeredLinearMapOfRelaxCommuting g hcomm) := by
  constructor
  · intro x y hxy
    apply hbij.1
    rw [relaxCommuting_observer_eq_linear_plus_base g hcomm x]
    rw [relaxCommuting_observer_eq_linear_plus_base g hcomm y]
    rw [hxy]
  · intro z
    rcases hbij.2 (z + g 0) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hgx := relaxCommuting_observer_eq_linear_plus_base g hcomm x
    have hsum : centeredLinearMapOfRelaxCommuting g hcomm x + g 0 = z + g 0 := by
      rw [← hgx, hx]
    have hsub := congrArg (fun y : F => y - g 0) hsum
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsub

/-- THEOREM 5: bijective relaxation-preserving maps are exactly affine maps
with bijective linear part. -/
theorem commutesWithRelaxModule_and_bijective_iff_affineRealEquivalenceMap
    (g : E -> F) :
    (CommutesWithRealRelaxModule g ∧ Function.Bijective g) ↔
      IsAffineRealEquivalenceMap g := by
  constructor
  · intro h
    exact ⟨centeredLinearMapOfRelaxCommuting g h.1,
      centeredLinearMap_bijective_of_commutesWithRelaxModule_bijective
        g h.1 h.2,
      g 0,
      relaxCommuting_observer_eq_linear_plus_base g h.1⟩
  · intro h
    rcases h with ⟨L, hLbij, b, hg⟩
    constructor
    · exact affineRealMap_commutesWithRelaxModule g ⟨L, b, hg⟩
    · constructor
      · intro x y hxy
        apply hLbij.1
        have hxy' := congrArg (fun z : F => z - b) hxy
        rw [hg x, hg y] at hxy'
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxy'
      · intro z
        rcases hLbij.2 (z - b) with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [hg x, hx]
        simp [sub_eq_add_neg, add_comm]

/-! ## Certificate -/

/-- P729 certificate: the homomorphisms of the real target-general relaxation
algebra are exactly affine maps, and bijective homomorphisms are exactly
affine maps with bijective linear part. -/
structure RelaxationAffineMapClassificationCertificate
    (E : Type u) (F : Type v)
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] : Prop where
  affine_maps_commute :
    ∀ g : E -> F, IsAffineRealMap g -> CommutesWithRealRelaxModule g
  commuting_maps_affine :
    ∀ g : E -> F, CommutesWithRealRelaxModule g -> IsAffineRealMap g
  hom_iff_affine :
    ∀ g : E -> F, CommutesWithRealRelaxModule g ↔ IsAffineRealMap g
  bijective_linear_part_forced :
    ∀ (g : E -> F) (hcomm : CommutesWithRealRelaxModule g),
      Function.Bijective g ->
      Function.Bijective (centeredLinearMapOfRelaxCommuting g hcomm)
  automorphism_shape_iff :
    ∀ g : E -> F,
      (CommutesWithRealRelaxModule g ∧ Function.Bijective g) ↔
        IsAffineRealEquivalenceMap g

/-- THEOREM 6: every pair of real module carriers has the full affine
classification certificate. -/
theorem relaxationAffineMapClassificationCertificate :
    RelaxationAffineMapClassificationCertificate E F where
  affine_maps_commute := affineRealMap_commutesWithRelaxModule
  commuting_maps_affine := affineRealMap_of_commutesWithRelaxModule
  hom_iff_affine := commutesWithRelaxModule_iff_affineRealMap
  bijective_linear_part_forced := by
    intro g hcomm hbij
    exact centeredLinearMap_bijective_of_commutesWithRelaxModule_bijective
      g hcomm hbij
  automorphism_shape_iff :=
    commutesWithRelaxModule_and_bijective_iff_affineRealEquivalenceMap

end AffineRelaxation
end SaturationMonoid
