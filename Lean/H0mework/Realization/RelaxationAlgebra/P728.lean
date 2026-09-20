import H0mework.Realization.Residual.P727

/-!
# Proposition 728: relaxation-commuting observers are affine-linear

P726/P727 prove the forward direction: linear projections produce common
residual projection cores.  This file proves the rigidity converse over real
module carriers.

If an observer `g : E -> F` commutes with every affine relaxation step,

`g (relaxModule target sigma x) = relaxModule (g target) sigma (g x)`,

then its centered part `x ↦ g x - g 0` is a genuine linear map.  If `g 0 = 0`,
then `g` itself is linear.  Thus the common-core projection bridge has no
hidden nonlinear freedom in the real carrier: preserving the relaxation
operation forces affine-linearity.
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

/-- A map commutes with all target-general real relaxation operations. -/
def CommutesWithRealRelaxModule (g : E -> F) : Prop :=
  ∀ (target : E) (sigma : ℝ) (x : E),
    g (relaxModule target sigma x) =
      relaxModule (g target) sigma (g x)

/-- THEOREM 1: a relaxation-commuting map that sends zero to zero preserves
all scalar multiplication. -/
theorem relaxCommuting_map_smul_of_zero
    (g : E -> F)
    (hcomm : CommutesWithRealRelaxModule g)
    (hzero : g 0 = 0)
    (a : ℝ) (x : E) :
    g (a • x) = a • g x := by
  have h := hcomm 0 (1 - a) x
  have hleft : relaxModule (0 : E) (1 - a) x = a • x := by
    unfold relaxModule
    module
  have hright : relaxModule (g (0 : E)) (1 - a) (g x) = a • g x := by
    rw [hzero]
    unfold relaxModule
    module
  rw [hleft, hright] at h
  exact h

/-- THEOREM 2: a relaxation-commuting map that sends zero to zero preserves
addition. -/
theorem relaxCommuting_map_add_of_zero
    (g : E -> F)
    (hcomm : CommutesWithRealRelaxModule g)
    (hzero : g 0 = 0)
    (x y : E) :
    g (x + y) = g x + g y := by
  let half : ℝ := (2 : ℝ)⁻¹
  let mid : E := half • (x + y)
  have hmid_comm := hcomm y half x
  have hleft : relaxModule y half x = mid := by
    dsimp [mid, half]
    unfold relaxModule
    module
  have hright :
      relaxModule (g y) half (g x) =
        half • (g x + g y) := by
    dsimp [half]
    unfold relaxModule
    module
  have hmid : g mid = half • (g x + g y) := by
    rw [hleft, hright] at hmid_comm
    exact hmid_comm
  have htwo_mid : (2 : ℝ) • mid = x + y := by
    dsimp [mid, half]
    module
  calc
    g (x + y)
        = g ((2 : ℝ) • mid) := by rw [htwo_mid]
    _ = (2 : ℝ) • g mid := by
          exact relaxCommuting_map_smul_of_zero g hcomm hzero 2 mid
    _ = (2 : ℝ) • (half • (g x + g y)) := by rw [hmid]
    _ = g x + g y := by
          dsimp [half]
          module

/-- THEOREM 3: a relaxation-commuting map that sends zero to zero is a linear
map. -/
def linearMapOfRelaxCommutingZero
    (g : E -> F)
    (hcomm : CommutesWithRealRelaxModule g)
    (hzero : g 0 = 0) : E →ₗ[ℝ] F where
  toFun := g
  map_add' := relaxCommuting_map_add_of_zero g hcomm hzero
  map_smul' := relaxCommuting_map_smul_of_zero g hcomm hzero

/-- THEOREM 4: the linear map reconstructed from a zero-based commuting
observer has the original observer as its function. -/
theorem linearMapOfRelaxCommutingZero_apply
    (g : E -> F)
    (hcomm : CommutesWithRealRelaxModule g)
    (hzero : g 0 = 0)
    (x : E) :
    linearMapOfRelaxCommutingZero g hcomm hzero x = g x := rfl

/-- Center an arbitrary observer by subtracting its value at zero. -/
def centeredRelaxObserver (g : E -> F) : E -> F :=
  fun x => g x - g 0

/-- THEOREM 5: centering sends zero to zero. -/
theorem centeredRelaxObserver_zero (g : E -> F) :
    centeredRelaxObserver g 0 = 0 := by
  unfold centeredRelaxObserver
  simp

/-- THEOREM 6: centering preserves relaxation-commutation. -/
theorem centeredRelaxObserver_commutes
    (g : E -> F)
    (hcomm : CommutesWithRealRelaxModule g) :
    CommutesWithRealRelaxModule (centeredRelaxObserver g) := by
  intro target sigma x
  unfold centeredRelaxObserver
  rw [hcomm target sigma x]
  unfold relaxModule
  module

/-- THEOREM 7: the centered part of any relaxation-commuting observer is
linear. -/
def centeredLinearMapOfRelaxCommuting
    (g : E -> F)
    (hcomm : CommutesWithRealRelaxModule g) : E →ₗ[ℝ] F :=
  linearMapOfRelaxCommutingZero
    (centeredRelaxObserver g)
    (centeredRelaxObserver_commutes g hcomm)
    (centeredRelaxObserver_zero g)

/-- THEOREM 8: the reconstructed centered linear map is exactly
`x ↦ g x - g 0`. -/
theorem centeredLinearMapOfRelaxCommuting_apply
    (g : E -> F)
    (hcomm : CommutesWithRealRelaxModule g)
    (x : E) :
    centeredLinearMapOfRelaxCommuting g hcomm x = g x - g 0 := rfl

/-- THEOREM 9: every relaxation-commuting observer is an affine translate of
its reconstructed centered linear map. -/
theorem relaxCommuting_observer_eq_linear_plus_base
    (g : E -> F)
    (hcomm : CommutesWithRealRelaxModule g)
    (x : E) :
    g x = centeredLinearMapOfRelaxCommuting g hcomm x + g 0 := by
  rw [centeredLinearMapOfRelaxCommuting_apply]
  simp

/-! ## Certificates -/

/-- P728 certificate: preserving every real relaxation operation is rigid
enough to force affine-linearity. -/
structure RelaxCommutingAffineRigidityCertificate
    (E : Type u) (F : Type v)
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] : Prop where
  zero_based_preserves_smul :
    ∀ (g : E -> F),
      CommutesWithRealRelaxModule g ->
      g 0 = 0 ->
      ∀ (a : ℝ) (x : E), g (a • x) = a • g x
  zero_based_preserves_add :
    ∀ (g : E -> F),
      CommutesWithRealRelaxModule g ->
      g 0 = 0 ->
      ∀ x y : E, g (x + y) = g x + g y
  zero_based_linear :
    ∀ (g : E -> F),
      CommutesWithRealRelaxModule g ->
      g 0 = 0 ->
      ∃ L : E →ₗ[ℝ] F, ∀ x : E, L x = g x
  centered_commutes :
    ∀ (g : E -> F),
      CommutesWithRealRelaxModule g ->
      CommutesWithRealRelaxModule (centeredRelaxObserver g)
  centered_linear :
    ∀ (g : E -> F),
      CommutesWithRealRelaxModule g ->
      ∃ L : E →ₗ[ℝ] F, ∀ x : E, L x = g x - g 0
  affine_reconstruction :
    ∀ (g : E -> F) (hcomm : CommutesWithRealRelaxModule g),
      ∀ x : E, g x = centeredLinearMapOfRelaxCommuting g hcomm x + g 0

/-- THEOREM 10: every pair of real module carriers has the affine rigidity
certificate. -/
theorem relaxCommutingAffineRigidityCertificate :
    RelaxCommutingAffineRigidityCertificate E F where
  zero_based_preserves_smul := relaxCommuting_map_smul_of_zero
  zero_based_preserves_add := relaxCommuting_map_add_of_zero
  zero_based_linear := by
    intro g hcomm hzero
    exact ⟨linearMapOfRelaxCommutingZero g hcomm hzero,
      linearMapOfRelaxCommutingZero_apply g hcomm hzero⟩
  centered_commutes := centeredRelaxObserver_commutes
  centered_linear := by
    intro g hcomm
    exact ⟨centeredLinearMapOfRelaxCommuting g hcomm,
      centeredLinearMapOfRelaxCommuting_apply g hcomm⟩
  affine_reconstruction := by
    intro g hcomm x
    exact relaxCommuting_observer_eq_linear_plus_base g hcomm x

end AffineRelaxation
end SaturationMonoid
