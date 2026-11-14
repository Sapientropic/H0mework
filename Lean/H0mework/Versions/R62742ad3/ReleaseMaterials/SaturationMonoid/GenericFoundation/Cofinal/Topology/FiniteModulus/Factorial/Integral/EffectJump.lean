import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Integral.Bounded
import H0mework.Versions.R62742ad3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Integral.Representative
import Mathlib.Analysis.Normed.Module.Basic

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits

variable {L : Type u} [AddCommGroup L]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem integer_smul_norm (coefficient : ℤ) (value : E) :
    ‖coefficient • value‖ = (coefficient.natAbs : ℝ)*‖value‖ := by
  rw [norm_zsmul ℝ, norm_intCast_eq_abs_mul_norm_one, norm_one, mul_one, Nat.cast_natAbs]

/-- Two representatives of adjacent actual restrictions differ by a whole modulus in the action. -/
theorem factorial_effect_jump (coordinate : L ≃ₗ[ℤ] ℤ) (effect : L →ₗ[ℤ] E)
    (value : FactorialCompletion (L := L)) (source : Nat → L)
    (reads : ∀ stage, modulusProjection (factorialModulus stage) (source stage) =
      (factorialRestriction (L := L) stage).hom value) (stage : Nat) :
    let unit := effect (coordinate.symm 1)
    ∃! jump : ℤ,
      (factorialModulus stage : ℤ)*jump = coordinate (source (stage+1)) - coordinate (source stage) ∧
      effect (source (stage+1)) - effect (source stage) = (factorialModulus stage : ℤ) • (jump • unit) ∧
      ‖effect (source (stage+1)) - effect (source stage)‖ =
        (factorialModulus stage : ℝ)*(jump.natAbs : ℝ)*‖unit‖ := by
  dsimp only
  let edge := (homOfLE (Nat.le_succ stage)).op
  let restrict := (factorialTower (L := L)).map edge
  have coherent := ConcreteCategory.congr_hom (limit.w (factorialTower (L := L)) edge) value
  have same : modulusProjection (factorialModulus stage) (source (stage+1)) =
      modulusProjection (factorialModulus stage) (source stage) :=
    (factorial_edge_projection (Nat.le_succ stage) _).symm.trans
      ((congrArg restrict.hom (reads (stage+1))).trans (coherent.trans (reads stage).symm))
  obtain ⟨difference, paid⟩ := (modulus_source_fibre (factorialModulus stage)
    (factorial_modulus_ne_zero stage) (source (stage+1)) (source stage)).1 same
  have coefficient := congrArg coordinate paid
  rw [map_smul, map_sub, smul_eq_mul] at coefficient
  have recover : difference = coordinate difference • coordinate.symm 1 := by
    apply coordinate.injective
    rw [map_smul, coordinate.apply_symm_apply, smul_eq_mul, mul_one]
  have acted : effect (source (stage+1)) - effect (source stage) =
      (factorialModulus stage : ℤ) • (coordinate difference • effect (coordinate.symm 1)) := by
    rw [← map_sub, ← paid, map_smul]
    exact congrArg ((factorialModulus stage : ℤ) • ·)
      ((congrArg effect recover).trans (map_smul effect _ _))
  refine ⟨coordinate difference, ⟨coefficient, acted, ?_⟩, ?_⟩
  · rw [acted, integer_smul_norm, integer_smul_norm]
    change (factorialModulus stage : ℝ)*((coordinate difference).natAbs*‖effect (coordinate.symm 1)‖) = _
    rw [mul_assoc]
  · intro other written
    have positive : (0 : ℤ) < (factorialModulus stage : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero (factorial_modulus_ne_zero stage)
    exact mul_left_cancel₀ positive.ne' (written.1.trans coefficient.symm)

theorem factorial_effect_jump_lt_iff (coordinate : L ≃ₗ[ℤ] ℤ) (effect : L →ₗ[ℤ] E)
    (live : effect (coordinate.symm 1) ≠ 0)
    (value : FactorialCompletion (L := L)) (source : Nat → L)
    (reads : ∀ stage, modulusProjection (factorialModulus stage) (source stage) =
      (factorialRestriction (L := L) stage).hom value) (stage : Nat) :
    ‖effect (source (stage+1)) - effect (source stage)‖ <
        (factorialModulus stage : ℝ)*‖effect (coordinate.symm 1)‖ ↔
      source (stage+1) = source stage := by
  have positive : (0 : ℝ) < (factorialModulus stage : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (factorial_modulus_ne_zero stage)
  have unit := norm_pos_iff.mpr live
  obtain ⟨jump, ⟨coefficient, _, distance⟩, _⟩ := factorial_effect_jump coordinate effect value source reads stage
  constructor
  · intro small
    have zero : jump = 0 := by
      by_contra different
      have magnitude : (1 : ℝ) ≤ (jump.natAbs : ℝ) := by
        exact_mod_cast Int.natAbs_pos.mpr different
      have gap := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left magnitude positive.le) unit.le
      rw [mul_one, ← distance] at gap
      exact (not_lt_of_ge gap) small
    rw [zero, mul_zero] at coefficient
    exact coordinate.injective (sub_eq_zero.mp coefficient.symm)
  · intro equal
    rw [equal, sub_self, norm_zero]
    exact mul_pos positive unit

/-- The actual whole-effect spacing detects integral descent of the signed representatives. -/
theorem factorial_small_effect_recovers_source (coordinate : L ≃ₗ[ℤ] ℤ) (effect : L →ₗ[ℤ] E)
    (live : effect (coordinate.symm 1) ≠ 0) (value : FactorialCompletion (L := L)) :
    (∃! source : L, factorialCanonicalMap source = value) ↔
      ∃ base : Nat, ∀ stage ≥ base,
        ‖effect (factorialBalancedLift coordinate value (stage+1)) -
          effect (factorialBalancedLift coordinate value stage)‖ <
          (factorialModulus stage : ℝ)*‖effect (coordinate.symm 1)‖ := by
  let representative := factorialBalancedLift coordinate value
  have reads (stage : Nat) := (factorial_balanced_lift coordinate value stage).1
  have discrete := factorial_effect_jump_lt_iff coordinate effect live value representative reads
  constructor
  · rintro ⟨source, written, _⟩
    obtain ⟨base, stable⟩ := factorial_balanced_diagonal coordinate source
    refine ⟨base, fun stage late => (discrete stage).2 ?_⟩
    dsimp only [representative]
    rw [← written]
    exact (stable (stage+1) (late.trans (Nat.le_succ stage))).trans (stable stage late).symm
  · rintro ⟨base, small⟩
    have fixed (stage : Nat) (late : base ≤ stage) : representative stage = representative base := by
      induction stage, late using Nat.le_induction with
      | base => rfl
      | succ stage late prior => exact ((discrete stage).1 (small stage late)).trans prior
    classical
    obtain ⟨source, stocked, original⟩ := (factorial_integral_inventory_iff {representative base} value).2
      ⟨base, fun stage late =>
        ⟨representative base, Finset.mem_singleton_self _, fixed stage late ▸ reads stage⟩⟩
    have same := Finset.mem_singleton.mp stocked
    have written : factorialCanonicalMap (representative base) = value := same ▸ original
    exact ⟨representative base, written, fun other equal =>
      factorial_canonical_injective coordinate (equal.trans written.symm)⟩

/-- An actual nonintegral coherent class produces a whole-effect jump at an arbitrarily late layer. -/
theorem factorial_nonintegral_effect_jumps (coordinate : L ≃ₗ[ℤ] ℤ) (effect : L →ₗ[ℤ] E)
    (live : effect (coordinate.symm 1) ≠ 0) (value : FactorialCompletion (L := L))
    (outside : ¬∃ source : L, factorialCanonicalMap source = value) (base : Nat) :
    ∃ stage ≥ base, (factorialModulus stage : ℝ)*‖effect (coordinate.symm 1)‖ ≤
      ‖effect (factorialBalancedLift coordinate value (stage+1)) -
        effect (factorialBalancedLift coordinate value stage)‖ := by
  by_contra missing
  have selected := (factorial_small_effect_recovers_source coordinate effect live value).2
    ⟨base, fun stage late => lt_of_not_ge (fun jump => missing ⟨stage, late, jump⟩)⟩
  exact outside selected.exists

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
