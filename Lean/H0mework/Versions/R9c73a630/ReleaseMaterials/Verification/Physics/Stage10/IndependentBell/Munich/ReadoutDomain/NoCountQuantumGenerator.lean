import Mathlib.Tactic

set_option autoImplicit false

namespace BellNoCountQuantumGenerator

def mask (b : Bool) : ℝ := if b then 1 else 0

theorem original_mark_restriction (inside forbidden : Bool) :
    mask (inside && !forbidden) - mask inside = -mask (inside && forbidden) := by
  cases inside <;> cases forbidden <;> norm_num [mask]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem source_quantum_registered_restriction (J : V →ₗ[ℝ] V) (rho : V)
    (inside forbidden : Bool) :
    mask (inside && !forbidden) • J rho - mask inside • J rho =
      -mask (inside && forbidden) • J rho := by
  rw [← sub_smul, original_mark_restriction]

theorem source_natural_minus_forbidden (L J : V →ₗ[ℝ] V) (rho : V) (forbidden : Bool) :
    L rho + mask (!forbidden) • J rho - J rho = L rho - mask forbidden • J rho := by
  cases forbidden <;> simp [mask]

variable {ι : Type*} [Fintype ι]

theorem whole_source_quantum_restriction (L : V →ₗ[ℝ] V) (J : ι → V →ₗ[ℝ] V)
    (rho : ι → V) (inside forbidden : ι → Bool) :
    L (∑ i, mask (inside i) • rho i) +
      (∑ i, (mask (inside i && !forbidden i) • J i (rho i) -
             mask (inside i) • J i (rho i))) =
      L (∑ i, mask (inside i) • rho i) -
        ∑ i, mask (inside i && forbidden i) • J i (rho i) := by
  simp_rw [source_quantum_registered_restriction, neg_smul]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]

end BellNoCountQuantumGenerator
