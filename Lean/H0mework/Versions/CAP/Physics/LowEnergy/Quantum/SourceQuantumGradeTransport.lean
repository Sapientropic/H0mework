import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceQuantumFockGrade56
import Mathlib.Tactic

/-! Diagonal radial similarity on the complete original occupation carrier. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceGradeTransport
open SaturationMonoid.PhysicsCore
open QuantizationCheck.Fermion SourceFockRaising
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def count (s word : Finset ι) : ℕ := (word.filter (fun i => i ∈ s)).card

omit [Fintype ι] in
theorem count_le (s word : Finset ι) : count s word ≤ s.card :=
  Finset.card_le_card (by intro i hi; exact (Finset.mem_filter.mp hi).2)

def weight (s : Finset ι) (r : ℂ) : End (ι := ι) where
  toFun psi word := r ^ (s.card - count s word) * psi word
  map_add' psi phi := by ext word; simp [mul_add]
  map_smul' c psi := by ext word; simp [mul_left_comm]

omit [Fintype ι] in
@[simp] theorem weight_apply (s : Finset ι) (r : ℂ) (psi : Fock ι) (word : Finset ι) :
    weight s r psi word = r ^ (s.card - count s word) * psi word := rfl

theorem weight_inverse (s : Finset ι) (r : ℂ) (hr : r ≠ 0) :
    weight s r * weight s r⁻¹ = 1 := by
  ext psi word
  simp [Module.End.mul_apply, hr]

omit [Fintype ι] in
theorem coefficient_grade (s : Finset ι) (T : End (ι := ι)) (d : ℕ)
    (law : grade s * T = T * grade s + (d : ℂ) • T)
    (u v : Finset ι) (nonzero : T (occupationBasis u) v ≠ 0) :
    count s v = count s u + d := by
  have he : grade s (occupationBasis u) = (count s u : ℂ) • occupationBasis u := by
    simpa [count, SourceFockRaising.grade, Finset.filter_mem_eq_inter] using
      basis_eigenstate (fun i : ι => if i ∈ s then (1 : ℂ) else 0) u
  have h := congrArg (fun A : End (ι := ι) => A (occupationBasis u) v) law
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    he, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, grade_apply] at h
  have hcast : (count s v : ℂ) = (count s u + d : ℂ) :=
    mul_right_cancel₀ nonzero (by simpa only [add_mul, count] using h)
  exact_mod_cast hcast

omit [Fintype ι] in
theorem weight_basis (s u : Finset ι) (r : ℂ) :
    weight s r (occupationBasis u) = r ^ (s.card - count s u) • occupationBasis u := by
  ext v
  by_cases same : v = u
  · subst v; simp [occupationBasis]
  · simp [occupationBasis, same]

theorem weight_homogeneous (s : Finset ι) (T : End (ι := ι)) (d : ℕ)
    (law : grade s * T = T * grade s + (d : ℂ) • T)
    (r : ℂ) (hr : r ≠ 0) :
    weight s r * T = (r ^ d)⁻¹ • (T * weight s r) := by
  have hb (u : Finset ι) :
      (weight s r * T) (occupationBasis u) =
        ((r ^ d)⁻¹ • (T * weight s r)) (occupationBasis u) := by
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, weight_basis,
      map_smul, Pi.smul_apply, smul_eq_mul, weight_apply]
    by_cases hz : T (occupationBasis u) v = 0
    · simp [hz]
    · have hg := coefficient_grade s T d law u v hz
      have hv := count_le s v
      have hp : s.card - count s u = s.card - count s v + d := by omega
      rw [hp, pow_add]
      field_simp
  apply LinearMap.ext
  intro psi
  have expansion : psi = ∑ u : Finset ι, psi u • occupationBasis u := by
    ext v; simp [occupationBasis, Finset.sum_apply]
  rw [expansion, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun u _ => by rw [map_smul, map_smul, hb])

theorem conjugate_homogeneous (s : Finset ι) (T : End (ι := ι)) (d : ℕ)
    (law : grade s * T = T * grade s + (d : ℂ) • T)
    (r : ℂ) (hr : r ≠ 0) :
    weight s r * T * weight s r⁻¹ = (r ^ d)⁻¹ • T := by
  rw [weight_homogeneous s T d law r hr, smul_mul_assoc, mul_assoc,
    weight_inverse s r hr, mul_one]

theorem pairing_return (s : Finset ι) (r : ℝ) (hr : r ≠ 0) (psi phi : Fock ι) :
    pairing (weight s (r : ℂ) psi) (weight s ((r : ℂ)⁻¹) phi) = pairing psi phi := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro word _
  have hn : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [weight_apply, star_mul, star_pow, Complex.star_def, Complex.conj_ofReal,
    inv_pow]
  field_simp

open SourceQuantumFockGrade56 SourceQuantumConfigurationHilbert SourceQuantumFockGauge
attribute [local instance] modeOrder

theorem original_yukawa_conjugate (spin : DiracCliffordRepresentation.DiracMatrix)
    (scalar : SU7ExteriorBreakingYukawa.ExteriorBreakingScalarCarrier)
    (r : ℂ) (hr : r ≠ 0) :
    weight target r * yukawaDensity spin scalar * weight target r⁻¹ =
      r⁻¹ • yukawaDensity spin scalar := by
  simpa using conjugate_homogeneous target (yukawaDensity spin scalar) 1
    (by simpa using yukawa_raises spin scalar) r hr

#print axioms original_yukawa_conjugate
#print axioms pairing_return
end LowEnergy.SourceGradeTransport
