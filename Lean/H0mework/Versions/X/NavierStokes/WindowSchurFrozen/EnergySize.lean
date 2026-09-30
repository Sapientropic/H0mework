import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.HeatDual

set_option autoImplicit false
open scoped BigOperators
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryHeatSize
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeFiniteActionResolvent
open NativeWholeH1Mixed (modes)
open NativeWindowHistoryHeatDual (energy form)
noncomputable section

def size (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) : ℝ := Real.sqrt (energy nu M v)

theorem size_nonnegative (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) : 0 ≤ size nu M v := Real.sqrt_nonneg _

theorem size_square (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) : (size nu M v)^2=energy nu M v :=
  Real.sq_sqrt (NativeWindowHistoryHeatDual.energy_nonnegative nu M v)

theorem size_zero (nu : Viscosity) (M : ℕ) : size nu M 0=0 := by
  have source : energy nu M 0=0 := (NativeWindowHistoryHeatDual.form_self nu M 0).symm.trans (map_zero _)
  simp only [size,source,Real.sqrt_zero]

theorem size_neg (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) : size nu M (-v)=size nu M v := by
  have source : energy nu M (-v)=energy nu M v := by
    rw [← NativeWindowHistoryHeatDual.form_self,← NativeWindowHistoryHeatDual.form_self]
    simp only [map_neg,LinearMap.neg_apply,neg_neg]
  exact congrArg Real.sqrt source

theorem size_add (nu : Viscosity) (M : ℕ) (u v : physicalSpace (modes M)) :
    size nu M (u+v) ≤ size nu M u+size nu M v := by
  have source : energy nu M (u+v)=energy nu M u+2*form nu M u v+energy nu M v := by
    simp only [← NativeWindowHistoryHeatDual.form_self,map_add,LinearMap.add_apply,
      NativeWindowHistoryHeatDual.form_symmetric nu M v u]
    ring
  have paired := (le_abs_self (form nu M u v)).trans (NativeWindowHistoryHeatDual.form_bound nu M u v)
  apply (Real.sqrt_le_left (add_nonneg (size_nonnegative nu M u) (size_nonnegative nu M v))).mpr
  rw [source]
  have first := size_square nu M u
  have second := size_square nu M v
  change form nu M u v ≤ size nu M u*size nu M v at paired
  nlinarith only [paired,first,second]

theorem size_nsmul (nu : Viscosity) (M : ℕ) (n : ℕ) (v : physicalSpace (modes M)) :
    size nu M (n • v)≤(n : ℝ)*size nu M v := by
  induction n with
  | zero => simp only [zero_nsmul,size_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ n ih =>
    rw [succ_nsmul]
    have triangle := size_add nu M (n • v) v
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith only [triangle,ih]

theorem size_sum {I : Type*} (nu : Viscosity) (M : ℕ) (indices : Finset I) (v : I → physicalSpace (modes M)) :
    size nu M (∑ i∈indices,v i)≤∑ i∈indices,size nu M (v i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,size_zero,le_refl]
  | @insert i indices outside ih =>
    rw [Finset.sum_insert outside,Finset.sum_insert outside]
    have triangle := size_add nu M (v i) (∑ j∈indices,v j)
    linarith only [triangle,ih]

theorem size_bound (nu : Viscosity) (M : ℕ) (u v : physicalSpace (modes M)) (C : ℝ) (nonnegative : 0≤C)
    (paid : energy nu M u≤C^2*energy nu M v) : size nu M u≤C*size nu M v := by
  have source := Real.sqrt_le_sqrt paid
  simpa only [size,Real.sqrt_mul (sq_nonneg C),Real.sqrt_sq nonnegative] using source

theorem energy_bound (nu : Viscosity) (M : ℕ) (u v : physicalSpace (modes M)) (C : ℝ)
    (paid : size nu M u≤C*size nu M v) : energy nu M u≤C^2*energy nu M v := by
  have source := pow_le_pow_left₀ (size_nonnegative nu M u) paid 2
  simpa only [mul_pow,size_square] using source

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryHeatSize
