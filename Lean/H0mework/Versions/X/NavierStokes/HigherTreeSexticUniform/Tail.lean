import H0mework.Versions.X.NavierStokes.HigherTreeSexticUniform.Prefix

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformTail
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalIntegerLatticeCriticalKernel ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
open NativeUnheatedSexticLatticePower NativeUnheatedClockMomentKernel NativeUnheatedSexticUniformCube NativeUnheatedSexticUniformPrefix
noncomputable section

def decay (radius : ℕ) : ℝ := ((radius : ℝ)*Real.sqrt radius)⁻¹

theorem decay_nonnegative (radius : ℕ) : 0 ≤ decay radius := by unfold decay; positivity

theorem decay_step (radius : ℕ) : decay (4*radius) = decay radius/8 := by
  unfold decay
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  ring

theorem annulus_seven (center : IntegerWavevector) (radius : ℕ) (positive : 0 < radius) :
    (∑ wave ∈ integerWaveFrequencyCube (4*radius) \ integerWaveFrequencyCube radius,
      density 7 wave*density 2 (center-wave)) ≤ 2160*decay radius := by
  apply (annulus_bound 7 center radius positive).trans_eq
  have root : 0 < Real.sqrt radius := Real.sqrt_pos.mpr (Nat.cast_pos.mpr positive)
  have sixth : (Real.sqrt radius)^6 = (radius : ℝ)^3 := by
    rw [show (Real.sqrt radius)^6 = ((Real.sqrt radius)^2)^3 by ring,
      Real.sq_sqrt (Nat.cast_nonneg radius)]
  unfold decay
  push_cast
  field_simp
  linear_combination -2160*sixth

theorem power_tail (center : IntegerWavevector) (radius number : ℕ) (positive : 0 < radius) :
    amount 7 center (4^number*radius)-amount 7 center radius ≤
      4320*(decay radius-decay (4^number*radius)) := by
  induction number with
  | zero => simp
  | succ number previous =>
      have step : (4 : ℕ)^(number+1)*radius=4*(4^number*radius) := by rw [pow_succ]; ring
      rw [step]
      have split : amount 7 center (4*(4^number*radius)) =
          (∑ wave ∈ integerWaveFrequencyCube (4*(4^number*radius)) \ integerWaveFrequencyCube (4^number*radius),
            density 7 wave*density 2 (center-wave))+amount 7 center (4^number*radius) := by
        exact (Finset.sum_sdiff (cube_mono (show 4^number*radius ≤ 4*(4^number*radius) by omega))).symm
      have paid := annulus_seven center (4^number*radius) (by positivity)
      rw [split, decay_step]
      nlinarith [decay_nonnegative (4^number*radius)]

theorem weighted_tail (center : IntegerWavevector) (radius : ℕ) (positive : 0 < radius)
    (observed : Finset IntegerWavevector) :
    (∑ wave ∈ observed \ integerWaveFrequencyCube radius, density 7 wave*density 2 (center-wave)) ≤
      4320*decay radius := by
  classical
  let upper := max radius (observed.sup integerWaveCoordinateRadius)
  let number := Nat.log 4 upper+1
  have enclosed : upper ≤ 4^number := (Nat.lt_pow_succ_log_self (by norm_num : 1 < (4 : ℕ)) upper).le
  have scale : 4^number ≤ 4^number*radius := Nat.le_mul_of_pos_right _ positive
  have ordered : radius ≤ 4^number*radius := (le_max_left _ _).trans (enclosed.trans scale)
  have covered : observed \ integerWaveFrequencyCube radius ⊆
      integerWaveFrequencyCube (4^number*radius) \ integerWaveFrequencyCube radius := by
    intro wave inside
    refine Finset.mem_sdiff.mpr ⟨?_, (Finset.mem_sdiff.mp inside).2⟩
    exact integerWave_mem_frequencyCube_of_radius_le wave (4^number*radius)
      (((Finset.le_sup (Finset.mem_sdiff.mp inside).1).trans (le_max_right _ _)).trans (enclosed.trans scale))
  have compared := Finset.sum_le_sum_of_subset_of_nonneg covered
    (fun wave _ _ => mul_nonneg (density_positive 7 wave).le (density_positive 2 (center-wave)).le)
  have equality : (∑ wave ∈ integerWaveFrequencyCube (4^number*radius) \ integerWaveFrequencyCube radius,
      density 7 wave*density 2 (center-wave)) = amount 7 center (4^number*radius)-amount 7 center radius :=
    eq_sub_of_add_eq (Finset.sum_sdiff (cube_mono ordered))
  rw [equality] at compared
  exact (compared.trans (power_tail center radius number positive)).trans
    (by nlinarith [decay_nonnegative (4^number*radius)])

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformTail
