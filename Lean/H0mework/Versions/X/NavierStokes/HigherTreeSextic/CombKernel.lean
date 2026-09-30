import H0mework.Versions.X.NavierStokes.HigherTreeSextic.Collapse
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.CriticalSum

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticCombKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeUnheatedSexticLatticePower NativeUnheatedTriadDepthKernel NativeUnheatedQuinticFiveRows
noncomputable section
variable {nu : Viscosity}

def energy {n : ℕ} (nu : Viscosity) (waves : Fin n → IntegerWavevector) : ℝ :=
  nu.coeff*∑ number : Fin n, integerWaveViscousMultiplier (waves number)

theorem energy_inverse {n : ℕ} (waves : Fin n → IntegerWavevector) :
    (energy nu waves)⁻¹ ≤ ((n : ℝ)+1)*(floor nu)⁻¹*(∑ number : Fin n, mass (waves number))⁻¹ := by
  let total := ∑ number : Fin n, integerWaveNormSq (waves number)
  have original : energy nu waves = floor nu*total := by
    simp only [energy, floor, integerWaveViscousMultiplier, ← Finset.mul_sum, total, mul_assoc]
  by_cases zero : total=0
  · rw [original, zero, mul_zero, inv_zero]
    have nonnegative : 0 ≤ ∑ number : Fin n, mass (waves number) := Finset.sum_nonneg fun number _ => (mass_positive _).le
    positivity [floor_positive nu]
  · have total0 : 0 ≤ total := Finset.sum_nonneg fun number _ => integerWaveNormSq_nonneg _
    have existsWave : ∃ number : Fin n, waves number ≠ 0 := by
      by_contra empty
      push Not at empty
      apply zero
      simp only [total, empty, integerWaveNormSq, Pi.zero_apply, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, Finset.sum_const_zero]
    obtain ⟨number, nonzero⟩ := existsWave
    have atLeast : 1 ≤ total := (one_le_integerWaveNormSq _ nonzero).trans
      (Finset.single_le_sum (fun other _ => integerWaveNormSq_nonneg (waves other)) (Finset.mem_univ number))
    have sumSame : (∑ number : Fin n, mass (waves number)) = (n : ℝ)+total := by
      simp only [mass, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, total]
    have sumPos : 0 < ∑ number : Fin n, mass (waves number) := by rw [sumSame]; positivity
    have lower : (∑ number : Fin n, mass (waves number))/((n : ℝ)+1) ≤ total := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)+1)).mpr
      rw [sumSame]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have paid := inv_anti₀ (mul_pos (floor_positive nu) (div_pos sumPos (by positivity)))
      (mul_le_mul_of_nonneg_left lower (floor_positive nu).le)
    rw [original]
    exact paid.trans_eq (by rw [mul_inv_rev, inv_div, div_eq_mul_inv]; ring)

theorem energy_subset {n : ℕ} (waves : Fin n → IntegerWavevector) (target : ℝ) (positive : 0 < target)
    (lower : target ≤ ∑ number : Fin n, mass (waves number)) :
    (energy nu waves)⁻¹ ≤ ((n : ℝ)+1)*(floor nu)⁻¹*target⁻¹ :=
  (energy_inverse waves).trans (mul_le_mul_of_nonneg_left (inv_anti₀ positive lower) (by positivity [floor_positive nu]))

def originalSlot (slot : Fin 2) : Fin 3 := ⟨slot.val, by omega⟩
def originalLeaf (leaf : Fin 2) : Fin 4 := ⟨leaf.val, by omega⟩

def middle (slot : Fin 2) (wave : IntegerWavevector) (index : NativeUnheatedQuarticAllSlots.Index) : IntegerWavevector :=
  if slot=0 then wave-index.1.1-index.1.2 else index.1.2

def first (slot leaf : Fin 2) (wave : IntegerWavevector) (index : NativeUnheatedQuarticAllSlots.Index) : IntegerWavevector :=
  if leaf=0 then (if slot=0 then index.1.2 else wave-index.1.1-index.1.2)-index.2 else index.2

theorem remaining_waves (slot leaf : Fin 2) (wave : IntegerWavevector) (i j outside l m : Coordinate)
    (index : NativeUnheatedQuarticAllSlots.Index) (number : Fin 3) :
    (NativeUnheatedQuarticAllSlots.slots (originalSlot slot) wave i j outside l m index
      ((originalLeaf leaf).succAbove number)).1 = ![first slot leaf wave index, middle slot wave index, index.1.1] number := by
  fin_cases slot <;> fin_cases leaf <;> fin_cases number <;> rfl

theorem pair_lower (_slot : Fin 2) (wave : IntegerWavevector) (index : NativeUnheatedQuarticAllSlots.Index) :
    (NativeUnheatedQuinticKernel.pairRate nu wave index)⁻¹ ≤ 5*(floor nu)⁻¹*(mass index.1.1)⁻¹ := by
  let waves : Fin 2 → IntegerWavevector := ![wave-index.1.1,index.1.1]
  have paid := energy_subset (nu := nu) waves (mass index.1.1) (mass_positive _) (by
    rw [Fin.sum_univ_two]
    exact le_add_of_nonneg_left (mass_positive _).le)
  have same : energy nu waves = NativeUnheatedQuinticKernel.pairRate nu wave index := by
    rw [energy, Fin.sum_univ_two]
    change nu.coeff*(integerWaveViscousMultiplier (wave-index.1.1)+integerWaveViscousMultiplier index.1.1) =
      nu.coeff*(integerWaveViscousMultiplier (index.1.2+(wave-index.1.1-index.1.2))+integerWaveViscousMultiplier index.1.1)
    have joined : index.1.2+(wave-index.1.1-index.1.2)=wave-index.1.1 := by abel
    rw [joined]
  rw [same] at paid
  norm_num only at paid
  exact paid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num)
    (inv_nonneg.mpr (floor_positive nu).le)) (inv_nonneg.mpr (mass_positive index.1.1).le))

theorem triad_lower (slot : Fin 2) (wave : IntegerWavevector) (index : NativeUnheatedQuarticAllSlots.Index) :
    (NativeUnheatedQuinticKernel.parentRate nu wave index)⁻¹ ≤
      5*(floor nu)⁻¹*(mass (middle slot wave index)+mass index.1.1)⁻¹ := by
  let waves : Fin 3 → IntegerWavevector := ![index.1.2,wave-index.1.1-index.1.2,index.1.1]
  have positive := add_pos (mass_positive (middle slot wave index)) (mass_positive index.1.1)
  have lower : mass (middle slot wave index)+mass index.1.1 ≤ ∑ number : Fin 3, mass (waves number) := by
    rw [Fin.sum_univ_three]
    change mass (middle slot wave index)+mass index.1.1 ≤
      mass index.1.2+mass (wave-index.1.1-index.1.2)+mass index.1.1
    by_cases zero : slot=0
    · simp only [middle, if_pos zero]
      linarith [mass_positive index.1.2]
    · simp only [middle, if_neg zero]
      linarith [mass_positive (wave-index.1.1-index.1.2)]
  have paid := energy_subset (nu := nu) waves _ positive lower
  have same : energy nu waves = NativeUnheatedQuinticKernel.parentRate nu wave index := by
    simp only [energy, Fin.sum_univ_three, waves, NativeUnheatedQuinticKernel.parentRate,
      NativeUnheatedQuinticKernel.parents, NativeUnheatedTriadKernel.triadDecay]
  rw [same] at paid
  norm_num only at paid
  exact paid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num)
    (inv_nonneg.mpr (floor_positive nu).le)) (inv_nonneg.mpr positive.le))

theorem quartic_lower (slot leaf : Fin 2) (wave : IntegerWavevector) (i j outside l m : Coordinate)
    (index : NativeUnheatedQuarticAllSlots.Index) :
    (NativeUnheatedQuarticPrimitiveKernel.rate nu (originalSlot slot) wave i j outside l m index)⁻¹ ≤
      5*(floor nu)⁻¹*(mass (first slot leaf wave index)+mass (middle slot wave index)+mass index.1.1)⁻¹ := by
  let old := NativeUnheatedQuarticAllSlots.slots (originalSlot slot) wave i j outside l m index
  have lower : mass (first slot leaf wave index)+mass (middle slot wave index)+mass index.1.1 ≤ ∑ number : Fin 4, mass (old number).1 := by
    rw [Fin.sum_univ_succAbove _ (originalLeaf leaf), Fin.sum_univ_three]
    dsimp only [old]
    rw [remaining_waves slot leaf wave i j outside l m index 0,
      remaining_waves slot leaf wave i j outside l m index 1, remaining_waves slot leaf wave i j outside l m index 2]
    change _ ≤ mass (old (originalLeaf leaf)).1+(mass (first slot leaf wave index)+mass (middle slot wave index)+mass index.1.1)
    exact le_add_of_nonneg_left (mass_positive _).le
  have paid := energy_subset (nu := nu) (fun number => (old number).1) _
    (add_pos (add_pos (mass_positive _) (mass_positive _)) (mass_positive _)) lower
  have same : energy nu (fun number => (old number).1) = NativeUnheatedQuarticPrimitiveKernel.rate nu (originalSlot slot) wave i j outside l m index := by
    rw [energy, Fin.sum_univ_four]
    rfl
  simpa only [same, show ((4 : ℕ) : ℝ)+1=5 by norm_num] using paid

def coefficient (nu : Viscosity) : ℝ := (8*nu.coeff⁻¹^7*(5*(floor nu)⁻¹)^9)^(1/4 : ℝ)

theorem coefficient_nonnegative (nu : Viscosity) : 0 ≤ coefficient nu := Real.rpow_nonneg (by positivity [nu.coeff_pos, floor_positive nu]) _

private theorem fourth_root (x : ℝ) (positive : 0 ≤ x) : (x^(1/4 : ℝ))^4 = x := by
  rw [← Real.rpow_mul_natCast positive]
  norm_num

theorem kernel_bound (slot leaf : Fin 2) (wave : IntegerWavevector) (i j outside l m : Coordinate)
    (index : NativeUnheatedQuarticAllSlots.Index) :
    NativeUnheatedSexticCollapse.bound nu (originalSlot slot) wave i j outside l m index ≤ coefficient nu*
      NativeUnheatedSexticCriticalSum.profile (first slot leaf wave index) (middle slot wave index) index.1.1 := by
  have oldNonnegative := NativeUnheatedSexticCollapse.bound_nonnegative nu (originalSlot slot) wave i j outside l m index
  have profile0 := NativeUnheatedSexticCriticalSum.profile_nonnegative (first slot leaf wave index) (middle slot wave index) index.1.1
  apply (pow_le_pow_iff_left₀ oldNonnegative (mul_nonneg (coefficient_nonnegative nu) profile0) (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [NativeUnheatedSexticCollapse.bound, fourth_root _ (by
    positivity [nu.coeff_pos, NativeUnheatedQuarticPrimitiveKernel.rate_nonnegative nu (originalSlot slot) wave i j outside l m index]),
    mul_pow, coefficient, fourth_root _ (by positivity [nu.coeff_pos, floor_positive nu]), NativeUnheatedSexticCriticalSum.profile_fourth]
  have d := pair_lower (nu := nu) slot wave index
  have t := triad_lower (nu := nu) slot wave index
  have s := quartic_lower (nu := nu) slot leaf wave i j outside l m index
  have u0 : 0 ≤ nu.coeff⁻¹ := inv_nonneg.mpr nu.coeff_pos.le
  have v0 : 0 ≤ (floor nu)⁻¹ := inv_nonneg.mpr (floor_positive nu).le
  have d0 : 0 ≤ (NativeUnheatedQuinticKernel.pairRate nu wave index)⁻¹ := inv_nonneg.mpr
    (mul_nonneg nu.coeff_pos.le (add_nonneg (NativeUnheatedTriadKernel.multiplier_nonnegative _) (NativeUnheatedTriadKernel.multiplier_nonnegative _)))
  have t0 : 0 ≤ (NativeUnheatedQuinticKernel.parentRate nu wave index)⁻¹ := inv_nonneg.mpr (NativeUnheatedTriadKernel.triad_nonnegative (nu := nu) _ _ _)
  have s0 := inv_nonneg.mpr (NativeUnheatedQuarticPrimitiveKernel.rate_nonnegative nu (originalSlot slot) wave i j outside l m index)
  calc
    _ ≤ 8*nu.coeff⁻¹^7*(5*(floor nu)⁻¹*(mass index.1.1)⁻¹)^2*
        (5*(floor nu)⁻¹*(mass (middle slot wave index)+mass index.1.1)⁻¹)^2*
        (5*(floor nu)⁻¹*(mass (first slot leaf wave index)+mass (middle slot wave index)+mass index.1.1)⁻¹)^5 := by gcongr
    _ = _ := by
      simp only [NativeUnheatedSexticRowSquare.pairMass, mul_inv_rev, inv_pow, mul_pow]
      ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticCombKernel
