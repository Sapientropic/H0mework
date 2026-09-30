import H0mework.Versions.X.NavierStokes.HigherTreeSextic.BalancedSum
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.CombKernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticBalancedKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeUnheatedSexticLatticePower NativeUnheatedTriadDepthKernel NativeUnheatedQuinticFiveRows
open NativeUnheatedSexticCombKernel (originalSlot energy energy_subset coefficient coefficient_nonnegative middle)
noncomputable section
variable {nu : Viscosity}
abbrev Index := NativeUnheatedQuarticAllSlots.Index

def originalLeaf (kind : Fin 2) : Fin 4 := kind.succ.succ

def parent (slot : Fin 2) (wave : IntegerWavevector) (index : Index) : IntegerWavevector :=
  if slot=0 then index.1.2 else wave-index.1.1-index.1.2

def left (index : Index) : IntegerWavevector := index.2

def right (slot : Fin 2) (wave : IntegerWavevector) (index : Index) : IntegerWavevector := parent slot wave index-index.2

def remaining (slot kind : Fin 2) (wave : IntegerWavevector) (index : Index) : IntegerWavevector :=
  if kind=0 then index.1.1 else middle slot wave index

theorem pair_sum (slot : Fin 2) (wave : IntegerWavevector) (index : Index) : left index+right slot wave index = parent slot wave index := by
  unfold left right
  abel

theorem old_waves (slot : Fin 2) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) (number : Fin 4) :
    (NativeUnheatedQuarticAllSlots.slots (originalSlot slot) wave i j outside l m index number).1 =
      ![left index,right slot wave index,middle slot wave index,index.1.1] number := by
  fin_cases slot <;> fin_cases number <;> rfl

theorem remaining_waves (slot kind : Fin 2) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) (number : Fin 3) :
    (NativeUnheatedQuarticAllSlots.slots (originalSlot slot) wave i j outside l m index ((originalLeaf kind).succAbove number)).1 =
      ![left index,right slot wave index,remaining slot kind wave index] number := by
  fin_cases slot <;> fin_cases kind <;> fin_cases number <;> rfl

theorem pair_lower (slot kind : Fin 2) (wave : IntegerWavevector) (index : Index) :
    (NativeUnheatedQuinticKernel.pairRate nu wave index)⁻¹ ≤ 5*(floor nu)⁻¹*
      (mass (NativeUnheatedSexticBalancedSum.momentum kind (remaining slot kind wave index) (left index) (right slot wave index)))⁻¹ := by
  let waves : Fin 2 → IntegerWavevector := ![wave-index.1.1,index.1.1]
  have identity : NativeUnheatedSexticBalancedSum.momentum kind (remaining slot kind wave index) (left index) (right slot wave index) =
      if kind=0 then index.1.1 else wave-index.1.1 := by
    rw [NativeUnheatedSexticBalancedSum.momentum, pair_sum]
    by_cases zero : kind=0
    · simp only [zero, if_true, remaining]
    · simp only [if_neg zero, remaining]
      unfold parent middle
      split_ifs <;> abel
  have lower : mass (NativeUnheatedSexticBalancedSum.momentum kind (remaining slot kind wave index) (left index) (right slot wave index)) ≤
      ∑ number : Fin 2, mass (waves number) := by
    rw [identity, Fin.sum_univ_two]
    change mass (if kind=0 then index.1.1 else wave-index.1.1) ≤ mass (wave-index.1.1)+mass index.1.1
    split_ifs <;> linarith [mass_positive (wave-index.1.1), mass_positive index.1.1]
  have paid := energy_subset (nu := nu) waves _ (mass_positive _) lower
  have same : energy nu waves = NativeUnheatedQuinticKernel.pairRate nu wave index := by
    rw [energy, Fin.sum_univ_two]
    change nu.coeff*(integerWaveViscousMultiplier (wave-index.1.1)+integerWaveViscousMultiplier index.1.1) =
      nu.coeff*(integerWaveViscousMultiplier (index.1.2+(wave-index.1.1-index.1.2))+integerWaveViscousMultiplier index.1.1)
    have joined : index.1.2+(wave-index.1.1-index.1.2)=wave-index.1.1 := by abel
    rw [joined]
  rw [same] at paid
  norm_num only at paid
  exact paid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num)
    (inv_nonneg.mpr (floor_positive nu).le)) (inv_nonneg.mpr (mass_positive _).le))

theorem triad_lower (slot kind : Fin 2) (wave : IntegerWavevector) (index : Index) :
    (NativeUnheatedQuinticKernel.parentRate nu wave index)⁻¹ ≤ 5*(floor nu)⁻¹*
      (mass (left index+right slot wave index)+mass (remaining slot kind wave index))⁻¹ := by
  let waves : Fin 3 → IntegerWavevector := ![parent slot wave index,middle slot wave index,index.1.1]
  have positive := add_pos (mass_positive (left index+right slot wave index)) (mass_positive (remaining slot kind wave index))
  have lower : mass (left index+right slot wave index)+mass (remaining slot kind wave index) ≤ ∑ number : Fin 3, mass (waves number) := by
    rw [pair_sum, Fin.sum_univ_three]
    change mass (parent slot wave index)+mass (remaining slot kind wave index) ≤
      mass (parent slot wave index)+mass (middle slot wave index)+mass index.1.1
    unfold remaining
    split_ifs <;> linarith [mass_positive (parent slot wave index), mass_positive (middle slot wave index), mass_positive index.1.1]
  have paid := energy_subset (nu := nu) waves _ positive lower
  have same : energy nu waves = NativeUnheatedQuinticKernel.parentRate nu wave index := by
    rw [energy, Fin.sum_univ_three]
    fin_cases slot
    · rfl
    · change nu.coeff*(integerWaveViscousMultiplier (wave-index.1.1-index.1.2)+integerWaveViscousMultiplier index.1.2+integerWaveViscousMultiplier index.1.1) =
        nu.coeff*(integerWaveViscousMultiplier index.1.2+integerWaveViscousMultiplier (wave-index.1.1-index.1.2)+integerWaveViscousMultiplier index.1.1)
      ring
  rw [same] at paid
  norm_num only at paid
  exact paid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num)
    (inv_nonneg.mpr (floor_positive nu).le)) (inv_nonneg.mpr positive.le))

theorem quartic_lower (slot : Fin 2) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) :
    (NativeUnheatedQuarticPrimitiveKernel.rate nu (originalSlot slot) wave i j outside l m index)⁻¹ ≤
      5*(floor nu)⁻¹*(mass (left index)+mass (right slot wave index))⁻¹ := by
  let old := NativeUnheatedQuarticAllSlots.slots (originalSlot slot) wave i j outside l m index
  have lower : mass (left index)+mass (right slot wave index) ≤ ∑ number : Fin 4, mass (old number).1 := by
    rw [Fin.sum_univ_four]
    dsimp only [old]
    rw [old_waves slot wave i j outside l m index 0, old_waves slot wave i j outside l m index 1,
      old_waves slot wave i j outside l m index 2, old_waves slot wave i j outside l m index 3]
    change _ ≤ mass (left index)+mass (right slot wave index)+mass (middle slot wave index)+mass index.1.1
    linarith [mass_positive (middle slot wave index), mass_positive index.1.1]
  have paid := energy_subset (nu := nu) (fun number => (old number).1) _ (add_pos (mass_positive _) (mass_positive _)) lower
  have same : energy nu (fun number => (old number).1) = NativeUnheatedQuarticPrimitiveKernel.rate nu (originalSlot slot) wave i j outside l m index := by
    rw [energy, Fin.sum_univ_four]
    rfl
  simpa only [same, show ((4 : ℕ) : ℝ)+1=5 by norm_num] using paid

private theorem fourth_root (x : ℝ) (positive : 0 ≤ x) : (x^(1/4 : ℝ))^4=x := by
  rw [← Real.rpow_mul_natCast positive]
  norm_num

theorem kernel_bound (slot kind : Fin 2) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) :
    NativeUnheatedSexticCollapse.bound nu (originalSlot slot) wave i j outside l m index ≤ coefficient nu*
      NativeUnheatedSexticBalancedSum.profile kind (remaining slot kind wave index) (left index) (right slot wave index) := by
  have profile0 := NativeUnheatedSexticBalancedSum.profile_nonnegative kind (remaining slot kind wave index) (left index) (right slot wave index)
  apply (pow_le_pow_iff_left₀ (NativeUnheatedSexticCollapse.bound_nonnegative nu (originalSlot slot) wave i j outside l m index)
    (mul_nonneg (coefficient_nonnegative nu) profile0) (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [NativeUnheatedSexticCollapse.bound, fourth_root _ (by
    positivity [nu.coeff_pos, NativeUnheatedQuarticPrimitiveKernel.rate_nonnegative nu (originalSlot slot) wave i j outside l m index]),
    mul_pow, coefficient, fourth_root _ (by positivity [nu.coeff_pos, floor_positive nu]), NativeUnheatedSexticBalancedSum.profile_fourth]
  have d := pair_lower (nu := nu) slot kind wave index
  have t := triad_lower (nu := nu) slot kind wave index
  have s := quartic_lower (nu := nu) slot wave i j outside l m index
  have u0 : 0 ≤ nu.coeff⁻¹ := inv_nonneg.mpr nu.coeff_pos.le
  have v0 : 0 ≤ (floor nu)⁻¹ := inv_nonneg.mpr (floor_positive nu).le
  have d0 : 0 ≤ (NativeUnheatedQuinticKernel.pairRate nu wave index)⁻¹ := inv_nonneg.mpr
    (mul_nonneg nu.coeff_pos.le (add_nonneg (NativeUnheatedTriadKernel.multiplier_nonnegative _) (NativeUnheatedTriadKernel.multiplier_nonnegative _)))
  have t0 : 0 ≤ (NativeUnheatedQuinticKernel.parentRate nu wave index)⁻¹ := inv_nonneg.mpr (NativeUnheatedTriadKernel.triad_nonnegative (nu := nu) _ _ _)
  have s0 := inv_nonneg.mpr (NativeUnheatedQuarticPrimitiveKernel.rate_nonnegative nu (originalSlot slot) wave i j outside l m index)
  calc
    _ ≤ 8*nu.coeff⁻¹^7*(5*(floor nu)⁻¹*(mass (NativeUnheatedSexticBalancedSum.momentum kind (remaining slot kind wave index) (left index) (right slot wave index)))⁻¹)^2*
        (5*(floor nu)⁻¹*(mass (left index+right slot wave index)+mass (remaining slot kind wave index))⁻¹)^2*
        (5*(floor nu)⁻¹*(mass (left index)+mass (right slot wave index))⁻¹)^5 := by gcongr
    _ = _ := by
      simp only [NativeUnheatedSexticRowSquare.pairMass, mul_inv_rev, inv_pow, mul_pow]
      ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticBalancedKernel
