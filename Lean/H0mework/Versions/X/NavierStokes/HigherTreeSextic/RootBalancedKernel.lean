import H0mework.Versions.X.NavierStokes.HigherTreeSextic.RootBalancedSum
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.CombKernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticRootBalancedKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeUnheatedSexticLatticePower NativeUnheatedTriadDepthKernel
open NativeUnheatedSexticCombKernel (energy energy_subset coefficient coefficient_nonnegative)
noncomputable section
variable {nu : Viscosity}
abbrev Index := NativeUnheatedQuarticAllSlots.Index

def originalLeaf (leaf : Fin 2) : Fin 4 := ⟨leaf.val, by omega⟩
def first (leaf : Fin 2) (wave : IntegerWavevector) (index : Index) : IntegerWavevector := if leaf=0 then wave-index.1.1-index.1.2 else index.1.2
def left (index : Index) : IntegerWavevector := index.2
def right (index : Index) : IntegerWavevector := index.1.1-index.2

theorem remaining_waves (leaf : Fin 2) (wave : IntegerWavevector) (i j outside l m : Coordinate)
    (index : Index) (number : Fin 3) :
    (NativeUnheatedQuarticAllSlots.slots 2 wave i j outside l m index
      ((originalLeaf leaf).succAbove number)).1 = ![first leaf wave index,left index,right index] number := by
  fin_cases leaf <;> fin_cases number <;> rfl

theorem parent_sum (index : Index) : left index+right index = index.1.1 := by
  unfold left right
  abel

theorem triad_lower (leaf : Fin 2) (wave : IntegerWavevector) (index : Index) :
    (NativeUnheatedQuinticKernel.parentRate nu wave index)⁻¹ ≤
      5*(floor nu)⁻¹*(mass index.1.1+mass (first leaf wave index))⁻¹ := by
  let waves : Fin 3 → IntegerWavevector := ![index.1.2,wave-index.1.1-index.1.2,index.1.1]
  have positive := add_pos (mass_positive index.1.1) (mass_positive (first leaf wave index))
  have lower : mass index.1.1+mass (first leaf wave index) ≤ ∑ number : Fin 3, mass (waves number) := by
    rw [Fin.sum_univ_three]
    change _ ≤ mass index.1.2+mass (wave-index.1.1-index.1.2)+mass index.1.1
    unfold first
    split_ifs <;> linarith [mass_positive index.1.2, mass_positive (wave-index.1.1-index.1.2)]
  have paid := energy_subset (nu := nu) waves _ positive lower
  have same : energy nu waves = NativeUnheatedQuinticKernel.parentRate nu wave index := by
    simp only [energy, Fin.sum_univ_three, waves, NativeUnheatedQuinticKernel.parentRate,
      NativeUnheatedQuinticKernel.parents, NativeUnheatedTriadKernel.triadDecay]
  rw [same] at paid
  norm_num only at paid
  exact paid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num)
    (inv_nonneg.mpr (floor_positive nu).le)) (inv_nonneg.mpr positive.le))

theorem quartic_lower (leaf : Fin 2) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) :
    (NativeUnheatedQuarticPrimitiveKernel.rate nu 2 wave i j outside l m index)⁻¹ ≤
      5*(floor nu)⁻¹*(mass (left index)+mass (right index)+mass (first leaf wave index))⁻¹ := by
  let old := NativeUnheatedQuarticAllSlots.slots 2 wave i j outside l m index
  have lower : mass (left index)+mass (right index)+mass (first leaf wave index) ≤ ∑ number : Fin 4, mass (old number).1 := by
    rw [Fin.sum_univ_succAbove _ (originalLeaf leaf), Fin.sum_univ_three]
    dsimp only [old]
    rw [remaining_waves leaf wave i j outside l m index 0,
      remaining_waves leaf wave i j outside l m index 1, remaining_waves leaf wave i j outside l m index 2]
    change _ ≤ mass (old (originalLeaf leaf)).1+(mass (first leaf wave index)+mass (left index)+mass (right index))
    linarith [mass_positive (old (originalLeaf leaf)).1]
  have paid := energy_subset (nu := nu) (fun number => (old number).1) _
    (add_pos (add_pos (mass_positive _) (mass_positive _)) (mass_positive _)) lower
  have same : energy nu (fun number => (old number).1) = NativeUnheatedQuarticPrimitiveKernel.rate nu 2 wave i j outside l m index := by
    rw [energy, Fin.sum_univ_four]
    rfl
  simpa only [same, show ((4 : ℕ) : ℝ)+1=5 by norm_num] using paid

private theorem fourth_root (x : ℝ) (positive : 0 ≤ x) : (x^(1/4 : ℝ))^4 = x := by
  rw [← Real.rpow_mul_natCast positive]
  norm_num

theorem kernel_bound (leaf : Fin 2) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) :
    NativeUnheatedSexticCollapse.bound nu 2 wave i j outside l m index ≤ coefficient nu*
      NativeUnheatedSexticRootBalancedSum.profile (first leaf wave index) (left index) (right index) := by
  have oldNonnegative := NativeUnheatedSexticCollapse.bound_nonnegative nu 2 wave i j outside l m index
  have profile0 := NativeUnheatedSexticRootBalancedSum.profile_nonnegative (first leaf wave index) (left index) (right index)
  apply (pow_le_pow_iff_left₀ oldNonnegative (mul_nonneg (coefficient_nonnegative nu) profile0) (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [NativeUnheatedSexticCollapse.bound, fourth_root _ (by
    positivity [nu.coeff_pos, NativeUnheatedQuarticPrimitiveKernel.rate_nonnegative nu 2 wave i j outside l m index]),
    mul_pow, coefficient, fourth_root _ (by positivity [nu.coeff_pos, floor_positive nu]),
    NativeUnheatedSexticRootBalancedSum.profile_fourth, parent_sum]
  have d := NativeUnheatedSexticCombKernel.pair_lower (nu := nu) 0 wave index
  have t := triad_lower (nu := nu) leaf wave index
  have s := quartic_lower (nu := nu) leaf wave i j outside l m index
  have u0 : 0 ≤ nu.coeff⁻¹ := inv_nonneg.mpr nu.coeff_pos.le
  have v0 : 0 ≤ (floor nu)⁻¹ := inv_nonneg.mpr (floor_positive nu).le
  have d0 : 0 ≤ (NativeUnheatedQuinticKernel.pairRate nu wave index)⁻¹ := inv_nonneg.mpr
    (mul_nonneg nu.coeff_pos.le (add_nonneg (NativeUnheatedTriadKernel.multiplier_nonnegative _) (NativeUnheatedTriadKernel.multiplier_nonnegative _)))
  have t0 : 0 ≤ (NativeUnheatedQuinticKernel.parentRate nu wave index)⁻¹ := inv_nonneg.mpr (NativeUnheatedTriadKernel.triad_nonnegative (nu := nu) _ _ _)
  have s0 := inv_nonneg.mpr (NativeUnheatedQuarticPrimitiveKernel.rate_nonnegative nu 2 wave i j outside l m index)
  calc
    _ ≤ 8*nu.coeff⁻¹^7*(5*(floor nu)⁻¹*(mass index.1.1)⁻¹)^2*
        (5*(floor nu)⁻¹*(mass index.1.1+mass (first leaf wave index))⁻¹)^2*
        (5*(floor nu)⁻¹*(mass (left index)+mass (right index)+mass (first leaf wave index))⁻¹)^5 := by gcongr
    _ = _ := by
      simp only [NativeUnheatedSexticRowSquare.pairMass, mul_inv_rev, inv_pow, mul_pow]
      ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticRootBalancedKernel
