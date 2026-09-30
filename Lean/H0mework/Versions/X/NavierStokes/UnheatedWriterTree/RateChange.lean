import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Leaf
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.NormalForm

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeRateChange
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeUnheatedTreeTime NativeUnheatedTriadChannels
noncomputable section
variable {nu : Viscosity} {n : ℕ}

def crossRate (nu : Viscosity) (first last : IntegerWavevector) : ℝ :=
  2*nu.coeff*(2*Real.pi)^2*∑ coordinate : Coordinate, (first coordinate : ℝ)*(last coordinate : ℝ)

theorem multiplier_split (wave inside : IntegerWavevector) :
    integerWaveViscousMultiplier wave = integerWaveViscousMultiplier inside +
      integerWaveViscousMultiplier (wave-inside) +
        2*(2*Real.pi)^2*(∑ coordinate : Coordinate, (inside coordinate : ℝ)*((wave-inside) coordinate : ℝ)) := by
  have rows (coordinate : Coordinate) : (wave coordinate : ℝ)^2 = (inside coordinate : ℝ)^2 +
      ((wave-inside) coordinate : ℝ)^2+2*((inside coordinate : ℝ)*((wave-inside) coordinate : ℝ)) := by
    simp only [Pi.sub_apply, Int.cast_sub]
    ring
  simp only [integerWaveViscousMultiplier, integerWaveNormSq]
  conv_lhs => arg 2; arg 2; ext coordinate; rw [rows coordinate]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem rate_split (slots : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate) (inside : IntegerWavevector) :
    sumRate nu slots = sumRate nu (NativeUnheatedTreeLeaf.slots slots leaf p q inside) +
      crossRate nu inside ((slots leaf).1-inside) := by
  unfold sumRate
  rw [Fin.sum_univ_succAbove _ leaf]
  simp only [Fin.sum_univ_succ, NativeUnheatedTreeLeaf.slots, Fin.cons_zero, Fin.cons_succ]
  rw [multiplier_split (slots leaf).1 inside]
  unfold crossRate
  ring

theorem parent_zero_of_split_rate_zero (slots : Fin (n+1) → Slot) (leaf : Fin (n+1))
    (p q : Coordinate) (inside : IntegerWavevector)
    (zero : sumRate nu (NativeUnheatedTreeLeaf.slots slots leaf p q inside) = 0) : (slots leaf).1 = 0 := by
  have first := NativeUnheatedTreeOutput.rate_zero_wave _ zero (0 : Fin (n+2))
  have second := NativeUnheatedTreeOutput.rate_zero_wave _ zero (1 : Fin (n+2))
  change inside = 0 at first
  change (slots leaf).1-inside = 0 at second
  simpa only [first, sub_zero] using second

theorem pressure_zero (p q response : Coordinate) : pressure 0 p q response = 0 := by
  apply norm_eq_zero.mp
  have paid := pressure_bound 0 p q response
  have zero : integerWaveViscousMultiplier 0 = 0 := by simp [integerWaveViscousMultiplier, integerWaveNormSq]
  exact le_antisymm (by simpa only [zero, Real.sqrt_zero] using paid) (norm_nonneg _)

theorem inverse_change (slots : Fin (n+1) → Slot) (leaf : Fin (n+1)) (z : ℂ)
    (p q : Coordinate) (inside : IntegerWavevector) :
    ((sumRate nu slots)⁻¹-(sumRate nu (NativeUnheatedTreeLeaf.slots slots leaf p q inside))⁻¹) •
      NativeUnheatedTreeLeaf.kernel z slots leaf p q =
    (-(crossRate nu inside ((slots leaf).1-inside))*
      (sumRate nu slots*sumRate nu (NativeUnheatedTreeLeaf.slots slots leaf p q inside))⁻¹) •
      NativeUnheatedTreeLeaf.kernel z slots leaf p q := by
  by_cases oldZero : sumRate nu slots = 0
  · have parent := NativeUnheatedTreeOutput.rate_zero_wave slots oldZero leaf
    simp only [NativeUnheatedTreeLeaf.kernel, parent, pressure_zero, mul_zero, smul_zero]
  by_cases newZero : sumRate nu (NativeUnheatedTreeLeaf.slots slots leaf p q inside) = 0
  · have parent := parent_zero_of_split_rate_zero slots leaf p q inside newZero
    simp only [NativeUnheatedTreeLeaf.kernel, parent, pressure_zero, mul_zero, smul_zero]
  congr 1
  have same := rate_split (nu := nu) slots leaf p q inside
  field_simp
  nlinarith

theorem normalizer_commutator (slots : Fin (n+1) → Slot) (leaf : Fin (n+1)) (z : ℂ)
    (p q : Coordinate) (inside : IntegerWavevector) :
    NativeUnheatedTreeLeaf.kernel (NativeUnheatedTreeNormalForm.normalizer nu slots z) slots leaf p q -
      NativeUnheatedTreeNormalForm.normalizer nu (NativeUnheatedTreeLeaf.slots slots leaf p q inside)
        (NativeUnheatedTreeLeaf.kernel z slots leaf p q) =
    (-(crossRate nu inside ((slots leaf).1-inside))*
      (sumRate nu slots*sumRate nu (NativeUnheatedTreeLeaf.slots slots leaf p q inside))⁻¹) •
      NativeUnheatedTreeLeaf.kernel z slots leaf p q := by
  rw [NativeUnheatedTreeLeaf.kernel, NativeUnheatedTreeNormalForm.normalizer, smul_mul_assoc]
  change (sumRate nu slots)⁻¹ • NativeUnheatedTreeLeaf.kernel z slots leaf p q -
    (sumRate nu (NativeUnheatedTreeLeaf.slots slots leaf p q inside))⁻¹ • NativeUnheatedTreeLeaf.kernel z slots leaf p q = _
  rw [← sub_smul, inverse_change]

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeRateChange
