import H0mework.Physics.LowEnergy.LightModes.Wave
import H0mework.Physics.SpinPair.Parameters

/-! The source time and momentum units are read from the original lapse and
spin scale. All four branches keep that same physical clock. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightModes
open Stage9C.Material.SpinPair Filter Topology
noncomputable section

def physicalExponent (branch : Branch) (q : ℝ) : ℂ :=
  (lapse*spinScale : ℝ)*sourceWave branch q

def nativeSlope : Branch → ℝ
  | .vectorReal => -18/25
  | .vectorPhase => -594/1675
  | .axialPhase => 1/3
  | .quadraticPair => -3/20

theorem native_coefficient (branch : Branch) :
    ((lapse*spinScale : ℝ) : ℂ)^2/(spinScale : ℂ)^(2*sourcePower branch)*
      ((sourceRoot branch).center : ℂ)=(nativeSlope branch : ℂ) := by
  have n2 : (lapse : ℂ)^2=(54/125 : ℂ) := by rw [← Complex.ofReal_pow,lapse_sq]; norm_num
  have s2 : (spinScale : ℂ)^2=2 := by rw [← Complex.ofReal_pow,spinScale_sq]; norm_num
  have s4 : (spinScale : ℂ)^4=4 := by
    calc
      _ = ((spinScale : ℂ)^2)^2 := by ring
      _ = 4 := by rw [s2]; norm_num
  cases branch <;> norm_num [sourceRoot,sourcePower,nativeSlope,Complex.ofReal_mul,mul_pow,n2,s2,s4]

theorem source_native_leading (branch : Branch) :
    Tendsto (fun q : ℝ => (physicalExponent branch q)^2/((spinScale*q : ℝ) : ℂ)^(2*sourcePower branch))
      (𝓝[≠] 0) (𝓝 (nativeSlope branch : ℂ)) := by
  have generated := (source_wave_leading branch).const_mul
    (((lapse*spinScale : ℝ) : ℂ)^2/(spinScale : ℂ)^(2*sourcePower branch))
  rw [native_coefficient] at generated
  convert! generated using 1
  funext q
  simp only [physicalExponent,Complex.ofReal_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

theorem source_native_nonzero (branch : Branch) (q : ℝ) (nonzero : q≠0) : physicalExponent branch q≠0 := by
  unfold physicalExponent
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero lapse_pos.ne' spinScale_pos.ne'))
    (source_wave_nonzero branch q nonzero)

theorem source_two_time_roots (branch : Branch) (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    sourceFactor branch ((sourceWave branch q)^2) ((q : ℂ)^2)=0 ∧
    sourceFactor branch ((-sourceWave branch q)^2) ((q : ℂ)^2)=0 ∧
      sourceWave branch q≠ -sourceWave branch q := by
  refine ⟨source_wave_on_shell branch q small,?_,?_⟩
  · simpa only [neg_sq] using source_wave_on_shell branch q small
  · intro same
    have twice : (2 : ℂ)*sourceWave branch q=0 := by linear_combination same
    have zero := (mul_eq_zero.mp twice).resolve_left (by norm_num)
    exact source_wave_nonzero branch q nonzero zero

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightModes
