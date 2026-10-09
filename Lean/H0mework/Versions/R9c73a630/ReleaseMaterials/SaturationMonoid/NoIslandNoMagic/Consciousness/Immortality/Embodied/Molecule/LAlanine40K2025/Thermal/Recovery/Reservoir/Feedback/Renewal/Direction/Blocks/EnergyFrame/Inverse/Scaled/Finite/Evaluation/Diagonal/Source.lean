import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Scalar

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
open Propagation.Interface Propagation.Producer
open scoped Matrix Matrix.Norms.L2Operator

def clock : ℚ := 15625000000000/36212777618028463
def systemTime : ℚ := 1+2*clock
def energy (i : Basis) : ℚ := (energies[i.val]! : ℚ)/10^15

def activeSeed (i : Basis) : Scalar.QComplex := (0,-energy i*systemTime/1024)
def gibbsSeed (i : Basis) : Scalar.QComplex := (-energy i/128,0)

theorem clock_original : clock=nativeClockStep := nativeClockStep_exact.symm

theorem time_original : (systemTime : ℝ)=Input.systemTime := by
  rw [systemTime,clock_original,Input.systemTime,Preparation.collisionCurrentTime]
  push_cast
  ring

theorem energy_original (i : Basis) : (energy i : ℂ)=E i i := by
  simp [energy,E]

theorem active_seed_original (i : Basis) : Scalar.value (activeSeed i)=
    (Input.systemTime/1024) • (-Complex.I*E i i) := by
  simp only [activeSeed,Scalar.value,Rat.cast_zero,zero_add,Rat.cast_div,Rat.cast_mul,Rat.cast_neg,Rat.cast_ofNat]
  rw [energy_original]
  have time : (systemTime : ℂ)=(Input.systemTime : ℂ) := by exact_mod_cast time_original
  rw [time]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

theorem gibbs_seed_original (i : Basis) : Scalar.value (gibbsSeed i)=
    (1/128 : ℝ) • (-E i i) := by
  simp only [gibbsSeed,Scalar.value,Rat.cast_zero,mul_zero,add_zero,Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat]
  rw [energy_original]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
