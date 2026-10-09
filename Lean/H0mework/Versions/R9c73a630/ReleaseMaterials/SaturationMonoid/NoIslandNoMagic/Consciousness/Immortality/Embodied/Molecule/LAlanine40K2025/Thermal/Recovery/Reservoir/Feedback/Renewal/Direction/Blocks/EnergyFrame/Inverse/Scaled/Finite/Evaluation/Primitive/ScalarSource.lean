import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Propagation.Producer
open scoped Matrix

def scalarEnergy (a b : Basis) (n : Fin 4) : ℚ :=
  ![Diagonal.energy a+Diagonal.energy b-1,Diagonal.energy a+Diagonal.energy b+3,
    2*Diagonal.energy a+1,2*Diagonal.energy b+1] n

def scalarSeed (energy tick : ℚ) : Scalar.QComplex := (0,-(tick*Diagonal.clock)*energy)

theorem recorded_energy_original (i : Basis) : (Diagonal.energy i : ℝ)=Donor.calculatedEnergy i := by
  simp only [Diagonal.energy,Donor.calculatedEnergy,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat]

theorem scalar_energy_original (a b : Basis) (n : Fin 4) :
    (scalarEnergy a b n : ℂ)=pcValues (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) n := by
  have ca : (Diagonal.energy a : ℂ)=(Donor.calculatedEnergy a : ℂ) := by exact_mod_cast recorded_energy_original a
  have cb : (Diagonal.energy b : ℂ)=(Donor.calculatedEnergy b : ℂ) := by exact_mod_cast recorded_energy_original b
  fin_cases n <;> norm_num [scalarEnergy,pcValues,ca,cb]

theorem scalar_seed_original (energy tick : ℚ) : Scalar.value (scalarSeed energy tick)=
    ((((tick : ℝ)*(nativeClockStep : ℝ) : ℝ) : ℂ)*(-Complex.I))*(energy : ℂ) := by
  simp only [Scalar.value,scalarSeed,Rat.cast_zero,zero_add,Rat.cast_neg,Rat.cast_mul]
  rw [Diagonal.clock_original]
  push_cast
  ring

theorem original_scalar_polynomial (a b : Basis) (n : Fin 4) (tick : ℚ) :
    Scalar.value (Scalar.polynomial (scalarSeed (scalarEnergy a b n) tick) 14)=
      ordinaryPCValues a b ((tick : ℝ)*(nativeClockStep : ℝ)) n := by
  rw [Scalar.value_polynomial,scalar_seed_original,scalar_energy_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
