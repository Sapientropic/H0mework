import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Rational
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.ScalarSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Propagation.Producer
open scoped Matrix BigOperators

def sourceSum (a b : Basis) (offset : ℚ) : ℚ := Diagonal.energy a+Diagonal.energy b+offset

def sourceDelta (a b : Basis) : ℚ := Diagonal.energy a-Diagonal.energy b

def sourcePhase : Scalar.QComplex := (0,-Diagonal.clock)

def sourceCoefficient (a b : Basis) (offset : ℚ) (k : Fin 3) : Scalar.QComplex :=
  polynomialQ (sourceSum a b offset) (sourceDelta a b) sourcePhase 14 k

theorem energy_complex (a : Basis) : (Diagonal.energy a : ℂ)=(Donor.calculatedEnergy a : ℂ) := by
  exact_mod_cast Primitive.recorded_energy_original a

theorem source_sum_value (a b : Basis) (offset : ℚ) :
    (sourceSum a b offset : ℂ)=(Donor.calculatedEnergy a : ℂ)+Donor.calculatedEnergy b+(offset : ℂ) := by
  simp only [sourceSum,Rat.cast_add,energy_complex]

theorem source_delta_value (a b : Basis) :
    (sourceDelta a b : ℂ)=(Donor.calculatedEnergy a : ℂ)-Donor.calculatedEnergy b := by
  simp only [sourceDelta,Rat.cast_sub,energy_complex]

theorem source_phase_value : Scalar.value sourcePhase=((nativeClockStep : ℝ) : ℂ)*(-Complex.I) := by
  have h := Primitive.scalar_seed_original (1 : ℚ) (1 : ℚ)
  simpa only [Primitive.scalarSeed,one_mul,mul_one,sourcePhase,Rat.cast_one,Complex.ofReal_one] using h

theorem original_source_coefficient (a b : Basis) (offset : ℚ) (k : Fin 3) :
    Scalar.value (sourceCoefficient a b offset k)=
      coefficientPolynomial ((Donor.calculatedEnergy a : ℂ)+Donor.calculatedEnergy b+(offset : ℂ))
        ((Donor.calculatedEnergy a : ℂ)-Donor.calculatedEnergy b)
        (((nativeClockStep : ℝ) : ℂ)*(-Complex.I)) 14 k := by
  rw [sourceCoefficient,polynomialQ_value,source_sum_value,source_delta_value,source_phase_value]

theorem source_zero_scalar (a b : Basis) (offset : ℚ) :
    Scalar.value (sourceCoefficient a b offset 0)=
      Scalar.value (Scalar.polynomial (Primitive.scalarSeed (sourceSum a b offset) 1) 14) := by
  rw [sourceCoefficient,polynomialQ_value,coefficient_polynomial_zero,Scalar.value_polynomial]
  have same : Scalar.value (Primitive.scalarSeed (sourceSum a b offset) 1)=
      Scalar.value sourcePhase*(sourceSum a b offset : ℂ) := by
    simp only [Scalar.value,Primitive.scalarSeed,sourcePhase,one_mul,Rat.cast_zero,zero_add,Rat.cast_neg,Rat.cast_mul]
    ring
  rw [same]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
