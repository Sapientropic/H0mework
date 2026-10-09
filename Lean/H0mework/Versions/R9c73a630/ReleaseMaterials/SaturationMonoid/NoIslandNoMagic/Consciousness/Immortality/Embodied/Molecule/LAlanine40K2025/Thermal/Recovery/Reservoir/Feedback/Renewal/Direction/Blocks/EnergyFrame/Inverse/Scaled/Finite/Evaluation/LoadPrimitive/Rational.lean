import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Coefficients
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.ScalarSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open scoped Matrix BigOperators

def powerQ (s d : ℚ) : Nat → Fin 3 → ℚ
  | 0 => ![1,0,0]
  | n+1 => let f := powerQ s d n
    ![s*f 0,f 0+s*f 1+(d^2+1)*f 2,f 1+s*f 2]

def polynomialQ (s d : ℚ) (z : Scalar.QComplex) : Nat → Fin 3 → Scalar.QComplex
  | 0 => fun _ => (0,0)
  | n+1 => fun k => polynomialQ s d z n k+((n.factorial : ℚ)⁻¹*powerQ s d n k) • Scalar.power z n

theorem powerQ_cast (s d : ℚ) (n : Nat) (k : Fin 3) :
    (powerQ s d n k : ℂ)=coefficientPower (s : ℂ) (d : ℂ) n k := by
  induction n generalizing k with
  | zero => fin_cases k <;> simp [powerQ,coefficientPower]
  | succ n ih => fin_cases k <;> simp [powerQ,coefficientPower,ih]

theorem polynomialQ_value (s d : ℚ) (z : Scalar.QComplex) (n : Nat) (k : Fin 3) :
    Scalar.value (polynomialQ s d z n k)=coefficientPolynomial (s : ℂ) (d : ℂ) (Scalar.value z) n k := by
  induction n with
  | zero => simp [polynomialQ,Scalar.value,coefficientPolynomial]
  | succ n ih =>
    rw [polynomialQ,Scalar.value_add,Scalar.value_smul,Scalar.value_power,ih]
    simp only [coefficientPolynomial,Finset.sum_range_succ,Rat.cast_mul,Rat.cast_inv,Rat.cast_natCast,powerQ_cast]
    ring

theorem coefficient_power_zero (s d : ℂ) (n : Nat) : coefficientPower s d n 0=s^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coefficientPower,ih,pow_succ,mul_comm]

theorem coefficient_polynomial_zero (s d z : ℂ) (n : Nat) :
    coefficientPolynomial s d z n 0=Primitive.scalarPolynomial (z*s) n := by
  simp only [coefficientPolynomial,Primitive.scalarPolynomial,coefficient_power_zero,mul_pow,mul_assoc]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
