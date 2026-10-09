import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions.Tensor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
open Collision Propagation.Producer Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem partial_swap_error {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (a b c d : ℝ) :
    ‖(partialSwap a b : JointMatrix ι)-partialSwap c d‖ ≤ |a-c|+|b-d| := by
  have split : (partialSwap a b : JointMatrix ι)-partialSwap c d=
      ((a-c : ℝ) : ℂ) • (1 : JointMatrix ι)-(Complex.I*((b-d : ℝ) : ℂ)) • swapOperator := by
    ext i j
    simp only [partialSwap,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    push_cast
    ring
  rw [split]
  apply (norm_sub_le _ _).trans
  simp only [norm_smul,norm_one,swap_norm,mul_one,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,le_refl]

def nativeExchangePolynomial : JointMatrix PairController := partialSwap cosineHat sineHat
def weakExchangePolynomial : JointMatrix PairController := partialSwap sineHat cosineHat

theorem native_exchange_polynomial_error :
    ‖(Exchange.exchangeUnitary (ι := PairController) (Native.sourceCoupling*(nativeClockStep : ℝ)) : JointMatrix PairController)-nativeExchangePolynomial‖ ≤ (2/10^18 : ℝ) := by
  have angle : Native.sourceCoupling*(nativeClockStep : ℝ)=BasisInverse.actualAngle := Native.sourceCoupling_clock
  rw [angle]
  have paid : |Real.cos BasisInverse.actualAngle-cosineHat| ≤ (1/10^18 : ℝ) ∧
      |Real.sin BasisInverse.actualAngle-sineHat| ≤ (1/10^18 : ℝ) := source_polynomial_error
  exact (partial_swap_error (ι := PairController) (Real.cos BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle) cosineHat sineHat).trans
    (by linarith [paid.1,paid.2])

theorem weak_exchange_polynomial_error :
    ‖(Exchange.exchangeUnitary (ι := PairController) (nativeClockStep : ℝ) : JointMatrix PairController)-weakExchangePolynomial‖ ≤ (2/10^18 : ℝ) := by
  have paid : |Real.cos BasisInverse.actualAngle-cosineHat| ≤ (1/10^18 : ℝ) ∧
      |Real.sin BasisInverse.actualAngle-sineHat| ≤ (1/10^18 : ℝ) := source_polynomial_error
  rw [BasisInverse.actualAngle,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub] at paid
  exact (partial_swap_error (ι := PairController) (Real.cos (nativeClockStep : ℝ)) (Real.sin (nativeClockStep : ℝ)) sineHat cosineHat).trans
    (by linarith [paid.1,paid.2])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
