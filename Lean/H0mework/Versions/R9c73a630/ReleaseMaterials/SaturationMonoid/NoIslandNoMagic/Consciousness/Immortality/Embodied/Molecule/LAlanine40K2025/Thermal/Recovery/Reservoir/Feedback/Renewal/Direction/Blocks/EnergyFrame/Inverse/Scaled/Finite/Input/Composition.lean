import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Factorization

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exchange_shared_commute (U : Matrix.unitaryGroup ι ℂ) (angle : ℝ) :
    Commute (Exchange.exchangeUnitary angle) (Quantum.localUnitary U U) := by
  apply Subtype.ext
  have h := ((Commute.one_left (Quantum.localUnitary U U : JointMatrix ι)).smul_left (Real.cos angle : ℂ)).sub_left
    ((Powered.Source.swap_commutes_shared U).smul_left (Complex.I*(Real.sin angle : ℂ)))
  exact h.eq

theorem exchange_product (a b : ℝ) :
    (Exchange.exchangeUnitary (ι := ι) a)*Exchange.exchangeUnitary b=Exchange.exchangeUnitary (a+b) := by
  apply Subtype.ext
  change partialSwap (Real.cos a) (Real.sin a)*partialSwap (Real.cos b) (Real.sin b)=_
  rw [partial_swap_product]
  simp only [Exchange.exchangeUnitary,Real.cos_add,Real.sin_add]
  congr 1
  ring

theorem shared_product (U V : Matrix.unitaryGroup ι ℂ) :
    Quantum.localUnitary U U*Quantum.localUnitary V V=Quantum.localUnitary (U*V) (U*V) := by
  apply Subtype.ext
  simp only [Quantum.localUnitary,Submonoid.coe_mul,Matrix.kronecker,← Matrix.mul_kronecker_mul]

theorem pair_steps_product (H K : SystemMatrix ι) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (g t u : ℝ) :
    Thermal.Dynamics.pairUnitary H hH g t*Thermal.Dynamics.pairUnitary K hK g u=
      Quantum.localUnitary (singleUnitary H hH t*singleUnitary K hK u) (singleUnitary H hH t*singleUnitary K hK u)*
        Exchange.exchangeUnitary (g*(t+u)) := by
  rw [pair_unitary_factors,pair_unitary_factors]
  rw [mul_assoc,← mul_assoc (Exchange.exchangeUnitary (g*t)),(exchange_shared_commute (singleUnitary K hK u) (g*t)).eq]
  rw [← mul_assoc,← mul_assoc,shared_product,mul_assoc,exchange_product]
  congr 1
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
