import H0mework.Physics.LowEnergyMatterSpace.LocalOperator

/-! The bounded local multipliers are the same real P286 field variations at each point. -/
set_option autoImplicit false
open MeasureTheory
open scoped Matrix Kronecker
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open Fermion SU7MotherLieAlgebra DiracCliffordRepresentation
noncomputable section
attribute [local instance] instLinearOrderSourceIndex

theorem tripletGaugeMatrix_real_smul (r : ℝ) (data : P286LieBlockData) :
    tripletGaugeMatrix (r • data)=(r : ℂ) • tripletGaugeMatrix data := by
  ext a b
  change r • (data.1 : Matrix (Fin 3) (Fin 3) ℂ) a b+
    (r • (data.2.2.1 : ℂ))*(1 : Matrix (Fin 3) (Fin 3) ℂ) a b=
    (r : ℂ)*((data.1 : Matrix (Fin 3) (Fin 3) ℂ) a b+
      data.2.2.1*(1 : Matrix (Fin 3) (Fin 3) ℂ) a b)
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_eq_mul]
  by_cases diagonal : a=b <;> simp [Matrix.one_apply,diagonal]
  ring

theorem gaugeDiracMatrix_real_smul (r : ℝ) (data : LorentzianIndex → P286LieBlockData) :
    gaugeDiracMatrix (r • data)=(r : ℂ) • gaugeDiracMatrix data := by
  simp only [gaugeDiracMatrix,Pi.smul_apply,tripletGaugeMatrix_real_smul,
    Matrix.kronecker_smul,← Finset.smul_sum]
  exact smul_comm _ _ _

theorem gaugeHamiltonianMatrix_real_smul (r : ℝ) (data : LorentzianIndex → P286LieBlockData) :
    gaugeHamiltonianMatrix (r • data)=(r : ℂ) • gaugeHamiltonianMatrix data := by
  rw [gaugeHamiltonianMatrix,gaugeDiracMatrix_real_smul,Matrix.mul_smul]
  rfl

theorem gaugeCurrentMatrix_real_smul (r : ℝ) (data : LorentzianIndex → P286LieBlockData) :
    gaugeCurrentMatrix (r • data)=(r : ℂ) • gaugeCurrentMatrix data := by
  rw [gaugeCurrentMatrix,gaugeDiracMatrix_real_smul,Matrix.mul_smul,smul_comm]
  rfl

private theorem operator_real_smul (r : ℝ) (A : SourceMatrix) (v : MatterFiber) :
    hamiltonianOperator ((r : ℂ) • A) v=(r : ℂ) • hamiltonianOperator A v := by
  unfold hamiltonianOperator
  rw [map_smul]
  rfl

private theorem real_value (z : ℂ) (real : star z=z) : (z.re : ℂ)=z := by
  have imaginary : z.im=0 := by
    have same := congrArg Complex.im real
    simp only [Complex.star_def,Complex.conj_im] at same
    linarith
  exact Complex.ext rfl (by simpa using imaginary.symm)

theorem localGaugeHamiltonian_native_ae (profile : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (profile x)=profile x)
    (data : LorentzianIndex → P286LieBlockData) (v : MatterL2) :
    localGaugeHamiltonian profile data v=ᵐ[volume] fun x =>
      hamiltonianOperator (gaugeHamiltonianMatrix ((profile x).re • data)) (v x) := by
  filter_upwards [localMatrixOperator_ae profile (gaugeHamiltonianMatrix data) v,real] with x hx hr
  change localMatrixOperator profile (gaugeHamiltonianMatrix data) v x=_
  rw [hx,gaugeHamiltonianMatrix_real_smul,operator_real_smul,real_value _ hr]

theorem localCurrentOperator_native_ae (profile : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (profile x)=profile x)
    (data : LorentzianIndex → P286LieBlockData) (v : MatterL2) :
    localCurrentOperator profile data v=ᵐ[volume] fun x =>
      hamiltonianOperator (gaugeCurrentMatrix ((profile x).re • data)) (v x) := by
  filter_upwards [localMatrixOperator_ae profile (gaugeCurrentMatrix data) v,real] with x hx hr
  change localMatrixOperator profile (gaugeCurrentMatrix data) v x=_
  rw [hx,gaugeCurrentMatrix_real_smul,operator_real_smul,real_value _ hr]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
