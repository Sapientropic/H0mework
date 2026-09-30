import H0mework.Physics.LowEnergy.Quantum.ScalarMagnusAlgebra
import H0mework.Physics.LowEnergy.Quantum.WavepacketCurrentAudit

/-! A genuine real-momentum family with time-varying polynomial CCR fields.
This checks the Lie algebra and source coupling, not a time-integral theorem. -/
set_option autoImplicit false
namespace SourceScalarMagnusAudit
open SourceWavepacketInteraction SourceWavepacketCurrent SourceWavepacketAudit
open SourceWavepacketCurrentAudit SourceScalarMagnus
open scoped BigOperators
noncomputable section

def field (t : ℝ) : Module.End ℂ Poly := Q - (t : ℂ) • P

theorem time_field_CCR (t s : ℝ) :
    field t * field s - field s * field t =
      (Complex.I * ((t-s : ℝ) : ℂ)) • 1 := by
  calc
    _ = ((t : ℂ)-(s : ℂ)) • (Q*P-P*Q) := by
      simp only [field, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
      module
    _ = _ := by
      rw [actual_polynomial_CCR, smul_smul]
      congr 1
      push_cast
      ring

def rho (t : ℝ) : Module.End ℂ PolynomialWave :=
  current (fun p : ℝ => p-1) (sourceMatrix t)

def V (t : ℝ) : Module.End ℂ PolynomialWave :=
  familyInteraction (fun _a : Fin 1 => fun p : ℝ => p-1)
    (fun _a : Fin 1 => scalarKernel (sourceMatrix t) (field t))

def B (t : ℝ) : Module.End ℂ PolynomialWave := (-Complex.I) • V t

theorem actual_family_is_coupling (t : ℝ) :
    V t = coupling (fun _a : Fin 1 => onBoson (M := ℝ) (I := Fin 2) (N := 2) (field t))
      (fun _a : Fin 1 => rho t) := by
  exact (actual_scalar_coupling (fun _a : Fin 1 => field t)
    (fun _a : Fin 1 => fun p : ℝ => p-1)
    (fun _a : Fin 1 => sourceMatrix t)).symm

theorem actual_family_factor (t : ℝ) : V t = onBoson (field t) * rho t := by
  rw [actual_family_is_coupling]
  simp [coupling]

theorem actual_family_commutator (t s : ℝ) :
    V t * V s - V s * V t =
      (Complex.I * ((t-s : ℝ) : ℂ)) • (rho t * rho s) := by
  rw [actual_family_factor t, actual_family_factor s]
  apply pair_commutator
  · exact (boson_commutes_current (field s) _ _).symm
  · exact (boson_commutes_current (field t) _ _).symm
  · exact currents_commute target _ _ _ _ (source_matrix_grade t) (source_matrix_grade s)
  · exact onBoson_CCR _ _ _ (time_field_CCR t s)

theorem actual_family_triple_zero (t s u : ℝ) :
    Commute (V u) (V t * V s - V s * V t) := by
  exact actual_scalar_triple_zero target
    (fun v (_a : Fin 1) => field v)
    (fun v (_a : Fin 1) w (_b : Fin 1) => Complex.I * ((v-w : ℝ) : ℂ))
    (fun (_v : ℝ) (_a : Fin 1) (p : ℝ) => p-1)
    (fun v (_a : Fin 1) => sourceMatrix v)
    (fun v _ => source_matrix_grade v)
    (fun v _ w _ => time_field_CCR v w) t s u

theorem B_product (t s : ℝ) : B t * B s = -(V t * V s) := by
  simp [B, smul_smul, Complex.I_mul_I]

theorem actual_Dyson_commutator (t s : ℝ) :
    B t * B s - B s * B t =
      (-Complex.I * ((t-s : ℝ) : ℂ)) • (rho t * rho s) := by
  rw [B_product, B_product]
  have negate : -(V t * V s) - -(V s * V t) = -(V t * V s - V s * V t) := by
    noncomm_ring
  rw [negate, actual_family_commutator]
  module

theorem actual_Dyson_triple_zero (t s u : ℝ) :
    Commute (B u) (B t * B s - B s * B t) := by
  rw [B_product, B_product]
  have negate : -(V t * V s) - -(V s * V t) = -(V t * V s - V s * V t) := by
    noncomm_ring
  rw [negate]
  exact ((actual_family_triple_zero t s u).smul_left (-Complex.I)).neg_right

theorem mixed_current_value :
    ((rho 1 * rho 0) polynomialWave) ![(2,1),(0,1)] = (20 : ℂ) • (1 : Poly) := by
  norm_num [rho, current, interaction, Module.End.mul_apply, lineAction,
    scalarKernel, polynomialWave, sameInternalWave, sourceMatrix,
    Fin.sum_univ_two, Function.update_apply, smul_smul]
  module

theorem nonzero_Dyson_commutator_value :
    ((B 1 * B 0 - B 0 * B 1) polynomialWave) ![(2,1),(0,1)] =
      (-20*Complex.I) • (1 : Poly) := by
  rw [actual_Dyson_commutator]
  change (-Complex.I * ((1-0 : ℝ) : ℂ)) •
    (((rho 1 * rho 0) polynomialWave) ![(2,1),(0,1)]) = _
  rw [mixed_current_value, smul_smul]
  congr 1
  norm_num
  ring

#print axioms SourceScalarMagnus.pair_commutator
#print axioms SourceScalarMagnus.coupling_commutator
#print axioms SourceScalarMagnus.coupling_triple_zero
#print axioms SourceScalarMagnus.actual_scalar_coupling
#print axioms SourceScalarMagnus.actual_scalar_triple_zero
#print axioms time_field_CCR
#print axioms actual_family_is_coupling
#print axioms actual_family_factor
#print axioms actual_family_commutator
#print axioms actual_family_triple_zero
#print axioms B_product
#print axioms actual_Dyson_commutator
#print axioms actual_Dyson_triple_zero
#print axioms mixed_current_value
#print axioms nonzero_Dyson_commutator_value

end
end SourceScalarMagnusAudit
