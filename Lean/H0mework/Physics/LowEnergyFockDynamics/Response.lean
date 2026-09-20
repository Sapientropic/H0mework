import H0mework.Physics.LowEnergyFockDynamics.Algebra
import H0mework.Physics.LowEnergyFermion.Hermitian
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Original occupation-space expectations follow their source wavefunctions. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open scoped BigOperators Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def oneParticleLinear : (ι → ℂ) →ₗ[ℂ] Fock ι where
  toFun := oneParticle
  map_add' u v := by ext occupied; simp [oneParticle,add_mul,Finset.sum_add_distrib]
  map_smul' c u := by ext occupied; simp [oneParticle,Finset.mul_sum,mul_assoc]

theorem source_matrix_oneParticle (H : Matrix ι ι ℂ) (u : ι → ℂ) :
    secondQuantize H (oneParticle u)=oneParticle (H*ᵥu) :=
  secondQuantize_oneParticle H u

theorem original_oneParticle_derivative (ψ : ℝ → ι → ℂ) (v : ι → ℂ) (t : ℝ)
    (derivative : HasDerivAt ψ v t) :
    HasDerivAt (fun time => oneParticle (ψ time)) (oneParticle v) t := by
  exact ((oneParticleLinear.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    t derivative)

theorem original_fock_schrodinger (ψ : ℝ → ι → ℂ) (H : Matrix ι ι ℂ) (t : ℝ)
    (derivative : HasDerivAt ψ ((-Complex.I) • (H*ᵥψ t)) t) :
    HasDerivAt (fun time => oneParticle (ψ time))
      ((-Complex.I) • secondQuantize H (oneParticle (ψ t))) t := by
  have generated := original_oneParticle_derivative ψ _ t derivative
  rw [show oneParticle ((-Complex.I) • (H*ᵥψ t)) =
      (-Complex.I) • oneParticle (H*ᵥψ t) from oneParticleLinear.map_smul _ _] at generated
  rw [source_matrix_oneParticle]
  exact generated

theorem original_oneParticle_commutator (A B : Matrix ι ι ℂ) (u : ι → ℂ) :
    pairing (oneParticle u)
      (secondQuantize A (secondQuantize B (oneParticle u)) -
        secondQuantize B (secondQuantize A (oneParticle u))) =
      modePair u ((A*B-B*A)*ᵥu) := by
  rw [pairing_sub_right]
  rw [source_matrix_oneParticle,source_matrix_oneParticle,source_matrix_oneParticle,
    source_matrix_oneParticle,pairing_oneParticle,pairing_oneParticle]
  change modePair u (A*ᵥ(B*ᵥu))-modePair u (B*ᵥ(A*ᵥu)) = _
  simp [modePair,Matrix.sub_mulVec,Matrix.mulVec_mulVec,mul_sub,Finset.sum_sub_distrib]

omit [LinearOrder ι] in
theorem modePair_smul_left (c : ℂ) (u v : ι → ℂ) :
    modePair (c • u) v=star c*modePair u v := by
  simp only [modePair,Pi.smul_apply,smul_eq_mul,star_mul,Finset.mul_sum,mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [LinearOrder ι] in
theorem modePair_adjoint_left (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    modePair (A*ᵥu) v=modePair u (A.conjTranspose*ᵥv) := by
  simp only [modePair,Matrix.mulVec,dotProduct,star_sum,star_mul,
    Finset.sum_mul,Finset.mul_sum,Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [LinearOrder ι] in
theorem modePair_hasDerivAt (u v : ℝ → ι → ℂ) (du dv : ι → ℂ) (t : ℝ)
    (left : HasDerivAt u du t) (right : HasDerivAt v dv t) :
    HasDerivAt (fun time => modePair (u time) (v time))
      (modePair du (v t)+modePair (u t) dv) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hasDerivAt_pi.mp left i).star).mul (hasDerivAt_pi.mp right i))
  simpa only [modePair,Pi.mul_apply,Finset.sum_add_distrib] using h

omit [LinearOrder ι] in
theorem matrix_wave_derivative (A : Matrix ι ι ℂ) (ψ : ℝ → ι → ℂ)
    (v : ι → ℂ) (t : ℝ) (derivative : HasDerivAt ψ v t) :
    HasDerivAt (fun time => A*ᵥψ time) (A*ᵥv) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hasDerivAt_pi.mp derivative j).const_mul (A i j))
  simpa only [Matrix.mulVec,dotProduct] using h

omit [LinearOrder ι] in
theorem source_current_derivative (ψ : ℝ → ι → ℂ) (T B : Matrix ι ι ℂ) (t : ℝ)
    (selfAdjoint : T.conjTranspose=T)
    (derivative : HasDerivAt ψ ((-Complex.I) • (T*ᵥψ t)) t) :
    HasDerivAt (fun time => modePair (ψ time) (B*ᵥψ time))
      (Complex.I*modePair (ψ t) ((T*B-B*T)*ᵥψ t)) t := by
  have actual := modePair_hasDerivAt ψ (fun time => B*ᵥψ time) _ _ t derivative
    (matrix_wave_derivative B ψ _ t derivative)
  convert actual using 1
  rw [modePair_smul_left,Matrix.mulVec_smul,modePair_smul_right,
    modePair_adjoint_left,selfAdjoint]
  simp only [star_neg,Complex.star_def,Complex.conj_I,neg_neg]
  simp only [modePair,Matrix.sub_mulVec,Matrix.mulVec_mulVec,Pi.sub_apply,
    mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  simp only [Finset.sum_neg_distrib,neg_mul,sub_eq_add_neg]

theorem original_fock_current_derivative (ψ : ℝ → ι → ℂ) (T B : Matrix ι ι ℂ) (t : ℝ)
    (selfAdjoint : T.conjTranspose=T)
    (derivative : HasDerivAt ψ ((-Complex.I) • (T*ᵥψ t)) t) :
    HasDerivAt
      (fun time => pairing (oneParticle (ψ time))
        (secondQuantize B (oneParticle (ψ time))))
      (Complex.I*pairing (oneParticle (ψ t))
        (secondQuantize T (secondQuantize B (oneParticle (ψ t))) -
          secondQuantize B (secondQuantize T (oneParticle (ψ t))))) t := by
  rw [original_oneParticle_commutator]
  have identity : (fun time => pairing (oneParticle (ψ time))
      (secondQuantize B (oneParticle (ψ time)))) =
      (fun time => modePair (ψ time) (B*ᵥψ time)) := by
    funext time
    rw [source_matrix_oneParticle,pairing_oneParticle]
    rfl
  rw [identity]
  exact source_current_derivative ψ T B t selfAdjoint derivative

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
