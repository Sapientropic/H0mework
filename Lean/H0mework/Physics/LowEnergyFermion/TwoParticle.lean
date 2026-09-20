import H0mework.Physics.LowEnergyFermion.NormalOrder

/-! Two occupied wavefunctions, built by the original creation operators. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open scoped BigOperators Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def waveCreation : (ι → ℂ) →ₗ[ℂ] Module.End ℂ (Fock ι) where
  toFun u := ∑ i, u i • creation i
  map_add' u v := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c u := by simp [Pi.smul_apply, Finset.smul_sum, smul_smul]

theorem waveCreation_vacuum (u : ι → ℂ) :
    waveCreation u vacuum = oneParticle u := by
  ext s
  simp [waveCreation, create_vacuum, oneParticle]

def twoParticle (u v : ι → ℂ) : Fock ι := waveCreation u (waveCreation v vacuum)

theorem annihilation_wave (i : ι) (u : ι → ℂ) :
    annihilation i * waveCreation u + waveCreation u * annihilation i = u i • 1 := by
  simp only [waveCreation, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, ← Finset.sum_add_distrib, ← smul_add, operator_car]
  simp [smul_ite]

theorem annihilation_twoParticle (i : ι) (u v : ι → ℂ) :
    annihilation i (twoParticle u v) = u i • oneParticle v - v i • oneParticle u := by
  have inside : annihilation i (waveCreation v vacuum) = v i • vacuum := by
    rw [waveCreation_vacuum, annihilation_apply, annihilate_oneParticle]
    rfl
  have identity := congrArg (fun op : Module.End ℂ (Fock ι) => op (waveCreation v vacuum))
    (annihilation_wave i u)
  simp only [LinearMap.add_apply, Module.End.mul_apply, inside, map_smul,
    LinearMap.smul_apply, Module.End.one_apply] at identity
  rw [waveCreation_vacuum, waveCreation_vacuum] at identity
  simpa only [twoParticle, waveCreation_vacuum] using eq_sub_of_add_eq identity

theorem annihilation_twice (i j : ι) (u v : ι → ℂ) :
    annihilation j (annihilation i (twoParticle u v)) = (u i*v j-v i*u j) • vacuum := by
  rw [annihilation_twoParticle, map_sub, map_smul, map_smul]
  simp only [annihilation_apply, annihilate_oneParticle]
  funext s
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem twoParticle_left_sum (u v : ι → ℂ) :
    twoParticle u v = ∑ i, u i • creation i (oneParticle v) := by
  rw [twoParticle, waveCreation_vacuum]
  simp only [waveCreation, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.sum_apply, LinearMap.smul_apply]

theorem quantize_twoParticle (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    quantize A (twoParticle u v) = twoParticle (A *ᵥ u) v - twoParticle (A *ᵥ v) u := by
  simp only [quantize, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    annihilation_twoParticle, map_sub, map_smul, smul_sub, smul_smul,
    Finset.sum_sub_distrib]
  simp only [twoParticle_left_sum, Matrix.mulVec, dotProduct, Finset.sum_smul]

theorem normalProduct_twoParticle (A B : Matrix ι ι ℂ) (u v : ι → ℂ) :
    normalProduct A B (twoParticle u v) =
      twoParticle (A *ᵥ u) (B *ᵥ v) - twoParticle (A *ᵥ v) (B *ᵥ u) := by
  have identity := congrArg (fun op : Module.End ℂ (Fock ι) => op (twoParticle u v))
    (quantize_normal_order A B)
  simp only [Module.End.mul_apply, LinearMap.add_apply, quantize_twoParticle, map_sub,
    Matrix.mulVec_mulVec] at identity
  linear_combination -identity

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
