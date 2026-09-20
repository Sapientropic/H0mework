import H0mework.Physics.LowEnergyFermion.TwoParticle

/-! Original finite CAR transport for a source-generated one-particle frame. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open scoped BigOperators Matrix
noncomputable section
variable {ι α : Type*} [Fintype ι] [LinearOrder ι]

omit [Fintype ι] [LinearOrder ι] in
private theorem weighted_sub (c : ℂ) (A B : Module.End ℂ (Fock ι)) :
    c • A-c • B=c • (A-B) := (smul_sub c A B).symm

omit [Fintype ι] in
theorem annihilation_word_commutator (i j k : ι) :
    annihilation i * (creation j * annihilation k) -
      (creation j * annihilation k) * annihilation i =
      if i=j then annihilation k else 0 := by
  calc
    _ = (annihilation i*creation j+creation j*annihilation i)*annihilation k -
        creation j*(annihilation i*annihilation k+annihilation k*annihilation i) := by
          noncomm_ring
    _ = _ := by rw [operator_car,operator_annihilation_car]; split <;> simp_all

theorem annihilation_quantize (i : ι) (H : Matrix ι ι ℂ) :
    annihilation i * quantize H - quantize H * annihilation i =
      ∑ j, H i j • annihilation j := by
  simp only [quantize,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib,weighted_sub,annihilation_word_commutator]
  simp [smul_ite]

def annihilationField (W : Matrix α ι ℂ) (i : α) : Module.End ℂ (Fock ι) :=
  ∑ j, W i j • annihilation j

def creationField (W : Matrix α ι ℂ) (i : α) : Module.End ℂ (Fock ι) :=
  ∑ j, star (W i j) • creation j

theorem field_quantize (W : Matrix α ι ℂ) (H : Matrix ι ι ℂ) (i : α) :
    annihilationField W i * quantize H - quantize H * annihilationField W i =
      annihilationField (W*H) i := by
  simp only [annihilationField,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
  rw [← Finset.sum_sub_distrib]
  simp_rw [weighted_sub,annihilation_quantize,Finset.smul_sum,smul_smul]
  simp only [Matrix.mul_apply,Finset.sum_smul]
  rw [Finset.sum_comm]

theorem field_car (W V : Matrix α ι ℂ) (i j : α) :
    annihilationField W i * creationField V j +
      creationField V j * annihilationField W i =
      (W*V.conjTranspose) i j • (1 : Module.End ℂ (Fock ι)) := by
  simp only [annihilationField,creationField,Finset.sum_mul]
  simp only [Finset.mul_sum,smul_mul_smul]
  rw [Finset.sum_comm (f := fun (a b : ι) =>
    (star (V j a)*W i b) • (creation a*annihilation b))]
  simp_rw [mul_comm (star (V j _))]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib,← smul_add,operator_car]
  simp [smul_ite,Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_smul]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
