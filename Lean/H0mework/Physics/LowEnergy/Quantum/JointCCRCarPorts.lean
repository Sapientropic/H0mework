import H0mework.Physics.LowEnergyFockDynamics.Algebra

/-! Exact cubic CAR ports of the original normal product.  Matrices need
not be Hermitian: the independent momentum port keeps the original column,
with no added adjoint or extra Yukawa term. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SourceJointCCRCarPorts
open SaturationMonoid.PhysicsCore
open SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open scoped BigOperators Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [Fintype ι] [LinearOrder ι] in
private theorem weighted_sub (c : ℂ) (X Y : Module.End ℂ (Fock ι)) :
    c • X - c • Y = c • (X - Y) := (smul_sub c X Y).symm

def creationColumn (A : Matrix ι ι ℂ) (m : ι) : Module.End ℂ (Fock ι) :=
  ∑ i, A i m • creation i

omit [Fintype ι] in
private theorem creator_car (i j : ι) :
    creation i * creation j + creation j * creation i = 0 := by
  apply LinearMap.ext
  intro ψ
  exact create_create_car i j ψ

omit [Fintype ι] in
private theorem creator_word (i j k : ι) :
    (creation i * annihilation j) * creation k -
      creation k * (creation i * annihilation j) =
      if j = k then creation i else 0 := by
  calc
    _ = creation i * (annihilation j * creation k + creation k * annihilation j) -
        (creation i * creation k + creation k * creation i) * annihilation j := by
          noncomm_ring
    _ = _ := by rw [operator_car, creator_car]; split <;> simp_all

theorem quantize_creation (A : Matrix ι ι ℂ) (m : ι) :
    quantize A * creation m - creation m * quantize A = creationColumn A m := by
  simp only [quantize, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, weighted_sub, creator_word]
  simp [smul_ite, creationColumn]

theorem quantize_creationColumn (A B : Matrix ι ι ℂ) (m : ι) :
    quantize A * creationColumn B m - creationColumn B m * quantize A =
      creationColumn (A * B) m := by
  simp only [creationColumn, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  rw [← Finset.sum_sub_distrib]
  simp_rw [weighted_sub, quantize_creation, creationColumn, Finset.smul_sum, smul_smul]
  simp only [Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem original_normal_product (A B : Matrix ι ι ℂ) :
    normalProduct A B = quantize A * quantize B - quantize (A * B) := by
  rw [quantize_normal_order]
  abel

/-- Each summand is one creator followed by two annihilators. -/
def cubicAnnihilation (A B : Matrix ι ι ℂ) (m : ι) : Module.End ℂ (Fock ι) :=
  quantize B * annihilationField A m + quantize A * annihilationField B m

/-- Each summand is two creators followed by one annihilator. -/
def cubicCreation (A B : Matrix ι ι ℂ) (m : ι) : Module.End ℂ (Fock ι) :=
  creationColumn B m * quantize A + creationColumn A m * quantize B

theorem annihilation_normalProduct (A B : Matrix ι ι ℂ) (m : ι) :
    annihilation m * normalProduct A B - normalProduct A B * annihilation m =
      cubicAnnihilation A B m := by
  calc
    _ = (annihilation m * quantize A - quantize A * annihilation m) * quantize B +
        quantize A * (annihilation m * quantize B - quantize B * annihilation m) -
        (annihilation m * quantize (A * B) - quantize (A * B) * annihilation m) := by
          rw [original_normal_product]
          simp only [mul_sub, sub_mul, mul_assoc]
          abel
    _ = annihilationField A m * quantize B + quantize A * annihilationField B m -
        annihilationField (A * B) m := by
          simp only [annihilation_quantize, annihilationField]
    _ = _ := by
      rw [← field_quantize A B m]
      unfold cubicAnnihilation
      abel

theorem normalProduct_creation (A B : Matrix ι ι ℂ) (m : ι) :
    normalProduct A B * creation m - creation m * normalProduct A B =
      cubicCreation A B m := by
  calc
    _ = quantize A * (quantize B * creation m - creation m * quantize B) +
        (quantize A * creation m - creation m * quantize A) * quantize B -
        (quantize (A * B) * creation m - creation m * quantize (A * B)) := by
          rw [original_normal_product]
          simp only [mul_sub, sub_mul, mul_assoc]
          abel
    _ = quantize A * creationColumn B m + creationColumn A m * quantize B -
        creationColumn (A * B) m := by rw [quantize_creation, quantize_creation, quantize_creation]
    _ = _ := by
      rw [← quantize_creationColumn A B m]
      unfold cubicCreation
      abel

theorem normalProduct_primal_port (A B : Matrix ι ι ℂ) (m : ι) :
    Complex.I • (normalProduct A B * annihilation m - annihilation m * normalProduct A B) =
      (-Complex.I) • cubicAnnihilation A B m := by
  have reverse : normalProduct A B * annihilation m - annihilation m * normalProduct A B =
      -(annihilation m * normalProduct A B - normalProduct A B * annihilation m) := by abel
  rw [reverse, annihilation_normalProduct, smul_neg]
  exact (neg_smul Complex.I (cubicAnnihilation A B m)).symm

theorem normalProduct_independent_momentum_port (A B : Matrix ι ι ℂ) (m : ι) :
    Complex.I • (normalProduct A B * creation m - creation m * normalProduct A B) =
      Complex.I • cubicCreation A B m := by rw [normalProduct_creation]

end
end SourceJointCCRCarPorts
