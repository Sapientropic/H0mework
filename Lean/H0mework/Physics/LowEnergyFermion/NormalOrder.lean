import H0mework.Physics.LowEnergyFermion.CAR

/-! The original finite second quantization and its source four-operator remainder. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open scoped BigOperators Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def creation (i : ι) : Module.End ℂ (Fock ι) where
  toFun := create i
  map_add' ψ φ := by funext s; by_cases hi : i ∈ s <;> simp [create, hi, mul_add]
  map_smul' c ψ := by funext s; by_cases hi : i ∈ s <;> simp [create, hi, mul_left_comm]

def annihilation (i : ι) : Module.End ℂ (Fock ι) where
  toFun := annihilate i
  map_add' ψ φ := by funext s; by_cases hi : i ∈ s <;> simp [annihilate, hi, mul_add]
  map_smul' c ψ := by funext s; by_cases hi : i ∈ s <;> simp [annihilate, hi, mul_left_comm]

omit [Fintype ι] in
@[simp] theorem creation_apply (i : ι) (ψ : Fock ι) : creation i ψ = create i ψ := rfl
omit [Fintype ι] in
@[simp] theorem annihilation_apply (i : ι) (ψ : Fock ι) : annihilation i ψ = annihilate i ψ := rfl

omit [Fintype ι] in
theorem operator_car (i j : ι) :
    annihilation i * creation j + creation j * annihilation i =
      if i = j then 1 else 0 := by
  apply LinearMap.ext
  intro ψ
  funext s
  have identity := congrFun (annihilate_create_car i j ψ) s
  by_cases same : i = j <;> simpa [same, Module.End.mul_apply] using identity

omit [Fintype ι] in
theorem operator_annihilation_car (i j : ι) :
    annihilation i * annihilation j + annihilation j * annihilation i = 0 := by
  apply LinearMap.ext
  intro ψ
  funext s
  exact congrFun (annihilate_annihilate_car i j ψ) s

def quantize (A : Matrix ι ι ℂ) : Module.End ℂ (Fock ι) :=
  ∑ i, ∑ j, A i j • (creation i * annihilation j)

theorem quantize_apply (A : Matrix ι ι ℂ) (ψ : Fock ι) :
    quantize A ψ = secondQuantize A ψ := by
  ext s
  simp [quantize, secondQuantize, Module.End.mul_apply]

def normalProduct (A B : Matrix ι ι ℂ) : Module.End ℂ (Fock ι) :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (A i j * B k l) • (creation i * creation k * annihilation l * annihilation j)

omit [Fintype ι] in
theorem word_normal_order (i j k l : ι) :
    (creation i * annihilation j) * (creation k * annihilation l) =
      (if j = k then creation i * annihilation l else 0) +
        creation i * creation k * annihilation l * annihilation j := by
  have mixed := congrArg (fun op : Module.End ℂ (Fock ι) => creation i * op * annihilation l)
    (operator_car j k)
  have anti := congrArg (fun op : Module.End ℂ (Fock ι) => creation i * creation k * op)
    (operator_annihilation_car j l)
  simp only [mul_add, add_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, mul_assoc] at mixed anti
  rw [eq_neg_of_add_eq_zero_left anti] at mixed
  simpa only [mul_assoc] using (sub_eq_iff_eq_add.mp mixed)

private theorem contraction_row (A B : Matrix ι ι ℂ) (i j : ι) :
    (∑ k, ∑ l, (A i j * B k l) •
      (if j = k then creation i * annihilation l else 0)) =
      ∑ l, (A i j * B j l) • (creation i * annihilation l) := by
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_comm]
  simp

theorem quantize_normal_order (A B : Matrix ι ι ℂ) :
    quantize A * quantize B = quantize (A * B) + normalProduct A B := by
  rw [quantize, quantize]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul]
  simp_rw [word_normal_order, smul_add, Finset.sum_add_distrib]
  change _ + normalProduct A B = quantize (A * B) + normalProduct A B
  congr 1
  simp_rw [contraction_row]
  simp only [quantize, Matrix.mul_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem original_secondQuantize_normal_order (A B : Matrix ι ι ℂ) (ψ : Fock ι) :
    secondQuantize A (secondQuantize B ψ) = secondQuantize (A * B) ψ + normalProduct A B ψ := by
  have identity := congrArg (fun op : Module.End ℂ (Fock ι) => op ψ) (quantize_normal_order A B)
  simpa [Module.End.mul_apply, quantize_apply] using identity

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
