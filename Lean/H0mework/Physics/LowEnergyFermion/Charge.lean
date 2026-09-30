import H0mework.Physics.LowEnergyFermion.MatrixElement

/-! The original CAR words preserve the charges carried by their source vertices. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open scoped BigOperators
noncomputable section
variable {ι : Type*} [LinearOrder ι]

def occupationCharge (q : ι → ℂ) : Module.End ℂ (Fock ι) where
  toFun ψ s := (∑ i ∈ s, q i) * ψ s
  map_add' ψ φ := by ext s; simp [mul_add]
  map_smul' c ψ := by ext s; simp [mul_left_comm]

omit [LinearOrder ι] in
@[simp] theorem occupationCharge_apply (q : ι → ℂ) (ψ : Fock ι) (s : Finset ι) :
    occupationCharge q ψ s = (∑ i ∈ s, q i) * ψ s := rfl

theorem occupationCharge_creation (q : ι → ℂ) (i : ι) :
    occupationCharge q * creation i =
      creation i * occupationCharge q + q i • creation i := by
  apply LinearMap.ext
  intro ψ
  funext s
  by_cases hi : i ∈ s
  · have sum_eq := Finset.sum_erase_add s q hi
    simp only [Module.End.mul_apply, creation_apply, occupationCharge_apply,
      LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, create, hi, ↓reduceIte]
    rw [← sum_eq]
    ring
  · simp [Module.End.mul_apply, create, hi]

theorem occupationCharge_annihilation (q : ι → ℂ) (i : ι) :
    occupationCharge q * annihilation i =
      annihilation i * occupationCharge q - q i • annihilation i := by
  apply LinearMap.ext
  intro ψ
  funext s
  by_cases hi : i ∈ s
  · simp [Module.End.mul_apply, annihilate, hi]
  · simp only [Module.End.mul_apply, annihilation_apply, occupationCharge_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, annihilate, hi, ↓reduceIte, Finset.sum_insert hi]
    ring

omit [LinearOrder ι] in
private theorem charge_product (N A B : Module.End ℂ (Fock ι)) (a b : ℂ)
    (first : N*A=A*N+a•A) (second : N*B=B*N+b•B) :
    N*(A*B)=(A*B)*N+(a+b)•(A*B) := by
  calc
    N*(A*B) = (N*A)*B := (mul_assoc _ _ _).symm
    _ = (A*N+a•A)*B := by rw [first]
    _ = A*(N*B)+a•(A*B) := by simp [add_mul, mul_assoc]
    _ = A*(B*N+b•B)+a•(A*B) := by rw [second]
    _ = (A*B)*N+(a+b)•(A*B) := by
      simp only [mul_add, mul_assoc, mul_smul_comm, add_smul]
      abel

theorem occupationCharge_bilinear (q : ι → ℂ) (i j : ι) :
    occupationCharge q * (creation i * annihilation j) =
      (creation i * annihilation j) * occupationCharge q +
        (q i-q j) • (creation i * annihilation j) := by
  have second : occupationCharge q * annihilation j =
      annihilation j * occupationCharge q + (-(q j)) • annihilation j := by
    rw [occupationCharge_annihilation, sub_eq_add_neg]
    congr 1
    exact (neg_smul (q j) (annihilation j)).symm
  simpa only [sub_eq_add_neg] using charge_product _ _ _ (q i) (-(q j))
    (occupationCharge_creation q i) second

theorem occupationCharge_four_word (q : ι → ℂ) (i j k l : ι) :
    occupationCharge q * (creation i * creation k * annihilation l * annihilation j) =
      (creation i * creation k * annihilation l * annihilation j) * occupationCharge q +
        (q i+q k-q j-q l) • (creation i * creation k * annihilation l * annihilation j) := by
  have first := charge_product _ _ _ (q i) (q k)
    (occupationCharge_creation q i) (occupationCharge_creation q k)
  have last (a : ι) : occupationCharge q * annihilation a =
      annihilation a * occupationCharge q + (-(q a)) • annihilation a := by
    rw [occupationCharge_annihilation, sub_eq_add_neg]
    congr 1
    exact (neg_smul (q a) (annihilation a)).symm
  have third := charge_product _ _ _ (q i+q k) (-(q l)) first (last l)
  have fourth := charge_product _ _ _ (q i+q k+ -(q l)) (-(q j)) third (last j)
  have coefficient : (q i+q k+ -(q l))+ -(q j)=q i+q k-q j-q l := by ring
  rw [coefficient] at fourth
  exact fourth

variable [Fintype ι]

theorem occupationCharge_original_quantize (q : ι → ℂ) :
    quantize (Matrix.diagonal q) = occupationCharge q := by
  apply LinearMap.ext
  intro ψ
  funext occupied
  simp [quantize_apply, secondQuantize, Matrix.diagonal_apply, create_annihilate_same,
    occupationCharge_apply, mul_ite, Finset.sum_mul]

theorem occupationCharge_quantize (q : ι → ℂ) (A : Matrix ι ι ℂ)
    (source_charge : ∀ i j, (q i-q j)*A i j=0) :
    occupationCharge q * quantize A = quantize A * occupationCharge q := by
  simp only [quantize, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [occupationCharge_bilinear, smul_add, smul_smul]
  have coefficient : A i j*(q i-q j)=0 := by rw [mul_comm]; exact source_charge i j
  rw [coefficient, zero_smul, add_zero]

theorem occupationCharge_normalProduct (q : ι → ℂ) (A B : Matrix ι ι ℂ)
    (first : ∀ i j, (q i-q j)*A i j=0)
    (second : ∀ i j, (q i-q j)*B i j=0) :
    occupationCharge q * normalProduct A B = normalProduct A B * occupationCharge q := by
  simp only [normalProduct, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [occupationCharge_four_word, smul_add, smul_smul]
  have coefficient : (A i j*B k l)*(q i+q k-q j-q l)=0 := by
    linear_combination (B k l)*(first i j) + (A i j)*(second k l)
  rw [coefficient, zero_smul, add_zero]

omit [LinearOrder ι] [Fintype ι] in
theorem occupationCharge_preserves_eigenstate (q : ι → ℂ) (T : Module.End ℂ (Fock ι))
    (law : occupationCharge q*T=T*occupationCharge q) (ψ : Fock ι) (charge : ℂ)
    (eigenstate : occupationCharge q ψ = charge • ψ) :
    occupationCharge q (T ψ)=charge • T ψ := by
  have identity := congrArg (fun a : Module.End ℂ (Fock ι) => a ψ) law
  simpa only [Module.End.mul_apply, eigenstate, map_smul] using identity

omit [LinearOrder ι] in
theorem occupationCharge_pairing (q : ι → ℝ) (ψ φ : Fock ι) :
    pairing (occupationCharge (fun i => (q i : ℂ)) ψ) φ =
      pairing ψ (occupationCharge (fun i => (q i : ℂ)) φ) := by
  simp only [pairing, occupationCharge_apply, star_mul, star_sum, Complex.star_def,
    Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro occupied _
  ring

omit [LinearOrder ι] in
theorem occupationCharge_selection (q : ι → ℝ) (T : Module.End ℂ (Fock ι))
    (law : occupationCharge (fun i => (q i : ℂ))*T =
      T*occupationCharge (fun i => (q i : ℂ)))
    (ψ φ : Fock ι) (incoming outgoing : ℝ) (different : outgoing ≠ incoming)
    (input : occupationCharge (fun i => (q i : ℂ)) ψ=(incoming : ℂ) • ψ)
    (output : occupationCharge (fun i => (q i : ℂ)) φ=(outgoing : ℂ) • φ) :
    pairing φ (T ψ)=0 := by
  have preserved := occupationCharge_preserves_eigenstate _ T law ψ _ input
  have identity := occupationCharge_pairing q φ (T ψ)
  rw [output, preserved, pairing_smul_left, pairing_smul_right] at identity
  simp only [Complex.star_def, Complex.conj_ofReal] at identity
  have nonzero : (outgoing : ℂ)-(incoming : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr different
  apply (mul_eq_zero.mp (show ((outgoing : ℂ)-(incoming : ℂ))*pairing φ (T ψ)=0 by
    linear_combination identity)).resolve_left nonzero

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
