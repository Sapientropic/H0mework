import H0mework.Physics.LowEnergyFockDynamics.Algebra

/-! Exact Heisenberg derivative structure of the source one-body currents.
The CAR normal product is symmetric, second quantization sends the one-body
commutator to the operator commutator, and the quartic normal product is a
derivation through `quantize`.  These generic identities are consumed by
`source_joint_current_heisenberg.py`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SourceJointCurrentHeisenberg
open SaturationMonoid.PhysicsCore
open SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open scoped BigOperators Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem quantize_add (A B : Matrix ι ι ℂ) :
    quantize (A + B) = quantize A + quantize B := by
  simp only [quantize, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem quantize_sub (A B : Matrix ι ι ℂ) :
    quantize (A - B) = quantize A - quantize B := by
  rw [eq_sub_iff_add_eq, ← quantize_add, sub_add_cancel]

private theorem normalProduct_eq (A B : Matrix ι ι ℂ) :
    normalProduct A B = quantize A * quantize B - quantize (A * B) := by
  rw [quantize_normal_order]
  abel

omit [Fintype ι] in
private theorem creation_swap (i j : ι) :
    creation i * creation j + creation j * creation i = 0 := by
  apply LinearMap.ext
  intro ψ
  exact create_create_car i j ψ

omit [Fintype ι] in
private theorem annihilation_swap (i j : ι) :
    annihilation i * annihilation j + annihilation j * annihilation i = 0 :=
  operator_annihilation_car i j

omit [Fintype ι] in
private theorem operator_swap (i j k l : ι) :
    creation i * creation k * annihilation l * annihilation j =
      creation k * creation i * annihilation j * annihilation l := by
  apply LinearMap.ext
  intro ψ
  simp only [Module.End.mul_apply]
  have step1 : annihilation l (annihilation j ψ) =
      -(annihilation j (annihilation l ψ)) := by
    simp only [annihilation_apply]
    exact eq_neg_of_add_eq_zero_left (annihilate_annihilate_car l j ψ)
  rw [step1, map_neg, map_neg]
  have step2 : creation i (creation k (annihilation j (annihilation l ψ))) =
      -creation k (creation i (annihilation j (annihilation l ψ))) := by
    simp only [creation_apply]
    exact eq_neg_of_add_eq_zero_left (create_create_car i k _)
  rw [step2, neg_neg]

omit [Fintype ι] in
private theorem normal_term_comm (A B : Matrix ι ι ℂ) (i j k l : ι) :
    (A i j * B k l) • (creation i * creation k * annihilation l * annihilation j) =
      (B k l * A i j) •
        (creation k * creation i * annihilation j * annihilation l) := by
  rw [operator_swap i j k l, mul_comm (A i j) (B k l)]

omit [LinearOrder ι] in
private theorem quadruple_swap (f : ι → ι → ι → ι → Module.End ℂ (Fock ι)) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc (∑ i, ∑ j, ∑ k, ∑ l, f i j k l)
      = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem normalProduct_comm (A B : Matrix ι ι ℂ) :
    normalProduct A B = normalProduct B A := by
  unfold normalProduct
  rw [quadruple_swap (fun i j k l =>
    (B i j * A k l) • (creation i * creation k * annihilation l * annihilation j))]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  exact normal_term_comm A B i j k l

theorem quantize_commutator (A B : Matrix ι ι ℂ) :
    quantize A * quantize B - quantize B * quantize A = quantize (A*B - B*A) := by
  rw [quantize_normal_order A B, quantize_normal_order B A, normalProduct_comm B A,
    quantize_sub]
  abel

theorem quantize_anticommutator (A B : Matrix ι ι ℂ) :
    quantize A * quantize B + quantize B * quantize A =
      (2 : ℂ) • normalProduct A B + quantize (A*B + B*A) := by
  rw [quantize_normal_order A B, quantize_normal_order B A, normalProduct_comm B A,
    quantize_add, two_smul ℂ]
  abel

theorem normalProduct_quantize_commutator (A B M : Matrix ι ι ℂ) :
    normalProduct A B * quantize M - quantize M * normalProduct A B =
      normalProduct (A*M - M*A) B + normalProduct A (B*M - M*B) := by
  have inter : quantize A * quantize B * quantize M - quantize M * (quantize A * quantize B) =
      quantize A * (quantize B * quantize M) - quantize A * (quantize M * quantize B) +
        (quantize A * quantize M * quantize B - quantize M * quantize A * quantize B) := by
    noncomm_ring
  have hz : quantize (A*B*M - M*(A*B)) =
      quantize ((A*M - M*A)*B) + quantize (A*(B*M - M*B)) := by
    rw [← quantize_add]
    congr 1
    noncomm_ring
  rw [normalProduct_eq, normalProduct_eq, normalProduct_eq, sub_mul, mul_sub]
  have rear : quantize A * quantize B * quantize M - quantize (A*B) * quantize M -
        (quantize M * (quantize A * quantize B) - quantize M * quantize (A*B)) =
      quantize A * quantize B * quantize M - quantize M * (quantize A * quantize B) -
        (quantize (A*B) * quantize M - quantize M * quantize (A*B)) := by
    noncomm_ring
  rw [rear, inter,
    ← mul_sub (quantize A) (quantize B * quantize M) (quantize M * quantize B),
    ← sub_mul (quantize A * quantize M) (quantize M * quantize A) (quantize B),
    quantize_commutator, quantize_commutator, quantize_commutator,
    quantize_normal_order, quantize_normal_order, hz]
  abel

private theorem normalProduct_zero_left (B : Matrix ι ι ℂ) :
    normalProduct (0 : Matrix ι ι ℂ) B = 0 := by simp [normalProduct]

private theorem normalProduct_zero_right (A : Matrix ι ι ℂ) :
    normalProduct A (0 : Matrix ι ι ℂ) = 0 := by simp [normalProduct]

theorem normalProduct_charge_commute (Q A B : Matrix ι ι ℂ)
    (hA : Q*A = A*Q) (hB : Q*B = B*Q) :
    quantize Q * normalProduct A B = normalProduct A B * quantize Q := by
  have e1 : A*Q - Q*A = 0 := sub_eq_zero.mpr hA.symm
  have e2 : B*Q - Q*B = 0 := sub_eq_zero.mpr hB.symm
  have h := normalProduct_quantize_commutator A B Q
  rw [e1, e2, normalProduct_zero_left, normalProduct_zero_right, add_zero] at h
  exact (eq_of_sub_eq_zero h).symm

end
end SourceJointCurrentHeisenberg
