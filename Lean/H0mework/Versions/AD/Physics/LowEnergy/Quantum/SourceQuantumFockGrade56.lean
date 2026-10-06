import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceQuantumFockGauge
import H0mework.Physics.LowEnergy.Quantum.FockFilteredWords
import H0mework.Versions.AB.Physics.LowEnergyMixed.Degree
/-! The finite raising capacity of the original full504 CAR carrier.
The target consists of both independent-real branches of the original
spin x Lambda6 basis, so its cardinality is generated as 2 * 4 * 7 = 56.
The original Yukawa and arbitrary live spin multipliers raise this grade;
57 insertions vanish on the whole Fock carrier, including interleaved
grade-zero factors and noncommuting boson operators. The actual original
70-coefficient scalar coupling is consumed as a finite sum, not one chosen
coefficient. These are operator algebra identities on the existing domains.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceQuantumFockGrade56
open SaturationMonoid.PhysicsCore
open SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SU7ExteriorMatterRestriction SU7ExteriorMatterRepresentation DiracCliffordRepresentation
open DiracExteriorMatterAction StageNineDiracDualYukawaSpinJurisdiction SU7ExteriorBreakingYukawa
open QuantizationCheck.Fermion SourceFockRaising SourceFockFilteredWords
open scoped BigOperators TensorProduct
attribute [local instance] modeOrder Fermion.fullIndexOrder
local instance : DecidableEq Quantum.Index := Quantum.instDecidableEqIndex

def sixEmbedding : (Bool × DiracSpinorIndex × ExteriorBasisIndex 6) ↪ Mode where
  toFun b := if b.1 then Sum.inl ⟨b.2.1, Sum.inl b.2.2⟩ else Sum.inr ⟨b.2.1, Sum.inl b.2.2⟩
  inj' := by
    rintro ⟨b,spin,index⟩ ⟨c,other,j⟩ h
    cases b <;> cases c <;> simp_all

@[simp] theorem sixEmbedding_apply (b : Bool × DiracSpinorIndex × ExteriorBasisIndex 6) :
    sixEmbedding b = if b.1 then Sum.inl ⟨b.2.1, Sum.inl b.2.2⟩ else Sum.inr ⟨b.2.1, Sum.inl b.2.2⟩ := rfl

def target : Finset Mode := Finset.univ.map sixEmbedding

def isSix (i : Quantum.Index) : Prop := i.2.isLeft

instance (i : Quantum.Index) : Decidable (isSix i) := inferInstanceAs (Decidable (i.2.isLeft = true))

theorem mem_target_left (i : Quantum.Index) : Sum.inl i ∈ target ↔ isSix i := by
  rcases i with ⟨spin, six | two | four⟩ <;>
    simp [target, isSix, Bool.exists_bool]
  exact ⟨six.val, six.property, rfl⟩

theorem mem_target_right (i : Quantum.Index) : Sum.inr i ∈ target ↔ isSix i := by
  rcases i with ⟨spin, six | two | four⟩ <;>
    simp [target, isSix, Bool.exists_bool]
  exact ⟨six.val, six.property, rfl⟩

theorem target_card : target.card = 56 := by
  have hs : Fintype.card (ExteriorBasisIndex 6) = 7 := by
    rw [← Module.finrank_eq_card_basis (su7ExteriorBasis 6), su7ExteriorPower_finrank]
    norm_num [Nat.choose]
  simp [target, Fintype.card_prod, DiracSpinorIndex, hs]

theorem coordinates_degreeSix (v : DiracExteriorMatterCarrier) (i : Quantum.Index) :
    Quantum.coordinates (MixedSymbol.degreeSix v) i =
      (if isSix i then (1 : ℂ) else 0) * Quantum.coordinates v i := by
  rcases i with ⟨spin, six | two | four⟩ <;>
    simp [Quantum.coordinates, Quantum.wholeBasis, Quantum.internalBasis,
      Module.Basis.equivFun_apply, MixedSymbol.degreeSix, isSix]


theorem degreeSix_matrix : Quantum.operatorMatrix MixedSymbol.degreeSix =
    Matrix.diagonal (fun i : Quantum.Index => if isSix i then (1 : ℂ) else 0) := by
  apply Matrix.ext
  intro i j
  have h := Quantum.matrix_action MixedSymbol.degreeSix
    (Quantum.coordinates.symm (Pi.single j 1))
  have hi := congrFun h i
  rw [coordinates_degreeSix, LinearEquiv.apply_symm_apply] at hi
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at hi
  by_cases same : i = j
  · subst j
    simpa only [Pi.single_eq_same, mul_one, Matrix.diagonal_apply_eq] using hi
  · simpa only [Pi.single_eq_of_ne same, mul_zero, Matrix.diagonal_apply_ne _ same] using hi


set_option backward.isDefEq.respectTransparency false in
theorem matrix_grade (A : Module.End ℂ DiracExteriorMatterCarrier) (w : ℕ)
    (law : MixedSymbol.degreeSix * A = A * MixedSymbol.degreeSix + (w : ℂ) • A)
    (i j : Quantum.Index) :
    ((if isSix i then (1 : ℂ) else 0) - (if isSix j then (1 : ℂ) else 0) - (w : ℂ)) *
      Quantum.operatorMatrix A i j = 0 := by
  classical
  have hm := congrArg Quantum.operatorMatrix law
  have mul (B C : Module.End ℂ DiracExteriorMatterCarrier) :
      Quantum.operatorMatrix (B * C) = Quantum.operatorMatrix B * Quantum.operatorMatrix C :=
    Quantum.matrix_composition B C
  have add (B C : Module.End ℂ DiracExteriorMatterCarrier) :
      Quantum.operatorMatrix (B + C) = Quantum.operatorMatrix B + Quantum.operatorMatrix C :=
    Quantum.operatorMatrix.map_add B C
  have smul (c : ℂ) (B : Module.End ℂ DiracExteriorMatterCarrier) :
      Quantum.operatorMatrix (c • B) = c • Quantum.operatorMatrix B :=
    Quantum.operatorMatrix.toLinearEquiv.map_smul c B
  rw [mul, add, mul, smul, degreeSix_matrix] at hm
  have h := congrFun (congrFun hm i) j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul] at h
  linear_combination h

theorem branches_grade (A : Matrix Quantum.Index Quantum.Index ℂ) (w : ℕ)
    (law : ∀ i j, ((if isSix i then (1 : ℂ) else 0) -
      (if isSix j then (1 : ℂ) else 0) - (w : ℂ)) * A i j = 0)
    (i j : Mode) :
    ((if i ∈ target then (1 : ℂ) else 0) - (if j ∈ target then (1 : ℂ) else 0) - (w : ℂ)) *
      SourceRealScalarFock.branches A i j = 0 := by
  cases i with
  | inl i => cases j with
    | inl j => simpa only [SourceRealScalarFock.branches, Matrix.fromBlocks_apply₁₁,
        mem_target_left] using law i j
    | inr j => simp [SourceRealScalarFock.branches]
  | inr i => cases j with
    | inl j => simp [SourceRealScalarFock.branches]
    | inr j =>
      have h := congrArg (fun z : ℂ => -star z) (law i j)
      simpa [SourceRealScalarFock.branches, mem_target_right, mul_neg] using h

def yukawaMatrix (spin : DiracMatrix) (scalar : ExteriorBreakingScalarCarrier) : Matrix Mode Mode ℂ :=
  SourceRealScalarFock.branches (Quantum.operatorMatrix
    ((diracMatrixMatterAction spin).comp (diracDualRightChiralYukawaAction scalar)))

def yukawaDensity (spin : DiracMatrix) (scalar : ExteriorBreakingScalarCarrier) : End (ι := Mode) :=
  Fermion.quantize (yukawaMatrix spin scalar)

theorem yukawa_mother_grade (spin : DiracMatrix) (scalar : ExteriorBreakingScalarCarrier) :
    MixedSymbol.degreeSix * (diracMatrixMatterAction spin * diracDualRightChiralYukawaAction scalar) =
      (diracMatrixMatterAction spin * diracDualRightChiralYukawaAction scalar) * MixedSymbol.degreeSix +
        (1 : ℂ) • (diracMatrixMatterAction spin * diracDualRightChiralYukawaAction scalar) := by
  have hs : MixedSymbol.degreeSix * diracMatrixMatterAction spin =
      diracMatrixMatterAction spin * MixedSymbol.degreeSix := MixedSymbol.degreeSix_spin spin
  have ho : MixedSymbol.degreeSix * diracDualRightChiralYukawaAction scalar =
      diracDualRightChiralYukawaAction scalar := MixedSymbol.yukawa_output scalar
  have hz : diracDualRightChiralYukawaAction scalar * MixedSymbol.degreeSix = 0 :=
    MixedSymbol.yukawa_degreeSix scalar
  rw [← mul_assoc, hs, mul_assoc, ho]
  rw [mul_assoc, hz, mul_zero, one_smul, zero_add]

theorem yukawa_raises (spin : DiracMatrix) (scalar : ExteriorBreakingScalarCarrier) :
    grade target * yukawaDensity spin scalar = yukawaDensity spin scalar * grade target + yukawaDensity spin scalar := by
  apply quantize_raises_grade
  intro i j
  have h := branches_grade _ 1 (matrix_grade _ 1
    (by simpa only [Nat.cast_one] using yukawa_mother_grade spin scalar)) i j
  norm_num only [Nat.cast_one] at h
  by_cases hi : i ∈ target <;> by_cases hj : j ∈ target <;>
    simpa only [yukawaMatrix, Module.End.mul_eq_comp, hi, hj, if_true, if_false] using h


theorem original_scalar_density_raises (a : SourceRealScalarFock.ScalarIndex) :
    grade target * SourceRealScalarFock.density a =
      SourceRealScalarFock.density a * grade target + SourceRealScalarFock.density a := by
  apply quantize_raises_grade
  have hbase := yukawa_mother_grade diracGammaZero (SourceScalarFock.scalarDirection a)
  have hmother : MixedSymbol.degreeSix * FullQuantum.yukawaHamiltonian (SourceScalarFock.scalarDirection a) =
      FullQuantum.yukawaHamiltonian (SourceScalarFock.scalarDirection a) * MixedSymbol.degreeSix +
        (1 : ℂ) • FullQuantum.yukawaHamiltonian (SourceScalarFock.scalarDirection a) := by
    unfold FullQuantum.yukawaHamiltonian
    change MixedSymbol.degreeSix * ((Stage9C.Material.SpinPair.lapse : ℂ) •
      (diracMatrixMatterAction diracGammaZero * diracDualRightChiralYukawaAction (SourceScalarFock.scalarDirection a))) = _
    rw [mul_smul_comm, hbase, smul_add, smul_mul_assoc]
    simp only [one_smul, Module.End.mul_eq_comp]
  intro i j
  have h := branches_grade _ 1 (matrix_grade _ 1 (by simpa only [Nat.cast_one] using hmother)) i j
  norm_num only [Nat.cast_one] at h
  by_cases hi : i ∈ target <;> by_cases hj : j ∈ target <;>
    simpa only [SourceRealScalarFock.sourceMatrix, SourceScalarFock.sourceMatrix,
      hi, hj, if_true, if_false] using h

section GeneralBound
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [Fintype ι] in
theorem grade_above_target (s : Finset ι) (m : ℕ) (hm : s.card < m)
    (psi : Fock ι) (he : grade s psi = (m : ℂ) • psi) : psi = 0 := by
  funext word
  by_contra hzero
  have he' : (((word.filter (fun i => i ∈ s)).card : ℕ) : ℂ) * psi word =
      (m : ℂ) * psi word := by
    simpa only [grade_apply, Pi.smul_apply, smul_eq_mul] using congrFun he word
  have hc : (word.filter (fun i => i ∈ s)).card = m := by
    exact_mod_cast mul_right_cancel₀ hzero he'
  have hb : (word.filter (fun i => i ∈ s)).card ≤ s.card :=
    Finset.card_le_card (by intro i hi; exact (Finset.mem_filter.mp hi).2)
  omega

omit [Fintype ι] in
theorem graded_word_eigenstate (s : Finset ι) (word : List (ℕ × End (ι := ι)))
    (laws : ∀ p ∈ word, grade s * p.2 = p.2 * grade s + (p.1 : ℂ) • p.2)
    (psi : Fock ι) (m : ℕ) (he : grade s psi = (m : ℂ) • psi) :
    grade s ((word.map Prod.snd).prod psi) =
      ((m + weight word : ℕ) : ℂ) • (word.map Prod.snd).prod psi := by
  induction word with
  | nil => simpa [weight] using he
  | cons p rest ih =>
    have hr := ih (fun q h => laws q (List.mem_cons_of_mem p h))
    have hh := homogeneous_eigenstate s p.2 p.1 (laws p List.mem_cons_self)
      ((rest.map Prod.snd).prod psi) (m + weight rest) hr
    simpa [weight, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh

theorem weighted_word_above_target (s : Finset ι) (word : List (ℕ × End (ι := ι)))
    (laws : ∀ p ∈ word, grade s * p.2 = p.2 * grade s + (p.1 : ℂ) • p.2)
    (long : s.card < weight word) : (word.map Prod.snd).prod = 0 := by
  have hb (v : Finset ι) : (word.map Prod.snd).prod (occupationBasis v) = 0 := by
    have he : grade s (occupationBasis v) =
        (((v.filter (fun i => i ∈ s)).card : ℕ) : ℂ) • occupationBasis v := by
      simpa [SourceFockRaising.grade, Finset.filter_mem_eq_inter] using
        basis_eigenstate (fun i : ι => if i ∈ s then (1 : ℂ) else 0) v
    exact grade_above_target s _ (by omega) _ (graded_word_eigenstate s word laws _ _ he)
  apply LinearMap.ext
  intro psi
  have expansion : psi = ∑ v : Finset ι, psi v • occupationBasis v := by
    funext v
    simp [occupationBasis, Finset.sum_apply]
  rw [expansion, map_sum]
  simp [map_smul, hb]
end GeneralBound


theorem occupation_grade_le_56 (word : Occupation) :
    (word.filter (fun i => i ∈ target)).card ≤ 56 := by
  rw [← target_card]
  exact Finset.card_le_card (by intro i hi; exact (Finset.mem_filter.mp hi).2)

theorem full_word_above_56 (word : List (ℕ × End (ι := Mode)))
    (laws : ∀ p ∈ word, grade target * p.2 = p.2 * grade target + (p.1 : ℂ) • p.2)
    (long : 56 < weight word) : (word.map Prod.snd).prod = 0 :=
  weighted_word_above_target target word laws (by simpa only [target_card] using long)

theorem full_tensor_word_above_56 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (word : List (ℕ × (Module.End ℂ V × End (ι := Mode))))
    (laws : ∀ p ∈ word, grade target * p.2.2 = p.2.2 * grade target + (p.1 : ℂ) • p.2.2)
    (long : 56 < (word.map Prod.fst).sum) :
    (word.map (fun p => p.2.1 ⊗ₜ[ℂ] p.2.2)).prod =
      (0 : Module.End ℂ V ⊗[ℂ] End (ι := Mode)) := by
  have factor := ordered_tensor_product (word.map Prod.snd)
  simp only [List.map_map, Function.comp_def] at factor
  rw [factor]
  have hz := full_word_above_56 (word.map (fun p => (p.1, p.2.2)))
    (by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact laws q hq)
    (by simpa [weight, List.map_map, Function.comp_def] using long)
  simp only [List.map_map, Function.comp_def] at hz
  rw [hz, TensorProduct.tmul_zero]

theorem preserving_times_raising (D Y : End (ι := Mode))
    (hD : grade target * D = D * grade target)
    (hY : grade target * Y = Y * grade target + Y) :
    grade target * (D * Y) = (D * Y) * grade target + D * Y := by
  rw [← mul_assoc, hD, mul_assoc, hY, mul_add, ← mul_assoc]

theorem original_57_insertions_zero
    (D : Fin 57 → End (ι := Mode))
    (preserves : ∀ i, grade target * D i = D i * grade target)
    (scalar : Fin 57 → SourceRealScalarFock.ScalarIndex) :
    (List.ofFn (fun i : Fin 57 => D i * SourceRealScalarFock.density (scalar i))).prod = 0 := by
  let word := List.ofFn (fun i : Fin 57 => (1, D i * SourceRealScalarFock.density (scalar i)))
  have h := full_word_above_56 word ?_ ?_
  · simpa [word, List.map_ofFn, Function.comp_def] using h
  · intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    simpa only [Nat.cast_one, one_smul] using preserving_times_raising (D i) _
      (preserves i) (original_scalar_density_raises (scalar i))
  · simp [word, weight]

theorem live_57_insertions_zero
    (D : Fin 57 → End (ι := Mode))
    (preserves : ∀ i, grade target * D i = D i * grade target)
    (spin : Fin 57 → DiracMatrix) (scalar : Fin 57 → ExteriorBreakingScalarCarrier) :
    (List.ofFn (fun i : Fin 57 => D i * yukawaDensity (spin i) (scalar i))).prod = 0 := by
  let word := List.ofFn (fun i : Fin 57 => (1, D i * yukawaDensity (spin i) (scalar i)))
  have h := full_word_above_56 word ?_ ?_
  · simpa [word, List.map_ofFn, Function.comp_def] using h
  · intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    simpa only [Nat.cast_one, one_smul] using preserving_times_raising (D i) _
      (preserves i) (yukawa_raises (spin i) (scalar i))
  · simp [word, weight]


theorem coefficient_derivative_grade (w : ℕ)
    (F : ℝ → Matrix Mode Mode ℂ) (D : Matrix Mode Mode ℂ) (t : ℝ)
    (law : ∀ r i j, ((if i ∈ target then (1 : ℂ) else 0) -
      (if j ∈ target then (1 : ℂ) else 0) - (w : ℂ)) * F r i j = 0)
    (derivative : ∀ i j, HasDerivAt (fun r => F r i j) (D i j) t) (i j : Mode) :
    ((if i ∈ target then (1 : ℂ) else 0) -
      (if j ∈ target then (1 : ℂ) else 0) - (w : ℂ)) * D i j = 0 := by
  have he := derivative i j
  have hc := he.const_mul ((if i ∈ target then (1 : ℂ) else 0) -
    (if j ∈ target then (1 : ℂ) else 0) - (w : ℂ))
  have hz : (fun r => ((if i ∈ target then (1 : ℂ) else 0) -
    (if j ∈ target then (1 : ℂ) else 0) - (w : ℂ)) * F r i j) = fun _ => 0 :=
    funext (fun r => law r i j)
  rw [hz] at hc
  exact hc.unique (hasDerivAt_const t (0 : ℂ))


private theorem left_sum_power_zero {κ R : Type*} [Fintype κ] [Semiring R]
    (term : κ → R) (n : ℕ) (A : R)
    (vanishes : ∀ word : List κ, word.length = n → A * (word.map term).prod = 0) :
    A * (∑ i, term i) ^ n = 0 := by
  induction n generalizing A with
  | zero => simpa using vanishes [] rfl
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i _
    apply ih (A * term i)
    intro word hw
    have h := vanishes (i :: word) (by simp [hw])
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using h

theorem full_original_Yukawa_57_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (boson : SourceRealScalarFock.ScalarIndex → Module.End ℂ V) :
    (∑ a : SourceRealScalarFock.ScalarIndex,
      boson a ⊗ₜ[ℂ] SourceRealScalarFock.density a) ^ 57 =
        (0 : Module.End ℂ V ⊗[ℂ] End (ι := Mode)) := by
  have h := left_sum_power_zero (fun a : SourceRealScalarFock.ScalarIndex =>
      boson a ⊗ₜ[ℂ] SourceRealScalarFock.density a) 57 1 ?_
  · simpa only [one_mul] using h
  · intro word hw
    have zero := full_tensor_word_above_56
      (word.map (fun a => (1, (boson a, SourceRealScalarFock.density a)))) ?_ ?_
    · simpa only [List.map_map, Function.comp_def, one_mul] using zero
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      simpa only [Nat.cast_one, one_smul] using original_scalar_density_raises a
    · simp [List.map_map, Function.comp_def, hw]

theorem original_coupling_57_zero : SourceRealScalarFock.coupling ^ 57 = 0 :=
  full_original_Yukawa_57_zero SourceScalarCCR.position


theorem original_joint_operator_57_zero :
    (SourceRealScalarFock.represent SourceRealScalarFock.coupling) ^ 57 = 0 := by
  have h : SourceRealScalarFock.represent (SourceRealScalarFock.coupling ^ 57) =
      (SourceRealScalarFock.represent SourceRealScalarFock.coupling) ^ 57 :=
    map_pow SourceRealScalarFock.represent.toRingHom SourceRealScalarFock.coupling 57
  rw [← h, original_coupling_57_zero]
  exact SourceRealScalarFock.represent.toRingHom.map_zero

end LowEnergy.SourceQuantumFockGrade56
