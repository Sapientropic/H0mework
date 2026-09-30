import H0mework.Physics.LowEnergy.Quantum.FockRaisingTensor

/-! Actual CAR consumers distinguish one-body nilpotency from many-particle
normal products. The four labels below test the generic finite theorem;
they are not a new physical mode inventory or a source scalar projection. -/
set_option autoImplicit false
namespace SourceFockRaisingAudit
open SaturationMonoid.PhysicsCore
open LowEnergy QuantizationCheck.Fermion SourceFockRaising
open scoped BigOperators Matrix TensorProduct
noncomputable section

def target : Finset (Fin 4) := {2, 3}

def raisingMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => if (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) then 1 else 0

def incoming : Fock (Fin 4) := occupationBasis {0, 1}

theorem actual_matrix_raises (i j : Fin 4) :
    ((if i ∈ target then 1 else 0 : ℂ) -
      (if j ∈ target then 1 else 0 : ℂ) - 1) * raisingMatrix i j = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [target, raisingMatrix, Fin.ext_iff]

theorem actual_one_body_square_zero : raisingMatrix * raisingMatrix = 0 := by
  apply Matrix.ext
  intro i j
  change (∑ k : Fin 4, raisingMatrix i k * raisingMatrix k j) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases hit : (i = 2 ∧ k = 0) ∨ (i = 3 ∧ k = 1)
  · rcases hit with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · have row : raisingMatrix 0 j = 0 := by
        simp only [raisingMatrix, show (0 : Fin 4) ≠ 2 from by decide,
          show (0 : Fin 4) ≠ 3 from by decide, false_and, or_self, if_false]
      rw [row, mul_zero]
    · have row : raisingMatrix 1 j = 0 := by
        simp only [raisingMatrix, show (1 : Fin 4) ≠ 2 from by decide,
          show (1 : Fin 4) ≠ 3 from by decide, false_and, or_self, if_false]
      rw [row, mul_zero]
  · simp [raisingMatrix, hit]

theorem incoming_number_sector (s : Finset (Fin 4)) (different : s.card ≠ 2) :
    incoming s = 0 := by
  have distinct : s ≠ ({0, 1} : Finset (Fin 4)) := by
    intro same
    apply different
    rw [same]
    decide
  simp [incoming, occupationBasis, distinct]

theorem incoming_is_two_particle :
    incoming = Fermion.twoParticle (Pi.single (0 : Fin 4) 1) (Pi.single 1 1) := by
  simp [Fermion.twoParticle_expansion, Pi.single_apply, Fin.sum_univ_four,
    Fermion.two_created, sign, incoming]

theorem actual_fock_square_normal_product :
    Fermion.quantize raisingMatrix * Fermion.quantize raisingMatrix =
      Fermion.normalProduct raisingMatrix raisingMatrix := by
  rw [Fermion.quantize_normal_order, actual_one_body_square_zero]
  simp [Fermion.quantize]

theorem actual_second_word_matrix_element :
    pairing (Fermion.twoParticle (Pi.single (2 : Fin 4) 1) (Pi.single 3 1))
      ((Fermion.quantize raisingMatrix * Fermion.quantize raisingMatrix) incoming) = 2 := by
  rw [actual_fock_square_normal_product, incoming_is_two_particle,
    Fermion.occupied_normal_matrixElement]
  norm_num [raisingMatrix, Fin.ext_iff]

theorem actual_second_word_nonzero :
    (Fermion.quantize raisingMatrix * Fermion.quantize raisingMatrix) incoming ≠ 0 := by
  intro zero
  have contradiction := actual_second_word_matrix_element
  rw [zero] at contradiction
  norm_num [pairing] at contradiction

theorem actual_third_word_zero :
    ([raisingMatrix, raisingMatrix, raisingMatrix].map Fermion.quantize).prod incoming = 0 := by
  apply matrix_word_vanishes_on_number_sector target _ _ 2 (by decide) incoming
    incoming_number_sector
  intro A member i j
  have same : A = raisingMatrix := by simpa using member
  rw [same]
  exact actual_matrix_raises i j

def bosonUp : Module.End ℂ (Fin 2 → ℂ) where
  toFun v := ![v 1, 0]
  map_add' u v := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

def bosonDown : Module.End ℂ (Fin 2 → ℂ) where
  toFun v := ![0, v 0]
  map_add' u v := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

theorem actual_bosons_do_not_commute : bosonUp * bosonDown ≠ bosonDown * bosonUp := by
  intro same
  have bad := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T ![1, 0] 0) same
  norm_num [Module.End.mul_apply, bosonUp, bosonDown] at bad

theorem actual_three_boson_factors_nonzero : bosonUp * bosonDown * bosonUp ≠ 0 := by
  intro zero
  have bad := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T ![0, 1] 0) zero
  norm_num [Module.End.mul_apply, bosonUp, bosonDown] at bad

theorem actual_tensor_order_kept :
    ([(bosonUp, Fermion.quantize raisingMatrix), (bosonDown, Fermion.quantize raisingMatrix)].map
      (fun pair => pair.1 ⊗ₜ[ℂ] pair.2)).prod =
      (bosonUp * bosonDown) ⊗ₜ[ℂ]
        (Fermion.quantize raisingMatrix * Fermion.quantize raisingMatrix) := by
  rw [ordered_tensor_product]
  simp

theorem actual_tensor_third_word_zero (v : Fin 2 → ℂ) :
    Module.endTensorEndAlgHom (S := ℂ)
      ([(bosonUp, raisingMatrix), (bosonDown, raisingMatrix), (bosonUp, raisingMatrix)].map
        (fun pair => pair.1 ⊗ₜ[ℂ] Fermion.quantize pair.2)).prod
      (v ⊗ₜ[ℂ] incoming) = 0 := by
  apply tensor_word_vanishes_on_number_sector target _ _ 2 (by decide) incoming
    incoming_number_sector v
  intro pair member i j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact actual_matrix_raises i j

#print axioms SourceFockRaising.grade_above_particle_number
#print axioms SourceFockRaising.raises_eigenstate
#print axioms SourceFockRaising.word_eigenstates
#print axioms SourceFockRaising.word_vanishes_on_number_sector
#print axioms SourceFockRaising.quantize_preserves_number
#print axioms SourceFockRaising.quantize_raises_grade
#print axioms SourceFockRaising.matrix_word_vanishes_on_number_sector
#print axioms actual_matrix_raises
#print axioms actual_one_body_square_zero
#print axioms incoming_number_sector
#print axioms incoming_is_two_particle
#print axioms actual_fock_square_normal_product
#print axioms actual_second_word_matrix_element
#print axioms actual_second_word_nonzero
#print axioms actual_third_word_zero
#print axioms SourceFockRaising.ordered_tensor_product
#print axioms SourceFockRaising.tensor_word_vanishes_on_number_sector
#print axioms actual_bosons_do_not_commute
#print axioms actual_three_boson_factors_nonzero
#print axioms actual_tensor_order_kept
#print axioms actual_tensor_third_word_zero

end
end SourceFockRaisingAudit
