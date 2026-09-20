import H0mework.Physics.LowEnergyFermion.TwoParticle

/-! Exact two-occupation matrix elements from the original Fock pairing. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open scoped BigOperators Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
theorem pairing_smul_left (c : ℂ) (ψ φ : Fock ι) :
    pairing (c • ψ) φ = star c * pairing ψ φ := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, star_mul, mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro occupied _
  ring

omit [LinearOrder ι] in
theorem pairing_sub_right (ψ φ χ : Fock ι) :
    pairing ψ (φ-χ) = pairing ψ φ-pairing ψ χ := by
  simp [pairing, mul_sub, Finset.sum_sub_distrib]

omit [LinearOrder ι] in
theorem pairing_smul_right (c : ℂ) (ψ φ : Fock ι) :
    pairing ψ (c • φ) = c * pairing ψ φ := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro occupied _
  ring

omit [LinearOrder ι] in
theorem pairing_sum_left {κ : Type*} [Fintype κ] (family : κ → Fock ι) (ψ : Fock ι) :
    pairing (∑ k, family k) ψ = ∑ k, pairing (family k) ψ := by
  simp only [pairing, Finset.sum_apply, star_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem pairing_occupation (occupied : Finset ι) (ψ : Fock ι) :
    pairing (occupationBasis occupied) ψ = ψ occupied := by
  simp [pairing, occupationBasis]

omit [Fintype ι] in
theorem star_sign (i : ι) (occupied : Finset ι) : star (sign i occupied) = sign i occupied := by
  simp [sign]

omit [Fintype ι] in
theorem two_created (i j : ι) :
    create i (create j (vacuum : Fock ι)) =
      if i=j then 0 else sign i {j} • occupationBasis {i,j} := by
  by_cases same : i=j
  · subst j
    simp [create_create]
  rw [if_neg same, create_vacuum]
  funext occupied
  by_cases hit : occupied={i,j}
  · subst occupied
    simp [create, occupationBasis, same]
  by_cases present : i ∈ occupied
  · have erased : occupied.erase i ≠ {j} := by
      intro identity
      apply hit
      rw [← Finset.insert_erase present, identity]
    simp [create, occupationBasis, present, erased, hit]
  · simp [create, occupationBasis, present, hit]

theorem pairing_two_created (i j : ι) (ψ : Fock ι) :
    pairing (create i (create j vacuum)) ψ = annihilate j (annihilate i ψ) ∅ := by
  rw [two_created]
  by_cases same : i=j
  · subst j
    simp [annihilate, pairing]
  simp [same, pairing_smul_left, pairing_occupation, star_sign, annihilate, sign_empty]

theorem twoParticle_expansion (u v : ι → ℂ) :
    twoParticle u v = ∑ i, ∑ j, (u i*v j) • create i (create j vacuum) := by
  unfold twoParticle
  conv_lhs => arg 1; rw [waveCreation]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [waveCreation, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul, creation_apply]

theorem pairing_twoParticle_left (u v : ι → ℂ) (ψ : Fock ι) :
    pairing (twoParticle u v) ψ =
      ∑ i, ∑ j, (star (u i)*star (v j))*annihilate j (annihilate i ψ) ∅ := by
  rw [twoParticle_expansion]
  simp only [pairing_sum_left, pairing_smul_left, star_mul, pairing_two_created]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def modePair (u v : ι → ℂ) : ℂ := ∑ i, star (u i)*v i

theorem pairing_twoParticle (x y u v : ι → ℂ) :
    pairing (twoParticle x y) (twoParticle u v) =
      modePair x u*modePair y v-modePair x v*modePair y u := by
  rw [pairing_twoParticle_left]
  change (∑ i, ∑ j, (star (x i)*star (y j))*(annihilation j (annihilation i (twoParticle u v))) ∅) = _
  simp only [annihilation_twice, Pi.smul_apply, smul_eq_mul, vacuum, occupationBasis,
    ↓reduceIte, mul_one, mul_sub, Finset.sum_sub_distrib]
  simp only [modePair, Finset.sum_mul]
  simp only [Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem normalProduct_matrixElement (A B : Matrix ι ι ℂ) (x y u v : ι → ℂ) :
    pairing (twoParticle x y) (normalProduct A B (twoParticle u v)) =
      (modePair x (A *ᵥ u)*modePair y (B *ᵥ v)-modePair x (B *ᵥ v)*modePair y (A *ᵥ u)) -
      (modePair x (A *ᵥ v)*modePair y (B *ᵥ u)-modePair x (B *ᵥ u)*modePair y (A *ᵥ v)) := by
  rw [normalProduct_twoParticle, pairing_sub_right, pairing_twoParticle, pairing_twoParticle]

theorem modePair_single_matrix (A : Matrix ι ι ℂ) (i j : ι) :
    modePair (Pi.single i 1) (A *ᵥ Pi.single j 1) = A i j := by
  simp [modePair, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, ite_mul]

theorem occupied_normal_matrixElement (A B : Matrix ι ι ℂ) (i k j l : ι) :
    pairing (twoParticle (Pi.single i 1) (Pi.single k 1))
      (normalProduct A B (twoParticle (Pi.single j 1) (Pi.single l 1))) =
      (A i j * B k l-B i l * A k j) - (A i l * B k j-B i j * A k l) := by
  rw [normalProduct_matrixElement]
  simp only [modePair_single_matrix]

theorem twoParticle_smul (a b : ℂ) (u v : ι → ℂ) :
    twoParticle (a • u) (b • v) = (a*b) • twoParticle u v := by
  simp [twoParticle, map_smul, smul_smul, mul_comm]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
