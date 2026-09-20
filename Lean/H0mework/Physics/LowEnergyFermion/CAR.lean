import H0mework.Physics.ConstitutiveInterfacesQuantization.CheckFermion

/-! Cross-mode CAR for the original finite occupation operators. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
noncomputable section
variable {ι : Type*} [LinearOrder ι]

theorem sign_insert (i j : ι) (s : Finset ι) (absent : j ∉ s) :
    sign i (insert j s) = (if j < i then -1 else 1) * sign i s := by
  by_cases before : j < i
  · simp [sign, Finset.filter_insert, before, absent, pow_succ, mul_comm]
  · simp [sign, Finset.filter_insert, before]

theorem cross_sign (i j : ι) (s : Finset ι) (different : i ≠ j)
    (first : i ∉ s) (second : j ∉ s) :
    sign i (insert j s) * sign j s + sign j (insert i s) * sign i s = 0 := by
  rw [sign_insert i j s second, sign_insert j i s first]
  rcases lt_or_gt_of_ne different with before | before
  · simp [before, not_lt_of_ge (le_of_lt before)]
    ring
  · simp [before, not_lt_of_ge (le_of_lt before)]
    ring

theorem annihilate_annihilate_cross (i j : ι) (different : i ≠ j) (ψ : Fock ι) :
    annihilate i (annihilate j ψ) + annihilate j (annihilate i ψ) = 0 := by
  funext s
  by_cases first : i ∈ s
  · simp [annihilate, first]
  by_cases second : j ∈ s
  · simp [annihilate, second]
  simp only [Pi.add_apply, annihilate, first, second, Finset.mem_insert,
    different, different.symm, false_or, ↓reduceIte, Pi.zero_apply]
  rw [Finset.insert_comm]
  have signs := cross_sign i j s different first second
  linear_combination ψ (insert i (insert j s)) * signs

theorem create_create_cross (i j : ι) (different : i ≠ j) (ψ : Fock ι) :
    create i (create j ψ) + create j (create i ψ) = 0 := by
  funext s
  by_cases first : i ∈ s
  · by_cases second : j ∈ s
    · let base := (s.erase i).erase j
      have no_i : i ∉ base := by simp [base]
      have no_j : j ∉ base := Finset.notMem_erase _ _
      have erase_i : s.erase i = insert j base := by
        exact (Finset.insert_erase (by simp [second, different.symm])).symm
      have erase_j : s.erase j = insert i base := by
        dsimp [base]
        rw [Finset.erase_right_comm]
        exact (Finset.insert_erase (by simp [first, different])).symm
      simp only [Pi.add_apply, create, first, second, ↓reduceIte,
        Finset.mem_erase, ne_eq, different, different.symm, not_false_eq_true, true_and,
        Pi.zero_apply]
      change sign i (s.erase i) * (sign j base * ψ base) +
        sign j (s.erase j) * (sign i ((s.erase j).erase i) * ψ ((s.erase j).erase i)) = 0
      rw [Finset.erase_right_comm (a := j) (b := i)]
      rw [erase_i, erase_j]
      rw [Finset.erase_insert no_j]
      have signs := cross_sign i j base different no_i no_j
      change sign i (insert j base) * (sign j base * ψ base) +
        sign j (insert i base) * (sign i base * ψ base) = 0
      linear_combination ψ base * signs
    · simp [create, second]
  · simp [create, first]

theorem annihilate_create_cross (i j : ι) (different : i ≠ j) (ψ : Fock ι) :
    annihilate i (create j ψ) + create j (annihilate i ψ) = 0 := by
  funext s
  by_cases first : i ∈ s
  · simp [annihilate, create, first, different]
  by_cases second : j ∈ s
  · have erased : (insert i s).erase j = insert i (s.erase j) :=
      Finset.erase_insert_of_ne different
    have inserted : sign i s = (if j < i then -1 else 1) * sign i (s.erase j) := by
      have identity := sign_insert i j (s.erase j) (Finset.notMem_erase _ _)
      simpa only [Finset.insert_erase second] using identity
    simp only [Pi.add_apply, annihilate, create, first, second, ↓reduceIte,
      Finset.mem_insert, Finset.mem_erase, different.symm, false_or,
      erased, Pi.zero_apply]
    rw [inserted, sign_insert j i (s.erase j) (by simp [first])]
    rcases lt_or_gt_of_ne different with before | before
    · simp [before, not_lt_of_ge (le_of_lt before)]
      ring
    · simp [before, not_lt_of_ge (le_of_lt before)]
      ring
  · simp [annihilate, create, first, second, different.symm]

theorem annihilate_create_car (i j : ι) (ψ : Fock ι) :
    annihilate i (create j ψ) + create j (annihilate i ψ) = if i = j then ψ else 0 := by
  by_cases same : i = j
  · subst j
    simp only [↓reduceIte]
    exact same_mode_car i ψ
  · simpa only [if_neg same] using annihilate_create_cross i j same ψ

theorem create_create_car (i j : ι) (ψ : Fock ι) :
    create i (create j ψ) + create j (create i ψ) = 0 := by
  by_cases same : i = j
  · subst j
    simp [create_create]
  · exact create_create_cross i j same ψ

theorem annihilate_annihilate_car (i j : ι) (ψ : Fock ι) :
    annihilate i (annihilate j ψ) + annihilate j (annihilate i ψ) = 0 := by
  by_cases same : i = j
  · subst j
    simp [annihilate_annihilate]
  · exact annihilate_annihilate_cross i j same ψ

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
