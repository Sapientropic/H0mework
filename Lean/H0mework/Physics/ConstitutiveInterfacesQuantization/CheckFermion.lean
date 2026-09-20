import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
Finite occupation-space fermions.  The order fixes the standard exterior-basis signs;
the one-particle identity is computed from the creation and annihilation operators.
-/

namespace SaturationMonoid.PhysicsCore.QuantizationCheck.Fermion

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Amplitudes on all finite occupation configurations. -/
abbrev Fock (ι : Type*) := Finset ι → ℂ

/-- The exterior-basis sign counts occupied modes strictly before the acting mode. -/
def sign (i : ι) (s : Finset ι) : ℂ :=
  (-1 : ℂ) ^ (s.filter (fun j => j < i)).card

def occupationBasis (s : Finset ι) : Fock ι :=
  fun t => if t = s then 1 else 0

def vacuum : Fock ι := occupationBasis ∅

def create (i : ι) (ψ : Fock ι) : Fock ι :=
  fun s => if i ∈ s then sign i (s.erase i) * ψ (s.erase i) else 0

def annihilate (i : ι) (ψ : Fock ι) : Fock ι :=
  fun s => if i ∈ s then 0 else sign i s * ψ (insert i s)

def oneParticle (v : ι → ℂ) : Fock ι :=
  fun s => ∑ i, v i * occupationBasis {i} s

def pairing (ψ φ : Fock ι) : ℂ :=
  ∑ s, star (ψ s) * φ s

/-- The number-preserving second quantization, with no constant vacuum term. -/
def secondQuantize (A : ι → ι → ℂ) (ψ : Fock ι) : Fock ι :=
  fun s => ∑ i, ∑ j, A i j * create i (annihilate j ψ) s

omit [Fintype ι] in
@[simp] theorem sign_empty (i : ι) : sign i ∅ = 1 := by
  simp [sign]

omit [Fintype ι] in
theorem sign_mul_self (i : ι) (s : Finset ι) : sign i s * sign i s = 1 := by
  rw [sign, ← mul_pow]
  simp

omit [Fintype ι] in
@[simp] theorem annihilate_vacuum (i : ι) : annihilate i (vacuum : Fock ι) = 0 := by
  funext s
  simp [annihilate, vacuum, occupationBasis]

omit [Fintype ι] in
theorem create_create (i : ι) (ψ : Fock ι) : create i (create i ψ) = 0 := by
  funext s
  by_cases hi : i ∈ s <;> simp [create, hi]

omit [Fintype ι] in
theorem annihilate_annihilate (i : ι) (ψ : Fock ι) :
    annihilate i (annihilate i ψ) = 0 := by
  funext s
  by_cases hi : i ∈ s <;> simp [annihilate, hi]

omit [Fintype ι] in
theorem create_annihilate_same (i : ι) (ψ : Fock ι) (s : Finset ι) :
    create i (annihilate i ψ) s = if i ∈ s then ψ s else 0 := by
  by_cases hi : i ∈ s
  · simp only [create, if_pos hi, annihilate, Finset.notMem_erase, ↓reduceIte,
      Finset.insert_erase hi]
    rw [← mul_assoc, sign_mul_self, one_mul]
  · simp [create, hi]

omit [Fintype ι] in
theorem annihilate_create_same (i : ι) (ψ : Fock ι) (s : Finset ι) :
    annihilate i (create i ψ) s = if i ∈ s then 0 else ψ s := by
  by_cases hi : i ∈ s
  · simp [annihilate, hi]
  · simp only [annihilate, if_neg hi, create, Finset.mem_insert_self, ↓reduceIte,
      Finset.erase_insert hi]
    rw [← mul_assoc, sign_mul_self, one_mul]

omit [Fintype ι] in
/-- The same-mode canonical anticommutator holds on every occupation amplitude. -/
theorem same_mode_car (i : ι) (ψ : Fock ι) :
    annihilate i (create i ψ) + create i (annihilate i ψ) = ψ := by
  funext s
  simp only [Pi.add_apply, annihilate_create_same, create_annihilate_same]
  split <;> simp

@[simp] theorem oneParticle_singleton (v : ι → ℂ) (i : ι) :
    oneParticle v {i} = v i := by
  simp [oneParticle, occupationBasis]

omit [Fintype ι] in
@[simp] theorem annihilate_empty (i : ι) (ψ : Fock ι) :
    annihilate i ψ ∅ = ψ {i} := by
  simp [annihilate]

omit [Fintype ι] in
@[simp] theorem create_singleton (i k : ι) (ψ : Fock ι) :
    create i ψ {k} = if i = k then ψ ∅ else 0 := by
  by_cases h : i = k
  · subst k
    simp [create]
  · simp [create, h]

theorem secondQuantize_oneParticle_singleton (A : ι → ι → ℂ)
    (v : ι → ℂ) (i : ι) :
    secondQuantize A (oneParticle v) {i} = ∑ j, A i j * v j := by
  simp [secondQuantize, mul_ite]

theorem pairing_oneParticle_left (v : ι → ℂ) (ψ : Fock ι) :
    pairing (oneParticle v) ψ = ∑ i, star (v i) * ψ {i} := by
  simp only [pairing, oneParticle, star_sum, star_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  ext i
  simp [occupationBasis]

@[simp] theorem oneParticle_empty (v : ι → ℂ) : oneParticle v ∅ = 0 := by
  simp [oneParticle, occupationBasis]

theorem oneParticle_eq_zero_of_not_singleton (v : ι → ℂ) (s : Finset ι)
    (hs : ∀ i, s ≠ {i}) : oneParticle v s = 0 := by
  simp [oneParticle, occupationBasis, hs]

/-- An annihilator sends the entire one-particle sector to the vacuum sector. -/
theorem annihilate_oneParticle (i : ι) (v : ι → ℂ) :
    annihilate i (oneParticle v) = fun s => v i * vacuum s := by
  funext s
  by_cases hs : s = ∅
  · subst s
    simp [vacuum, occupationBasis]
  · by_cases hi : i ∈ s
    · simp [annihilate, hi, vacuum, occupationBasis, hs]
    · have hn : ∀ k, insert i s ≠ {k} := by
        intro k hk
        have hik : i = k := by
          have him : i ∈ insert i s := Finset.mem_insert_self i s
          rw [hk] at him
          simpa using him
        subst k
        have hs' : s ⊆ {i} := by
          rw [← hk]
          exact Finset.subset_insert i s
        apply hs
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxi : x = i := by simpa using hs' hx
        exact hi (hxi ▸ hx)
      simp [annihilate, hi, oneParticle_eq_zero_of_not_singleton v _ hn,
        vacuum, occupationBasis, hs]

omit [Fintype ι] in
theorem create_vacuum (i : ι) : create i (vacuum : Fock ι) = occupationBasis {i} := by
  funext s
  by_cases hs : s = {i}
  · subst s
    simp [vacuum, occupationBasis]
  · by_cases hi : i ∈ s
    · have he : s.erase i ≠ ∅ := by
        intro he
        apply hs
        have h := Finset.insert_erase hi
        rw [he] at h
        exact h.symm
      simp [create, hi, vacuum, occupationBasis, he, hs]
    · have hsi : s ≠ {i} := hs
      simp [create, hi, occupationBasis, hsi]

omit [Fintype ι] in
theorem create_const_mul (i : ι) (c : ℂ) (ψ : Fock ι) :
    create i (fun s => c * ψ s) = fun s => c * create i ψ s := by
  funext s
  by_cases hi : i ∈ s <;> simp [create, hi, mul_left_comm]

/-- The explicit second quantization preserves the one-particle sector on the full Fock carrier. -/
theorem secondQuantize_oneParticle (A : ι → ι → ℂ) (v : ι → ℂ) :
    secondQuantize A (oneParticle v) = oneParticle (fun i => ∑ j, A i j * v j) := by
  funext s
  simp only [secondQuantize, annihilate_oneParticle, create_const_mul, create_vacuum,
    oneParticle, Finset.sum_mul, mul_assoc]

theorem pairing_oneParticle (v w : ι → ℂ) :
    pairing (oneParticle v) (oneParticle w) = ∑ i, star (v i) * w i := by
  simp [pairing_oneParticle_left]

theorem oneParticle_injective : Function.Injective (oneParticle (ι := ι)) := by
  intro v w h
  funext i
  simpa using congrFun h {i}

/-- Every complex one-particle matrix element is preserved by the explicit Fock operators. -/
theorem pairing_secondQuantize_oneParticle (A : ι → ι → ℂ) (v w : ι → ℂ) :
    pairing (oneParticle v) (secondQuantize A (oneParticle w)) =
      ∑ i, star (v i) * (∑ j, A i j * w j) := by
  rw [pairing_oneParticle_left]
  simp_rw [secondQuantize_oneParticle_singleton]

theorem expectation_secondQuantize_oneParticle (A : ι → ι → ℂ) (v : ι → ℂ) :
    pairing (oneParticle v) (secondQuantize A (oneParticle v)) =
      ∑ i, star (v i) * (∑ j, A i j * v j) :=
  pairing_secondQuantize_oneParticle A v v

end SaturationMonoid.PhysicsCore.QuantizationCheck.Fermion
