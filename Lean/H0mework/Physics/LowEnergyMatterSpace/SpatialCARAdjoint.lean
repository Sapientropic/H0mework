import H0mework.Physics.LowEnergyMatterSpace.SpatialCARWords
import H0mework.Quantum.Kernel.Gram
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The finite spatial CAR representation preserves the actual Fock adjoint and positive Gram pairing. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
open QuantizationCheck.Fermion Fermion
open scoped InnerProductSpace ComplexOrder
noncomputable section
variable {m : Type*} [Fintype m] [LinearOrder m]

theorem pairing_create_adjoint (i : m) (ψ φ : Fock m) :
    pairing (create i ψ) φ=pairing ψ (annihilate i φ) := by
  have left : pairing (create i ψ) φ=
      ∑ s ∈ Finset.univ.filter (fun s : Finset m => i ∈ s),
        sign i (s.erase i)*star (ψ (s.erase i))*φ s := by
    simp only [pairing,create,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases present : i ∈ s
    · simp only [if_pos present,star_mul,star_sign]
      ring
    · simp only [if_neg present,star_zero,zero_mul]
  have right : pairing ψ (annihilate i φ)=
      ∑ s ∈ Finset.univ.filter (fun s : Finset m => i ∉ s),
        sign i s*star (ψ s)*φ (insert i s) := by
    simp [pairing,annihilate,Finset.sum_filter,mul_ite,mul_assoc,mul_left_comm]
  rw [left,right]
  apply Finset.sum_bij (fun s _ => s.erase i)
  · intro s _
    simp
  · intro s hs t ht same
    have first : i ∈ s := (Finset.mem_filter.mp hs).2
    have second : i ∈ t := (Finset.mem_filter.mp ht).2
    simpa only [Finset.insert_erase first,Finset.insert_erase second] using
      congrArg (insert i) same
  · intro t ht
    have absent : i ∉ t := (Finset.mem_filter.mp ht).2
    exact ⟨insert i t,by simp,Finset.erase_insert absent⟩
  · intro s hs
    rw [Finset.insert_erase (Finset.mem_filter.mp hs).2]

theorem pairing_wave_adjoint (u : m → ℂ) (ψ φ : Fock m) :
    pairing (waveCreation u ψ) φ=pairing ψ (annihilator u φ) := by
  simp only [waveCreation,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.sum_apply,
    LinearMap.smul_apply,pairing_sum_left,pairing_smul_left,creation_apply,pairing_create_adjoint]
  simp only [annihilator,LinearMap.sum_apply,LinearMap.smul_apply,annihilation_apply,
    pairing,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun _ _ => by ring)

omit [LinearOrder m] in
theorem pairing_star (ψ φ : Fock m) : star (pairing ψ φ)=pairing φ ψ := by
  simp only [pairing,star_sum,star_mul,star_star]

theorem pairing_annihilator_adjoint (u : m → ℂ) (ψ φ : Fock m) :
    pairing (annihilator u ψ) φ=pairing ψ (waveCreation u φ) := by
  have identity := congrArg star (pairing_wave_adjoint u φ ψ)
  simpa only [pairing_star] using identity.symm

def Letter.adjoint {α : Type*} : Letter α → Letter α
  | .create i => .annihilate i
  | .annihilate i => .create i

def wordAdjoint {α : Type*} (word : List (Letter α)) : List (Letter α) :=
  (word.map Letter.adjoint).reverse

theorem pairing_letter_adjoint {α : Type*} (coordinates : α → m → ℂ)
    (letter : Letter α) (ψ φ : Fock m) :
    pairing (letterOperator coordinates letter ψ) φ=
      pairing ψ (letterOperator coordinates letter.adjoint φ) := by
  cases letter with
  | create i => exact pairing_wave_adjoint (coordinates i) ψ φ
  | annihilate i => exact pairing_annihilator_adjoint (coordinates i) ψ φ

theorem wordOperator_append {α : Type*} (coordinates : α → m → ℂ)
    (first second : List (Letter α)) :
    wordOperator coordinates (first++second)=wordOperator coordinates first*wordOperator coordinates second := by
  induction first with
  | nil => simp only [List.nil_append,wordOperator,one_mul]
  | cons letter rest ih => simp only [List.cons_append,wordOperator,ih,mul_assoc]

theorem pairing_word_adjoint {α : Type*} (coordinates : α → m → ℂ)
    (word : List (Letter α)) (ψ φ : Fock m) :
    pairing (wordOperator coordinates word ψ) φ=
      pairing ψ (wordOperator coordinates (wordAdjoint word) φ) := by
  induction word generalizing φ with
  | nil => rfl
  | cons letter rest ih =>
    rw [wordOperator,Module.End.mul_apply,pairing_letter_adjoint,ih]
    simp only [wordAdjoint,List.map_cons,List.reverse_cons,wordOperator_append,wordOperator,
      mul_one,Module.End.mul_apply]

omit [LinearOrder m] in
theorem pairing_euclidean (ψ φ : Fock m) :
    pairing ψ φ=inner ℂ (WithLp.toLp 2 ψ) (WithLp.toLp 2 φ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

omit [LinearOrder m] in
theorem fock_gram_positive {α : Type*} (vectors : α → Fock m) :
    Matrix.PosSemidef (fun i j => pairing (vectors i) (vectors j)) := by
  simp_rw [pairing_euclidean]
  exact SaturationMonoid.Quantum.Kernel.gram_posSemidef (fun i => WithLp.toLp 2 (vectors i))

theorem allWord_positive {α β : Type*} (coordinates : α → m → ℂ) (source : α)
    (words : β → List (Letter α)) :
    Matrix.PosSemidef (fun i j => pairing (oneParticle (coordinates source))
      (wordOperator coordinates (wordAdjoint (words i)++words j) (oneParticle (coordinates source)))) := by
  simp_rw [wordOperator_append,Module.End.mul_apply,← pairing_word_adjoint]
  exact fock_gram_positive (fun i => wordOperator coordinates (words i) (oneParticle (coordinates source)))

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
