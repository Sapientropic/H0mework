import H0mework.Versions.AD.Physics.LowEnergy.Quantum.FiniteGradeModule

/-! State and two-leg bounds for an algebra with a finite source grade resolution. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.FiniteGradeAlgebra
open scoped BigOperators
variable {A ι : Type*} [Ring A] [Algebra ℂ A] [Fintype ι]

theorem weighted_left [DecidableEq ι] (P : ι → A) (c : ι → ℂ)
    (orthogonal : ∀ i j, P i*P j=if i=j then P i else 0) (i : ι) :
    P i*(∑ j, c j • P j)=c i • P i := by
  classical
  simp only [Finset.mul_sum, mul_smul_comm, orthogonal, smul_ite, smul_zero]
  simp

theorem weighted_right [DecidableEq ι] (P : ι → A) (c : ι → ℂ)
    (orthogonal : ∀ i j, P i*P j=if i=j then P i else 0) (j : ι) :
    (∑ i, c i • P i)*P j=c j • P j := by
  classical
  simp only [Finset.sum_mul, smul_mul_assoc, orthogonal, smul_ite, smul_zero]
  simp

theorem left_words (word : List A) (x : A) :
    (word.map (LinearMap.mulLeft ℂ)).prod x=word.prod*x := by
  induction word with
  | nil => simp
  | cons a tail ih => simpa only [List.map_cons, List.prod_cons, Module.End.mul_apply,
      LinearMap.mulLeft_apply, mul_assoc] using congrArg (a*·) ih

theorem words_zero (G : A) (P : ι → A) (w : ι → ℤ)
    (resolution : ∑ i, P i=1) (left : ∀ i, P i*G=(w i : ℂ) • P i)
    (right : ∀ i, G*P i=(w i : ℂ) • P i) (lower upper : ℤ)
    (bounds : ∀ i, lower ≤ w i ∧ w i ≤ upper) (word : List A)
    (laws : ∀ T ∈ word, G*T=T*G+T) (long : upper-lower < (word.length : ℤ)) : word.prod=0 := by
  let L := LinearMap.mulLeft ℂ (A := A)
  have hres : ∑ i, L (P i)=1 := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sum_apply, Module.End.one_apply, L, LinearMap.mulLeft_apply]
    rw [← Finset.sum_mul, resolution, one_mul]
  have hl (i : ι) : L (P i)*L G=(w i : ℂ) • L (P i) := by
    apply LinearMap.ext
    intro x
    change P i*(G*x)=(w i : ℂ) • (P i*x)
    rw [← mul_assoc, left, smul_mul_assoc]
  have hr (i : ι) : L G*L (P i)=(w i : ℂ) • L (P i) := by
    apply LinearMap.ext
    intro x
    change G*(P i*x)=(w i : ℂ) • (P i*x)
    rw [← mul_assoc, right, smul_mul_assoc]
  have hword : ∀ T ∈ word.map L, L G*T=T*L G+T := by
    intro T hT
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hT
    apply LinearMap.ext
    intro x
    change G*(a*x)=a*(G*x)+a*x
    rw [← mul_assoc, laws a ha, add_mul, mul_assoc]
  have hzero := FiniteGradeModule.word_zero (L G) (fun i => L (P i)) w hres hl hr
    lower upper bounds (word.map L) hword (by simpa only [List.length_map] using long)
  have h := congrArg (fun T : Module.End ℂ A => T 1) hzero
  simpa only [L, left_words, mul_one, LinearMap.zero_apply] using h

def commutator (G : A) : Module.End ℂ A := LinearMap.mulLeft ℂ G-LinearMap.mulRight ℂ G
def sandwich (P Q : A) : Module.End ℂ A := (LinearMap.mulRight ℂ Q)*(LinearMap.mulLeft ℂ P)

theorem sandwich_resolution (P : ι → A) (resolution : ∑ i, P i=1) :
    ∑ i : ι × ι, sandwich (P i.1) (P i.2)=1 := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, Fintype.sum_prod_type, sandwich, Module.End.mul_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Module.End.one_apply]
  simp_rw [← Finset.mul_sum, resolution, mul_one]
  rw [← Finset.sum_mul, resolution, one_mul]

omit [Fintype ι] in
theorem sandwich_left (G : A) (P : ι → A) (w : ι → ℤ)
    (left : ∀ i, P i*G=(w i : ℂ) • P i) (right : ∀ i, G*P i=(w i : ℂ) • P i) (i j : ι) :
    sandwich (P i) (P j)*commutator G=((w i-w j : ℤ) : ℂ) • sandwich (P i) (P j) := by
  apply LinearMap.ext
  intro x
  change P i*(G*x-x*G)*P j=((w i-w j : ℤ) : ℂ) • (P i*x*P j)
  calc
    _ = (P i*G)*x*P j-P i*x*(G*P j) := by noncomm_ring
    _ = _ := by rw [left, right, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, Int.cast_sub, sub_smul]

omit [Fintype ι] in
theorem sandwich_right (G : A) (P : ι → A) (w : ι → ℤ)
    (left : ∀ i, P i*G=(w i : ℂ) • P i) (right : ∀ i, G*P i=(w i : ℂ) • P i) (i j : ι) :
    commutator G*sandwich (P i) (P j)=((w i-w j : ℤ) : ℂ) • sandwich (P i) (P j) := by
  apply LinearMap.ext
  intro x
  change G*(P i*x*P j)-(P i*x*P j)*G=((w i-w j : ℤ) : ℂ) • (P i*x*P j)
  calc
    _ = (G*P i)*x*P j-P i*x*(P j*G) := by noncomm_ring
    _ = _ := by rw [right, left, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, Int.cast_sub, sub_smul]

theorem commutator_raises (G B : A) (h : G*B=B*G+B) :
    commutator G*commutator B=commutator B*commutator G+commutator B := by
  have hg : G*B-B*G=B := by rw [h]; abel
  apply LinearMap.ext
  intro x
  change G*(B*x-x*B)-(B*x-x*B)*G = B*(G*x-x*G)-(G*x-x*G)*B+(B*x-x*B)
  calc
    _ = B*(G*x-x*G)-(G*x-x*G)*B+((G*B-B*G)*x-x*(G*B-B*G)) := by noncomm_ring
    _ = _ := by rw [hg]

theorem commutator_words_zero (G : A) (P : ι → A) (w : ι → ℤ)
    (resolution : ∑ i, P i=1) (left : ∀ i, P i*G=(w i : ℂ) • P i)
    (right : ∀ i, G*P i=(w i : ℂ) • P i) (lower upper : ℤ)
    (bounds : ∀ i, lower ≤ w i ∧ w i ≤ upper) (word : List A)
    (laws : ∀ T ∈ word, G*T=T*G+T) (long : 2*(upper-lower) < (word.length : ℤ)) :
    (word.map commutator).prod=0 := by
  apply FiniteGradeModule.word_zero (commutator G)
    (fun i : ι × ι => sandwich (P i.1) (P i.2)) (fun i => w i.1-w i.2)
    (sandwich_resolution P resolution)
    (fun i => sandwich_left G P w left right i.1 i.2)
    (fun i => sandwich_right G P w left right i.1 i.2) (lower-upper) (upper-lower)
  · intro i
    have hi := bounds i.1
    have hj := bounds i.2
    constructor <;> omega
  · intro T hT
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hT
    exact commutator_raises G b (laws b hb)
  · simp only [List.length_map]
    omega

theorem family_words_zero {τ : Type*} (G : A) (P : ι → A) (w : ι → ℤ)
    (resolution : ∑ i, P i=1) (left : ∀ i, P i*G=(w i : ℂ) • P i)
    (right : ∀ i, G*P i=(w i : ℂ) • P i) (lower upper : ℤ)
    (bounds : ∀ i, lower ≤ w i ∧ w i ≤ upper) (B : τ → A)
    (laws : ∀ t, G*B t=B t*G+B t) (times : List τ)
    (long : upper-lower < (times.length : ℤ)) : (times.map B).prod=0 := by
  apply words_zero G P w resolution left right lower upper bounds
  · intro a ha
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
    exact laws t
  · simpa only [List.length_map] using long

theorem family_commutators_zero {τ : Type*} (G : A) (P : ι → A) (w : ι → ℤ)
    (resolution : ∑ i, P i=1) (left : ∀ i, P i*G=(w i : ℂ) • P i)
    (right : ∀ i, G*P i=(w i : ℂ) • P i) (lower upper : ℤ)
    (bounds : ∀ i, lower ≤ w i ∧ w i ≤ upper) (B : τ → A)
    (laws : ∀ t, G*B t=B t*G+B t) (times : List τ)
    (long : 2*(upper-lower) < (times.length : ℤ)) :
    (times.map (fun t => commutator (B t))).prod=0 := by
  have h := commutator_words_zero G P w resolution left right lower upper bounds (times.map B)
    (by intro a ha; obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha; exact laws t)
    (by simpa only [List.length_map] using long)
  simpa only [List.map_map, Function.comp_def] using h

#print axioms words_zero
#print axioms commutator_words_zero
end LowEnergy.FiniteGradeAlgebra
