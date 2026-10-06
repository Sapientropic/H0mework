import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationReciprocalFold

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumReciprocalBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol
open PreparationVacuumMoyalBudget
open scoped BigOperators

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

def CanonicalList (vs : List Phase) : Prop :=
  ∀ v∈vs, ∃ s : Slot, v=slotDirection s

theorem canonicalList_tail {v : Phase} {vs : List Phase} (hc : CanonicalList (v::vs)) :
    CanonicalList vs := fun w hw => hc w (List.mem_cons_of_mem v hw)

theorem canonicalList_splits {vs : List Phase} (hc : CanonicalList vs) (s : Split)
    (member : s∈wordSplittings vs) : CanonicalList s.1 ∧ CanonicalList s.2 := by
  induction vs generalizing s with
  | nil =>
    simp only [wordSplittings_nil,List.mem_singleton] at member
    subst s
    constructor <;> intro v h <;> simp at h
  | cons v vs ih =>
    have head := hc v (List.mem_cons_self)
    have tail := canonicalList_tail hc
    rw [wordSplittings_cons,List.mem_append] at member
    rcases member with member|member
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp member
      have paid := ih tail t ht
      refine ⟨paid.1,?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with same|rest
      · simpa only [same] using head
      · exact paid.2 w rest
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp member
      have paid := ih tail t ht
      refine ⟨?_,paid.2⟩
      intro w hw
      rcases List.mem_cons.mp hw with same|rest
      · simpa only [same] using head
      · exact paid.1 w rest

theorem tail_split_nonempty (v : Phase) (vs : List Phase) (s : Split)
    (member : s∈(wordSplittings (v::vs)).tail) : s.1.length ≠ 0 := by
  have count := wordSplittings_left_count (v::vs) 0
  rw [wordSplittings_head] at count
  have emptyCount : ((wordSplittings (v::vs)).tail).countP (fun t => t.1.length==0)=0 := by
    simpa using count
  intro zero
  have positive : 0 < ((wordSplittings (v::vs)).tail).countP (fun t => t.1.length==0) := by
    apply List.countP_pos_iff.mpr
    exact ⟨s,member,by simpa using zero⟩
  omega

theorem tail_split_short (v : Phase) (vs : List Phase) (s : Split)
    (member : s∈(wordSplittings (v::vs)).tail) : s.2.length < vs.length+1 := by
  have actualMember : s∈wordSplittings (v::vs) := List.mem_of_mem_tail member
  have lengths := wordSplittings_lengths (v::vs) s actualMember
  have nonempty := tail_split_nonempty v vs s member
  simp only [List.length_cons] at lengths
  omega

theorem tail_split_convolution (v : Phase) (vs : List Phase) (B U : ℕ → ℝ) :
    (((wordSplittings (v::vs)).tail).map (fun s => B s.1.length*U s.2.length)).sum=
      ∑ r : Fin (vs.length+1),((vs.length+1).choose (r.val+1) : ℝ)*B (r.val+1)*U (vs.length-r.val) := by
  let B0 : ℕ → ℝ := fun n => if n=0 then 0 else B n
  have replace : (((wordSplittings (v::vs)).tail).map (fun s => B s.1.length*U s.2.length)).sum=
      (((wordSplittings (v::vs)).tail).map (fun s => B0 s.1.length*U s.2.length)).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    simp only [B0,if_neg (tail_split_nonempty v vs s hs)]
  have full := split_convolution (v::vs) 0 B0 U
  rw [wordSplittings_head] at full
  simp only [List.map_cons,List.sum_cons,List.length_nil,B0,if_true,zero_mul,zero_add,
    List.length_cons] at full
  rw [replace,full]
  unfold convolution
  rw [Finset.sum_range_succ']
  simp only [if_true,mul_zero,zero_mul,add_zero,zero_add,
    Nat.succ_ne_zero,if_false]
  have reindex := Fin.sum_univ_eq_sum_range
    (fun r => ((vs.length+1).choose (r+1) : ℝ)*B (r+1)*U (vs.length-r)) (vs.length+1)
  rw [reindex]
  apply Finset.sum_congr rfl
  intro r hr
  congr 2
  omega

end LowEnergy.PreparationVacuumReciprocalBudget
