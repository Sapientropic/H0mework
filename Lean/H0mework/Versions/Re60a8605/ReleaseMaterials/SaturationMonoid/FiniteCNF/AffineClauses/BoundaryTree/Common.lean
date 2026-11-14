import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.FutureCost

/-! Shared source supports and exact row-CNF boundary fibres. A joint
    realization retains agreement on every shared address before projection
    to the requested outputs. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.CouncilCommon
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Formula Clause formulaRead Within)
open AffineClauseProduct (support Satisfiable)

def overlap (left right : Formula) : List Nat :=
  (support left).filter (fun i => decide (i ∈ support right))

theorem overlap_mem (left right : Formula) (i : Nat) :
    i ∈ overlap left right ↔ i ∈ support left ∧ i ∈ support right := by
  simp [overlap]

theorem merge_right_common (left right : Formula) (a b : Nat → Bool)
    (common : ∀ i ∈ overlap left right, a i=b i) :
    formulaRead right (AffineClauseProduct.merge left a b)=formulaRead right b := by
  apply AffineClauseProduct.formula_agree
  intro clause member row present i hit
  have retained := AffineClauseProduct.variable_mem right clause member row present i hit
  by_cases inLeft : i ∈ support left
  · simp only [AffineClauseProduct.merge,if_pos inLeft]
    exact common i ((overlap_mem left right i).mpr ⟨inLeft,retained⟩)
  · simp only [AffineClauseProduct.merge,if_neg inLeft]

theorem same_source_join (left right : Formula) :
    Satisfiable (left++right) ↔ ∃ a b : Nat → Bool,
      formulaRead left a=true ∧ formulaRead right b=true ∧
        ∀ i ∈ overlap left right, a i=b i := by
  constructor
  · rintro ⟨point,accepted⟩
    have both : formulaRead left point=true ∧ formulaRead right point=true := by
      simpa only [formulaRead,List.all_append,Bool.and_eq_true] using accepted
    exact ⟨point,point,both.1,both.2,fun _ _ => rfl⟩
  · rintro ⟨a,b,first,second,common⟩
    refine ⟨AffineClauseProduct.merge left a b,?_⟩
    simp only [formulaRead,List.all_append]
    change (formulaRead left (AffineClauseProduct.merge left a b) &&
      formulaRead right (AffineClauseProduct.merge left a b))=true
    rw [AffineClauseProduct.merge_left,merge_right_common left right a b common,first,second]
    rfl

/-- The exact source responsibility of one boundary message. -/
def Realizes (source : Formula) (keep : List Nat) (point : Nat → Bool) : Prop :=
  ∃ before : Nat → Bool, formulaRead source before=true ∧ ∀ i ∈ keep, before i=point i

def boundary (source outside : Formula) (keep : List Nat) : List Nat :=
  (support source).filter (fun i => decide (i ∈ support outside ∨ i ∈ keep))

theorem boundary_mem (source outside : Formula) (keep : List Nat) (i : Nat) :
    i ∈ boundary source outside keep ↔ i ∈ support source ∧ (i ∈ support outside ∨ i ∈ keep) := by
  simp [boundary]

theorem source_message_join (left right : Formula) (keep : List Nat) (point : Nat → Bool) :
    Realizes (left++right) keep point ↔ ∃ middle : Nat → Bool,
      Realizes left (boundary left right keep) middle ∧
      Realizes right (boundary right left keep) middle ∧ ∀ i ∈ keep, middle i=point i := by
  constructor
  · rintro ⟨before,accepted,agrees⟩
    have both : formulaRead left before=true ∧ formulaRead right before=true := by
      simpa only [formulaRead,List.all_append,Bool.and_eq_true] using accepted
    exact ⟨before,⟨before,both.1,fun _ _ => rfl⟩,⟨before,both.2,fun _ _ => rfl⟩,agrees⟩
  · rintro ⟨middle,⟨a,acceptedA,agreesA⟩,⟨b,acceptedB,agreesB⟩,outside⟩
    let assembled := AffineClauseProduct.merge left a (AffineClauseProduct.merge right b middle)
    refine ⟨assembled,?_,?_⟩
    · have common : ∀ i ∈ overlap left right, a i=(AffineClauseProduct.merge right b middle) i := by
        intro i member
        obtain ⟨inLeft,inRight⟩ := (overlap_mem left right i).mp member
        have first := agreesA i ((boundary_mem left right keep i).mpr ⟨inLeft,Or.inl inRight⟩)
        have second := agreesB i ((boundary_mem right left keep i).mpr ⟨inRight,Or.inl inLeft⟩)
        simp only [AffineClauseProduct.merge,if_pos inRight]
        exact first.trans second.symm
      simp only [formulaRead,List.all_append]
      change (formulaRead left assembled && formulaRead right assembled)=true
      rw [show formulaRead left assembled=formulaRead left a from AffineClauseProduct.merge_left _ _ _,
        show formulaRead right assembled=formulaRead right (AffineClauseProduct.merge right b middle) from
          merge_right_common left right a (AffineClauseProduct.merge right b middle) common,
        AffineClauseProduct.merge_left,acceptedA,acceptedB]
      rfl
    · intro i retained
      by_cases inLeft : i ∈ support left
      · change (if i ∈ support left then a i else _)=point i
        rw [if_pos inLeft]
        exact (agreesA i ((boundary_mem left right keep i).mpr ⟨inLeft,Or.inr retained⟩)).trans (outside i retained)
      · by_cases inRight : i ∈ support right
        · change (if i ∈ support left then a i else (if i ∈ support right then b i else middle i))=point i
          rw [if_neg inLeft,if_pos inRight]
          exact (agreesB i ((boundary_mem right left keep i).mpr ⟨inRight,Or.inr retained⟩)).trans (outside i retained)
        · change (if i ∈ support left then a i else (if i ∈ support right then b i else middle i))=point i
          rw [if_neg inLeft,if_neg inRight]
          exact outside i retained

def leaf (n : Nat) (keep : List Nat) (clause : Clause) : AffineCarrier.Cells :=
  (AffineForget.Cost.cells n keep (AffineClauses.clauseAction clause [[]]).value).value

def join (n : Nat) (keep : List Nat) (left right : AffineCarrier.Cells) : AffineCarrier.Cells :=
  left.flatMap fun a => right.flatMap fun b =>
    (AffineForget.Cost.cells n keep (AffineCarrier.pack (EliminateCost.runFrom (.basis a) b).result).value).value

end SaturationMonoid.ComplexityProjection.SATSource.CouncilCommon
