import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Core

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineClauseProduct

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Clause Formula clauseRead formulaRead Within)
open InterferenceProgram

def support (formula : Formula) : List Nat := (formula.flatten.flatMap Row.vars).dedup

theorem variable_mem (formula : Formula) (clause : Clause) (member : clause ∈ formula)
    (row : Row) (present : row ∈ clause) (i : Nat) (hit : i ∈ row.vars) : i ∈ support formula := by
  simp only [support,List.mem_dedup,List.mem_flatMap,List.mem_flatten]
  exact ⟨row,⟨clause,member,present⟩,hit⟩

theorem row_agree (row : Row) (left right : Nat → Bool) (agree : ∀ i ∈ row.vars, left i = right i) :
    row.holds left = row.holds right := by
  simp only [Row.holds,Row.eval]
  rw [Parity.eval_congr left right row.vars agree]

theorem clause_agree (clause : Clause) (left right : Nat → Bool)
    (agree : ∀ row ∈ clause, ∀ i ∈ row.vars, left i = right i) : clauseRead clause left = clauseRead clause right := by
  induction clause with
  | nil => rfl
  | cons row rest ih =>
      have first := row_agree row left right (agree row (by simp))
      have tail := ih (fun r member => agree r (by simp [member]))
      change (row.holds left || clauseRead rest left) = (row.holds right || clauseRead rest right)
      rw [first,tail]

theorem formula_agree (formula : Formula) (left right : Nat → Bool)
    (agree : ∀ clause ∈ formula, ∀ row ∈ clause, ∀ i ∈ row.vars, left i = right i) :
    formulaRead formula left = formulaRead formula right := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      have first := clause_agree clause left right (agree clause (by simp))
      have tail := ih (fun c member => agree c (by simp [member]))
      change (clauseRead clause left && formulaRead rest left) = (clauseRead clause right && formulaRead rest right)
      rw [first,tail]

def merge (source : Formula) (left right : Nat → Bool) : Nat → Bool :=
  fun i => if i ∈ support source then left i else right i

def Apart (left right : Formula) : Prop :=
  ∀ clause ∈ right, ∀ row ∈ clause, ∀ i ∈ row.vars, i ∉ support left

theorem merge_left (source : Formula) (left right : Nat → Bool) :
    formulaRead source (merge source left right) = formulaRead source left := by
  apply formula_agree
  intro clause member row present i hit
  simp [merge,variable_mem source clause member row present i hit]

theorem merge_right (source rest : Formula) (apart : Apart source rest) (left right : Nat → Bool) :
    formulaRead rest (merge source left right) = formulaRead rest right := by
  apply formula_agree
  intro clause member row present i hit
  simp [merge,apart clause member row present i hit]

def Satisfiable (formula : Formula) : Prop := ∃ assignment : Nat → Bool, formulaRead formula assignment = true

theorem separated_sat (left right : Formula) (apart : Apart left right) :
    Satisfiable (left++right) ↔ Satisfiable left ∧ Satisfiable right := by
  constructor
  · rintro ⟨assignment,accepted⟩
    have both : formulaRead left assignment = true ∧ formulaRead right assignment = true := by
      simpa only [formulaRead,List.all_append,Bool.and_eq_true] using accepted
    exact ⟨⟨assignment,both.1⟩,⟨assignment,both.2⟩⟩
  · rintro ⟨⟨leftPoint,first⟩,⟨rightPoint,second⟩⟩
    refine ⟨merge left leftPoint rightPoint,?_⟩
    simp only [formulaRead,List.all_append]
    change (formulaRead left (merge left leftPoint rightPoint) && formulaRead right (merge left leftPoint rightPoint)) = true
    rw [merge_left,merge_right left right apart,first,second]
    rfl

def touches (component : Formula) (clause : Clause) : Bool :=
  clause.any (fun row => row.vars.any (fun i => decide (i ∈ support component)))

def grow : Nat → Formula → Formula → Formula × Formula
  | 0,component,rest => (component,rest)
  | fuel+1,component,rest =>
      let moved := rest.filter (touches component)
      if moved = [] then (component,rest)
      else grow fuel (component++moved) (rest.filter (fun clause => !touches component clause))

theorem grow_members (fuel : Nat) (component rest : Formula) (clause : Clause) :
    clause ∈ (grow fuel component rest).1++(grow fuel component rest).2 ↔ clause ∈ component++rest := by
  induction fuel generalizing component rest with
  | zero => rfl
  | succ fuel ih =>
      simp only [grow]
      split
      · rfl
      · rw [ih]
        simp only [List.mem_append,List.mem_filter]
        cases touches component clause <;> simp

theorem no_touching_apart (component rest : Formula) (empty : rest.filter (touches component) = []) : Apart component rest := by
  intro clause member row present i hit
  have quiet : touches component clause = false :=
    Bool.eq_false_iff.mpr ((List.filter_eq_nil_iff.mp empty) clause member)
  have quietRow := (List.any_eq_false.mp quiet) row present
  exact of_decide_eq_false (Bool.eq_false_iff.mpr ((List.any_eq_false.mp (Bool.eq_false_iff.mpr quietRow)) i hit))

theorem grow_apart (fuel : Nat) (component rest : Formula) (enough : rest.length ≤ fuel) :
    Apart (grow fuel component rest).1 (grow fuel component rest).2 := by
  induction fuel generalizing component rest with
  | zero =>
      have empty : rest=[] := List.eq_nil_of_length_eq_zero (by omega)
      simp [grow,empty,Apart]
  | succ fuel ih =>
      simp only [grow]
      split
      · exact no_touching_apart component rest (by assumption)
      · rename_i nonempty
        apply ih
        have positive := List.length_pos_iff.mpr nonempty
        have account := List.length_eq_length_filter_add (l:=rest) (touches component)
        omega

theorem grow_rest_length (fuel : Nat) (component rest : Formula) : (grow fuel component rest).2.length ≤ rest.length := by
  induction fuel generalizing component rest with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      simp only [grow]
      split
      · exact Nat.le_refl _
      · exact (ih _ _).trans (List.length_filter_le _ _)

theorem formula_members (left right : Formula) (same : ∀ clause, clause ∈ left ↔ clause ∈ right) (assignment : Nat → Bool) :
    formulaRead left assignment = formulaRead right assignment := by
  apply Bool.eq_iff_iff.mpr
  simp only [formulaRead,List.all_eq_true]
  exact ⟨fun h c hc => h c ((same c).mpr hc),fun h c hc => h c ((same c).mp hc)⟩

theorem grow_read (clause : Clause) (rest : Formula) (assignment : Nat → Bool) :
    (formulaRead (grow rest.length [clause] rest).1 assignment && formulaRead (grow rest.length [clause] rest).2 assignment) =
      formulaRead (clause::rest) assignment := by
  have same := formula_members _ _ (grow_members rest.length [clause] rest) assignment
  simpa only [formulaRead,List.all_append,List.singleton_append] using same

theorem grow_within (n fuel : Nat) (component rest : Formula) (inside : Within n (component++rest)) :
    Within n (grow fuel component rest).1 ∧ Within n (grow fuel component rest).2 := by
  constructor
  · intro clause member
    exact inside clause ((grow_members fuel component rest clause).mp (List.mem_append_left _ member))
  · intro clause member
    exact inside clause ((grow_members fuel component rest clause).mp (List.mem_append_right _ member))

theorem formula_restrict (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Nat → Bool) :
    formulaRead formula (extendAssignment (fun i : Fin n => assignment i.val)) = formulaRead formula assignment := by
  apply formula_agree
  intro clause member row present i hit
  have bound := inside clause member row present i hit
  simp [extendAssignment,bound]

theorem model_image (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Assignment n) :
    (∃ parameter : AffineCarrier.Parameters n (AffineClauses.generate n formula).value,
      AffineCarrier.lift n (AffineClauses.generate n formula).value parameter = assignment) ↔
        formulaRead formula (extendAssignment assignment) = true := by
  rw [AffineCarrier.lift_image n _ (AffineClauses.generate_valid n formula inside),AffineClauses.generate_read n formula inside]

theorem model_possible (n : Nat) (formula : Formula) (inside : Within n formula) :
    (!(AffineClauses.generate n formula).value.isEmpty) = true ↔ Satisfiable formula := by
  rw [AffineCarrier.nonempty_iff n _ (AffineClauses.generate_valid n formula inside)]
  simp only [AffineClauses.generate_read n formula inside]
  constructor
  · rintro ⟨assignment,accepted⟩
    exact ⟨extendAssignment assignment,accepted⟩
  · rintro ⟨assignment,accepted⟩
    exact ⟨(fun i => assignment i.val),(formula_restrict n formula inside assignment).trans accepted⟩

inductive Tree (n : Nat) where
  | unit
  | part (source : Formula) (model : AffineCollect.Execution) (rest : Tree n)

def read {n : Nat} : Tree n → (Nat → Bool) → Bool
  | .unit,_ => true
  | .part _ model rest,assignment => AffineCarrier.read model.value assignment && read rest assignment

def possible {n : Nat} : Tree n → Bool
  | .unit => true
  | .part _ model rest => !model.value.isEmpty && possible rest

def storedCells {n : Nat} : Tree n → Nat
  | .unit => 0
  | .part _ model rest => model.value.length+storedCells rest

def parts {n : Nat} : Tree n → Nat
  | .unit => 0
  | .part _ _ rest => 1+parts rest

def build (n : Nat) : Nat → Formula → Tree n
  | _,[] => .unit
  | 0,formula => .part formula (AffineClauses.generate n formula) .unit
  | fuel+1,clause::rest =>
      let factors := grow rest.length [clause] rest
      .part factors.1 (AffineClauses.generate n factors.1) (build n fuel factors.2)

theorem build_read (n fuel : Nat) (formula : Formula) (inside : Within n formula) (assignment : Nat → Bool) :
    read (build n fuel formula) assignment = formulaRead formula assignment := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [build,read,AffineClauses.generate_read n _ inside,formulaRead]
  | succ fuel ih =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          have bounds := grow_within n rest.length [clause] rest inside
          simp only [build,read,AffineClauses.generate_read n _ bounds.1,ih _ bounds.2]
          exact grow_read clause rest assignment

theorem build_possible (n fuel : Nat) (formula : Formula) (inside : Within n formula) :
    possible (build n fuel formula) = true ↔ Satisfiable formula := by
  induction fuel generalizing formula with
  | zero =>
      cases formula with
      | nil => simp [build,possible,Satisfiable,formulaRead]
      | cons clause rest => simpa only [build,possible,Bool.and_true] using model_possible n _ inside
  | succ fuel ih =>
      cases formula with
      | nil => simp [build,possible,Satisfiable,formulaRead]
      | cons clause rest =>
          have bounds := grow_within n rest.length [clause] rest inside
          simp only [build,possible,Bool.and_eq_true,model_possible n _ bounds.1,ih _ bounds.2]
          rw [← separated_sat _ _ (grow_apart rest.length [clause] rest (Nat.le_refl _))]
          apply exists_congr
          intro assignment
          rw [formula_members _ _ (grow_members rest.length [clause] rest) assignment]
          rfl

def Parameters {n : Nat} : Tree n → Type
  | .unit => Assignment n
  | .part _ model rest => AffineCarrier.Parameters n model.value × Parameters rest

def lift {n : Nat} : (tree : Tree n) → Parameters tree → Assignment n
  | .unit,parameter => parameter
  | .part source model rest,parameter =>
      let left := AffineCarrier.lift n model.value parameter.1
      let right := lift rest parameter.2
      fun i => merge source (extendAssignment left) (extendAssignment right) i.val

theorem lift_fixes {n : Nat} (source : Formula) (model : AffineCollect.Execution) (rest : Tree n)
    (left : AffineCarrier.Parameters n model.value) (right : Parameters rest) (assignment : Assignment n)
    (first : AffineCarrier.lift n model.value left = assignment) (second : lift rest right = assignment) :
    lift (.part source model rest) (left,right) = assignment := by
  funext i
  simp [lift,first,second,merge,extendAssignment]

theorem build_image (n fuel : Nat) (formula : Formula) (inside : Within n formula) (assignment : Assignment n) :
    (∃ parameter : Parameters (build n fuel formula), lift (build n fuel formula) parameter = assignment) ↔
      formulaRead formula (extendAssignment assignment) = true := by
  induction fuel generalizing formula assignment with
  | zero =>
      cases formula with
      | nil =>
          change (∃ parameter : Assignment n, parameter = assignment) ↔ true = true
          exact ⟨fun _ => rfl,fun _ => ⟨assignment,rfl⟩⟩
      | cons clause rest =>
          constructor
          · rintro ⟨⟨left,right⟩,rfl⟩
            let source := clause::rest
            let model := AffineClauses.generate n source
            have first := (model_image n source inside (AffineCarrier.lift n model.value left)).mp ⟨left,rfl⟩
            exact (formula_restrict n source inside (merge source
              (extendAssignment (AffineCarrier.lift n model.value left)) (extendAssignment right))).trans
                ((merge_left source _ _).trans first)
          · intro accepted
            obtain ⟨parameter,same⟩ := (model_image n (clause::rest) inside assignment).mpr accepted
            exact ⟨(parameter,assignment),lift_fixes _ _ .unit parameter assignment assignment same rfl⟩
  | succ fuel ih =>
      cases formula with
      | nil =>
          change (∃ parameter : Assignment n, parameter = assignment) ↔ true = true
          exact ⟨fun _ => rfl,fun _ => ⟨assignment,rfl⟩⟩
      | cons clause rest =>
          let factors := grow rest.length [clause] rest
          have bounds := grow_within n rest.length [clause] rest inside
          have apart := grow_apart rest.length [clause] rest (Nat.le_refl _)
          constructor
          · rintro ⟨⟨left,right⟩,rfl⟩
            let a := AffineCarrier.lift n (AffineClauses.generate n factors.1).value left
            let b := lift (build n fuel factors.2) right
            have first : formulaRead factors.1 (extendAssignment a) = true :=
              (model_image n factors.1 bounds.1 a).mp ⟨left,rfl⟩
            have second : formulaRead factors.2 (extendAssignment b) = true :=
              (ih factors.2 bounds.2 b).mp ⟨right,rfl⟩
            have joined : formulaRead (clause::rest) (merge factors.1 (extendAssignment a) (extendAssignment b)) = true := by
              rw [← grow_read clause rest]
              rw [merge_left,merge_right factors.1 factors.2 apart,first,second]
              rfl
            exact (formula_restrict n (clause::rest) inside _).trans joined
          · intro accepted
            have both := (grow_read clause rest (extendAssignment assignment)).trans accepted
            have facts : formulaRead factors.1 (extendAssignment assignment) = true ∧
                formulaRead factors.2 (extendAssignment assignment) = true := by simpa using both
            obtain ⟨first,second⟩ := facts
            obtain ⟨left,firstEq⟩ := (model_image n factors.1 bounds.1 assignment).mpr first
            obtain ⟨right,secondEq⟩ := (ih factors.2 bounds.2 assignment).mpr second
            exact ⟨(left,right),lift_fixes factors.1 _ _ left right assignment firstEq secondEq⟩

def generate (n : Nat) (formula : Formula) : Tree n :=
  let cleaned := AffineClauses.cleanRun formula
  build n cleaned.value.length cleaned.value

theorem generate_read (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Nat → Bool) :
    read (generate n formula) assignment = formulaRead formula assignment := by
  rw [generate,AffineClauses.cleanRun_value,build_read n _ _ (AffineClauses.clean_within n formula inside),AffineClauses.clean_read]

theorem generate_image (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Assignment n) :
    (∃ parameter : Parameters (generate n formula), lift (generate n formula) parameter = assignment) ↔
      formulaRead formula (extendAssignment assignment) = true := by
  rw [generate,AffineClauses.cleanRun_value,build_image n _ _ (AffineClauses.clean_within n formula inside),AffineClauses.clean_read]

theorem generate_possible (n : Nat) (formula : Formula) (inside : Within n formula) :
    possible (generate n formula) = true ↔ Satisfiable formula := by
  rw [generate,AffineClauses.cleanRun_value,build_possible n _ _ (AffineClauses.clean_within n formula inside)]
  apply exists_congr
  intro assignment
  rw [AffineClauses.clean_read]

end SaturationMonoid.ComplexityProjection.SATSource.AffineClauseProduct
