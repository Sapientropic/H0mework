import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCarrier.Cost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Factor

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineProduct

open SaturationMonoid.ComplexityProjection.SATSource.Affine

/-- Each component keeps its generated carrier; no Cartesian list of cells is formed. -/
inductive Tree (n : Nat) where
  | unit
  | part (source : CNFFormula n) (model : AffineCarrier.Execution) (rest : Tree n)

def read {n : Nat} : Tree n → (Nat → Bool) → Bool
  | .unit,_ => true
  | .part _ model rest,assignment => AffineCarrier.read model.value assignment && read rest assignment

def possible {n : Nat} : Tree n → Bool
  | .unit => true
  | .part _ model rest => !model.value.isEmpty && possible rest

def storedCells {n : Nat} : Tree n → Nat
  | .unit => 0
  | .part _ model rest => model.value.length+storedCells rest

def modelVisits {n : Nat} : Tree n → Nat
  | .unit => 0
  | .part _ model rest => model.visits+modelVisits rest

def parts {n : Nat} : Tree n → Nat
  | .unit => 0
  | .part _ _ rest => 1+parts rest

def build {n : Nat} : Nat → CNFFormula n → Tree n
  | _,[] => .unit
  | 0,formula => .part formula (AffineCarrier.generate formula) .unit
  | fuel+1,clause::rest =>
      let factors := Factor.grow rest.length [clause] rest
      .part factors.1 (AffineCarrier.generate factors.1) (build fuel factors.2)

theorem grow_read {n : Nat} (clause : CNFClause n) (rest : CNFFormula n) (assignment : Nat → Bool) :
    (CNFFormula.eval (Factor.grow rest.length [clause] rest).1 assignment &&
      CNFFormula.eval (Factor.grow rest.length [clause] rest).2 assignment) =
        CNFFormula.eval (clause::rest) assignment := by
  have same := Factor.formula_eval_of_members _ _ (Factor.grow_members rest.length [clause] rest) assignment
  simpa only [CNFFormula.eval,List.all_append,List.singleton_append] using same

theorem build_read {n : Nat} (fuel : Nat) (formula : CNFFormula n) (assignment : Nat → Bool) :
    read (build fuel formula) assignment = CNFFormula.eval formula assignment := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [build,read,AffineCarrier.generate_read,CNFFormula.eval]
  | succ fuel ih =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          simp only [build,read,AffineCarrier.generate_read,ih]
          exact grow_read clause rest assignment

theorem build_possible {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    possible (build fuel formula) = true ↔ CNFSatisfiable formula := by
  induction fuel generalizing formula with
  | zero =>
      cases formula with
      | nil => simp [build,possible,CNFSatisfiable,CNFFormula.eval]
      | cons clause rest =>
          change (AffineCarrier.decideFormula (clause::rest) && true) = true ↔ _
          simp only [Bool.and_true,AffineCarrier.decideFormula_correct]
  | succ fuel ih =>
      cases formula with
      | nil => simp [build,possible,CNFSatisfiable,CNFFormula.eval]
      | cons clause rest =>
          change (AffineCarrier.decideFormula (Factor.grow rest.length [clause] rest).1 &&
            possible (build fuel (Factor.grow rest.length [clause] rest).2)) = true ↔ _
          simp only [Bool.and_eq_true,AffineCarrier.decideFormula_correct,ih]
          exact (Factor.grow_sat rest.length [clause] rest (Nat.le_refl _)).symm

theorem build_parts {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    parts (build fuel formula) ≤ formula.length := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [build,parts]
  | succ fuel ih =>
      cases formula with
      | nil => simp [build,parts]
      | cons clause rest =>
          have tail := ih (Factor.grow rest.length [clause] rest).2
          have size := Factor.grow_rest_length_le rest.length [clause] rest
          simp only [build,parts,List.length_cons]
          omega

def Parameters {n : Nat} : Tree n → Type
  | .unit => Assignment n
  | .part _ model rest => AffineCarrier.Parameters n model.value × Parameters rest

def lift {n : Nat} : (tree : Tree n) → Parameters tree → Assignment n
  | .unit,parameter => parameter
  | .part source model rest,parameter =>
      let left := AffineCarrier.lift n model.value parameter.1
      let right := lift rest parameter.2
      fun i => Factor.mergeAssignment source (extendAssignment left) (extendAssignment right) i.val

theorem merge_left {n : Nat} (source : CNFFormula n) (left right : Nat → Bool) :
    CNFFormula.eval source (Factor.mergeAssignment source left right) = CNFFormula.eval source left := by
  apply Factor.formula_eval_agree
  intro clause member literal present
  have owned : literal.var.val ∈ (Shared.sourceVars source).map Fin.val :=
    List.mem_map.mpr ⟨literal.var,Shared.sourceVars_supported source clause member literal present,rfl⟩
  simp [Factor.mergeAssignment,owned]

theorem merge_right {n : Nat} (source rest : CNFFormula n) (apart : Factor.Separated source rest)
    (left right : Nat → Bool) :
    CNFFormula.eval rest (Factor.mergeAssignment source left right) = CNFFormula.eval rest right := by
  apply Factor.formula_eval_agree
  intro clause member literal present
  have unowned : literal.var.val ∉ (Shared.sourceVars source).map Fin.val := by
    intro owned
    obtain ⟨i,inside,same⟩ := List.mem_map.mp owned
    exact apart clause member literal present (Fin.ext same ▸ inside)
  simp [Factor.mergeAssignment,unowned]

theorem lift_fixes {n : Nat} (source : CNFFormula n) (model : AffineCarrier.Execution) (rest : Tree n)
    (left : AffineCarrier.Parameters n model.value) (right : Parameters rest) (assignment : Assignment n)
    (first : AffineCarrier.lift n model.value left = assignment) (second : lift rest right = assignment) :
    lift (.part source model rest) (left,right) = assignment := by
  funext i
  simp [lift,first,second,Factor.mergeAssignment,extendAssignment]

theorem build_image {n : Nat} (fuel : Nat) (formula : CNFFormula n) (assignment : Assignment n) :
    (∃ parameter : Parameters (build fuel formula), lift (build fuel formula) parameter = assignment) ↔
      CNFFormula.eval formula (extendAssignment assignment) = true := by
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
            let model := AffineCarrier.generate source
            have first := (AffineCarrier.generate_image source (AffineCarrier.lift n model.value left)).mp ⟨left,rfl⟩
            exact (formula_eval_restrict source (Factor.mergeAssignment source
              (extendAssignment (AffineCarrier.lift n model.value left)) (extendAssignment right))).trans
                ((merge_left source _ _).trans first)
          · intro accepted
            obtain ⟨parameter,same⟩ := (AffineCarrier.generate_image (clause::rest) assignment).mpr accepted
            exact ⟨(parameter,assignment),lift_fixes _ _ .unit parameter assignment assignment same rfl⟩
  | succ fuel ih =>
      cases formula with
      | nil =>
          change (∃ parameter : Assignment n, parameter = assignment) ↔ true = true
          exact ⟨fun _ => rfl,fun _ => ⟨assignment,rfl⟩⟩
      | cons clause rest =>
          let factors := Factor.grow rest.length [clause] rest
          have apart := Factor.grow_separated rest.length [clause] rest (Nat.le_refl _)
          constructor
          · rintro ⟨⟨left,right⟩,rfl⟩
            let a := AffineCarrier.lift n (AffineCarrier.generate factors.1).value left
            let b := lift (build fuel factors.2) right
            have first : CNFFormula.eval factors.1 (extendAssignment a) = true :=
              (AffineCarrier.generate_image factors.1 a).mp ⟨left,rfl⟩
            have second : CNFFormula.eval factors.2 (extendAssignment b) = true :=
              (ih factors.2 b).mp ⟨right,rfl⟩
            have joined : CNFFormula.eval (clause::rest)
                (Factor.mergeAssignment factors.1 (extendAssignment a) (extendAssignment b)) = true := by
              rw [← grow_read clause rest]
              rw [merge_left,merge_right factors.1 factors.2 apart,first,second]
              rfl
            exact (formula_eval_restrict (clause::rest) _).trans joined
          · intro accepted
            have both := (grow_read clause rest (extendAssignment assignment)).trans accepted
            have facts : CNFFormula.eval factors.1 (extendAssignment assignment) = true ∧
                CNFFormula.eval factors.2 (extendAssignment assignment) = true := by simpa using both
            obtain ⟨first,second⟩ := facts
            obtain ⟨left,firstEq⟩ := (AffineCarrier.generate_image factors.1 assignment).mpr first
            obtain ⟨right,secondEq⟩ := (ih factors.2 assignment).mpr second
            exact ⟨(left,right),lift_fixes factors.1 _ _ left right assignment firstEq secondEq⟩

def generate {n : Nat} (formula : CNFFormula n) : Tree n := build formula.length formula

theorem generate_read {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    read (generate formula) assignment = CNFFormula.eval formula assignment := build_read _ _ _

theorem generate_image {n : Nat} (formula : CNFFormula n) (assignment : Assignment n) :
    (∃ parameter : Parameters (generate formula), lift (generate formula) parameter = assignment) ↔
      CNFFormula.eval formula (extendAssignment assignment) = true := build_image _ _ _

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool := possible (generate formula)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := build_possible _ _

def sourceAction {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  fun assignment => if read (generate formula) (extendAssignment assignment) then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (source : Source n) :
    zeroProjector formula source = sourceAction formula source := by
  funext assignment
  simp only [sourceAction,zeroProjector_apply,generate_read]

def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with
  | none => false
  | some input => decideFormula input.2

theorem decideBits_eq_original (bits : List Bool) : decideBits bits = Encoding.decideBits bits := by
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits,Encoding.decideBits,parsed]
  | some input =>
      simp only [decideBits,Encoding.decideBits,parsed]
      apply Bool.eq_iff_iff.mpr
      rw [decideFormula_correct,Dense.decideFormula_correct]

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original,Encoding.decideBits_iff_rootVerify]

end SaturationMonoid.ComplexityProjection.SATSource.AffineProduct
