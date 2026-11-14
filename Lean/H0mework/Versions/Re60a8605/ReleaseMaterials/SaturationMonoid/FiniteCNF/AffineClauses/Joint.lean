import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Cost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Product
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCollect.Joint
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCollect.JointCost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Seed

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.Joint
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineCarrier (Cells Valid Separated read)

-- These invariants come from the actual original row action, before any cover test.
theorem branches_separated (clause : Clause) (result : Result) : Separated (branches clause result).value := by
  induction clause generalizing result with
  | nil => simp [branches,Separated]
  | cons row rest ih =>
      apply AffineCarrier.separated_append _ _ (AffineCarrier.pack_separated _) (ih _)
      intro assignment
      rw [AffineCarrier.read_pack,branches_read,EliminateCost.insert_result,EliminateCost.insert_result,
        Result.insert_holds,Result.insert_holds,Propagation.flip_holds]
      cases result.holds assignment <;> cases row.holds assignment <;> cases clauseRead rest assignment <;> rfl

theorem cut_separated (clause : Clause) (result : Result) : Separated (cut clause result).value := by
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.flip)).result with
  | contradiction => simpa only [cut,checked] using AffineCarrier.pack_separated result
  | basis basis => simpa only [cut,checked] using branches_separated clause result

theorem action_separated (clause : Clause) (cells : Cells) (separate : Separated cells) :
    Separated (clauseAction clause cells).value := by
  induction cells with
  | nil => simp [clauseAction,Separated]
  | cons basis rest ih =>
      apply AffineCarrier.separated_append _ _ (cut_separated clause (.basis basis)) (ih (List.pairwise_cons.mp separate).2)
      intro assignment
      have before := AffineCarrier.separated_cons basis rest separate assignment
      rw [cut_read,clauseAction_read]
      change ((holds basis assignment && clauseRead clause assignment) &&
        (read rest assignment && clauseRead clause assignment)) = false
      cases first : holds basis assignment <;> cases last : read rest assignment <;>
        cases clauseRead clause assignment <;> simp_all

theorem read_restrict (n : Nat) (cells : Cells) (valid : Valid n cells) (assignment : Nat → Bool) :
    read cells (extendAssignment (fun i : Fin n => assignment i.val)) = read cells assignment := by
  induction cells with
  | nil => rfl
  | cons basis rest ih =>
      have first := AtomSource.holds_restrict n basis (valid basis (by simp)).2 assignment
      have tail := ih (fun b member => valid b (by simp [member]))
      change (holds basis (extendAssignment (fun i : Fin n => assignment i.val)) ||
        read rest (extendAssignment (fun i : Fin n => assignment i.val))) = _
      rw [first,tail]
      rfl

def step (n : Nat) (clause : Clause) (cells : Cells) : Cells :=
  let cut := clauseAction clause cells
  let shared := AffineCollect.collect n cut.value
  (AffineJointCover.Cost.compact n shared.value).value

theorem step_valid (n : Nat) (clause : Clause) (inside : RowsWithin n clause) (cells : Cells) (valid : Valid n cells) :
    Valid n (step n clause cells) :=
  AffineJointCover.Cost.compact_valid n _ (AffineCollect.collect_valid n _ (clauseAction_valid n clause inside cells valid))

theorem step_separated (n : Nat) (clause : Clause) (inside : RowsWithin n clause) (cells : Cells)
    (valid : Valid n cells) (separated : Separated cells) : Separated (step n clause cells) :=
  AffineJointCover.Cost.compact_separated n _ (AffineCollect.collect_separated n _
    (clauseAction_valid n clause inside cells valid) (action_separated clause cells separated))

theorem step_read (n : Nat) (clause : Clause) (inside : RowsWithin n clause) (cells : Cells)
    (valid : Valid n cells) (separated : Separated cells) (assignment : Nat → Bool) :
    read (step n clause cells) assignment = (read cells assignment && clauseRead clause assignment) := by
  have cutValid := clauseAction_valid n clause inside cells valid
  have sharedValid := AffineCollect.collect_valid n _ cutValid
  have sharedSeparated := AffineCollect.collect_separated n _ cutValid (action_separated clause cells separated)
  have exactRead := AffineJointCover.Cost.compact_read n _ sharedValid sharedSeparated (fun i => assignment i.val)
  rw [read_restrict n _ (AffineJointCover.Cost.compact_valid n _ sharedValid),read_restrict n _ sharedValid] at exactRead
  rw [step,exactRead,AffineCollect.collect_read n _ cutValid,clauseAction_read]

def run (n : Nat) : Formula → Cells → Cells
  | [],cells => cells
  | clause::rest,cells => run n rest (step n clause cells)

theorem run_valid (n : Nat) (formula : Formula) (inside : Within n formula) (cells : Cells) (valid : Valid n cells) :
    Valid n (run n formula cells) := by
  induction formula generalizing cells with
  | nil => exact valid
  | cons clause rest ih =>
      exact ih (fun c member => inside c (by simp [member])) _ (step_valid n clause (inside clause (by simp)) cells valid)

theorem run_separated (n : Nat) (formula : Formula) (inside : Within n formula) (cells : Cells)
    (valid : Valid n cells) (separated : Separated cells) : Separated (run n formula cells) := by
  induction formula generalizing cells with
  | nil => exact separated
  | cons clause rest ih =>
      exact ih (fun c member => inside c (by simp [member])) _ (step_valid n clause (inside clause (by simp)) cells valid)
        (step_separated n clause (inside clause (by simp)) cells valid separated)

theorem run_read (n : Nat) (formula : Formula) (inside : Within n formula) (cells : Cells)
    (valid : Valid n cells) (separated : Separated cells) (assignment : Nat → Bool) :
    read (run n formula cells) assignment = (read cells assignment && formulaRead formula assignment) := by
  induction formula generalizing cells with
  | nil => simp [run,formulaRead]
  | cons clause rest ih =>
      rw [run,ih (fun c member => inside c (by simp [member])) _
        (step_valid n clause (inside clause (by simp)) cells valid)
        (step_separated n clause (inside clause (by simp)) cells valid separated),
        step_read n clause (inside clause (by simp)) cells valid separated]
      simp [formulaRead,Bool.and_assoc]

def generate (n : Nat) (formula : Formula) : Cells :=
  let prepared := cleanRun formula
  let initial := Seed.generate prepared.value
  run n prepared.value (AffineCarrier.pack initial.value).value

theorem empty_valid (n : Nat) : Valid n [[]] := by
  intro basis member
  have same : basis=[] := List.mem_singleton.mp member
  subst basis
  exact ⟨triangular_nil,by simp [RowsWithin]⟩

theorem generate_valid (n : Nat) (formula : Formula) (inside : Within n formula) : Valid n (generate n formula) := by
  have initial := Seed.generate_valid n (clean formula) (clean_within n formula inside)
  rw [generate,cleanRun_value]
  exact run_valid n _ (clean_within n formula inside) _ (AffineCarrier.pack_valid n _ initial.1 initial.2)

theorem generate_separated (n : Nat) (formula : Formula) (inside : Within n formula) : Separated (generate n formula) := by
  have initial := Seed.generate_valid n (clean formula) (clean_within n formula inside)
  rw [generate,cleanRun_value]
  exact run_separated n _ (clean_within n formula inside) _ (AffineCarrier.pack_valid n _ initial.1 initial.2)
    (AffineCarrier.pack_separated _)

theorem generate_read (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Nat → Bool) :
    read (generate n formula) assignment = formulaRead formula assignment := by
  have initial := Seed.generate_valid n (clean formula) (clean_within n formula inside)
  rw [generate,cleanRun_value,run_read n _ (clean_within n formula inside) _
    (AffineCarrier.pack_valid n _ initial.1 initial.2) (AffineCarrier.pack_separated _),AffineCarrier.read_pack,
    Seed.generate_read,clean_read]

theorem generate_image (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Assignment n) :
    (∃ p : AffineCarrier.Parameters n (generate n formula), AffineCarrier.lift n (generate n formula) p=assignment) ↔
      formulaRead formula (extendAssignment assignment) = true := by
  rw [AffineCarrier.lift_image n _ (generate_valid n formula inside),generate_read n formula inside]

abbrev Pieces := List (Formula × Cells)

def factors (n : Nat) : Nat → Formula → Pieces
  | _,[] => []
  | 0,formula => [(formula,generate n formula)]
  | fuel+1,clause::rest =>
      let split := AffineClauseProduct.grow rest.length [clause] rest
      (split.1,generate n split.1)::factors n fuel split.2

def piecesRead (pieces : Pieces) (assignment : Nat → Bool) : Bool :=
  pieces.all (fun piece => read piece.2 assignment)

def possible (pieces : Pieces) : Bool := pieces.all (fun piece => !piece.2.isEmpty)

theorem factors_read (n fuel : Nat) (formula : Formula) (inside : Within n formula) (assignment : Nat → Bool) :
    piecesRead (factors n fuel formula) assignment = formulaRead formula assignment := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [factors,piecesRead,generate_read n _ inside,formulaRead]
  | succ fuel ih =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          have bounds := AffineClauseProduct.grow_within n rest.length [clause] rest inside
          simp only [factors,piecesRead,List.all_cons,generate_read n _ bounds.1]
          change (_ && piecesRead (factors n fuel _) assignment) = _
          rw [ih _ bounds.2]
          exact AffineClauseProduct.grow_read clause rest assignment

theorem model_possible (n : Nat) (formula : Formula) (inside : Within n formula) :
    (!(generate n formula).isEmpty) = true ↔ AffineClauseProduct.Satisfiable formula := by
  rw [AffineCarrier.nonempty_iff n _ (generate_valid n formula inside)]
  simp only [generate_read n formula inside]
  constructor
  · rintro ⟨x,accepted⟩
    exact ⟨extendAssignment x,accepted⟩
  · rintro ⟨x,accepted⟩
    exact ⟨(fun i => x i.val),(AffineClauseProduct.formula_restrict n formula inside x).trans accepted⟩

theorem factors_possible (n fuel : Nat) (formula : Formula) (inside : Within n formula) :
    possible (factors n fuel formula) = true ↔ AffineClauseProduct.Satisfiable formula := by
  induction fuel generalizing formula with
  | zero =>
      cases formula with
      | nil => simp [factors,possible,AffineClauseProduct.Satisfiable,formulaRead]
      | cons clause rest => simpa only [factors,possible,List.all_cons,List.all_nil,Bool.and_true] using model_possible n _ inside
  | succ fuel ih =>
      cases formula with
      | nil => simp [factors,possible,AffineClauseProduct.Satisfiable,formulaRead]
      | cons clause rest =>
          have bounds := AffineClauseProduct.grow_within n rest.length [clause] rest inside
          change ((!(generate n (AffineClauseProduct.grow rest.length [clause] rest).1).isEmpty) &&
            possible (factors n fuel (AffineClauseProduct.grow rest.length [clause] rest).2)) = true ↔ _
          simp only [Bool.and_eq_true,model_possible n _ bounds.1,ih _ bounds.2]
          rw [← AffineClauseProduct.separated_sat _ _ (AffineClauseProduct.grow_apart rest.length [clause] rest (Nat.le_refl _))]
          apply exists_congr
          intro assignment
          rw [AffineClauseProduct.formula_members _ _ (AffineClauseProduct.grow_members rest.length [clause] rest) assignment]
          rfl

def Parameters (n : Nat) : Pieces → Type
  | [] => Assignment n
  | piece::rest => AffineCarrier.Parameters n piece.2 × Parameters n rest

def lift (n : Nat) : (pieces : Pieces) → Parameters n pieces → Assignment n
  | [],parameters => parameters
  | piece::rest,parameters =>
      let first := AffineCarrier.lift n piece.2 parameters.1
      let last := lift n rest parameters.2
      fun i => AffineClauseProduct.merge piece.1 (extendAssignment first) (extendAssignment last) i.val

theorem lift_fixes (n : Nat) (source : Formula) (model : Cells) (rest : Pieces)
    (left : AffineCarrier.Parameters n model) (right : Parameters n rest) (assignment : Assignment n)
    (first : AffineCarrier.lift n model left = assignment) (second : lift n rest right = assignment) :
    lift n ((source,model)::rest) (left,right) = assignment := by
  funext i
  simp [lift,first,second,AffineClauseProduct.merge,extendAssignment]

theorem factors_image (n fuel : Nat) (formula : Formula) (inside : Within n formula) (assignment : Assignment n) :
    (∃ parameter : Parameters n (factors n fuel formula), lift n (factors n fuel formula) parameter = assignment) ↔
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
            let model := generate n source
            have first := (generate_image n source inside (AffineCarrier.lift n model left)).mp ⟨left,rfl⟩
            exact (AffineClauseProduct.formula_restrict n source inside (AffineClauseProduct.merge source
              (extendAssignment (AffineCarrier.lift n model left)) (extendAssignment right))).trans
                ((AffineClauseProduct.merge_left source _ _).trans first)
          · intro accepted
            obtain ⟨parameter,same⟩ := (generate_image n (clause::rest) inside assignment).mpr accepted
            exact ⟨(parameter,assignment),lift_fixes n _ _ [] parameter assignment assignment same rfl⟩
  | succ fuel ih =>
      cases formula with
      | nil =>
          change (∃ parameter : Assignment n, parameter = assignment) ↔ true = true
          exact ⟨fun _ => rfl,fun _ => ⟨assignment,rfl⟩⟩
      | cons clause rest =>
          let split := AffineClauseProduct.grow rest.length [clause] rest
          have bounds := AffineClauseProduct.grow_within n rest.length [clause] rest inside
          have apart := AffineClauseProduct.grow_apart rest.length [clause] rest (Nat.le_refl _)
          constructor
          · rintro ⟨⟨left,right⟩,rfl⟩
            let a := AffineCarrier.lift n (generate n split.1) left
            let b := lift n (factors n fuel split.2) right
            have first : formulaRead split.1 (extendAssignment a) = true := (generate_image n split.1 bounds.1 a).mp ⟨left,rfl⟩
            have second : formulaRead split.2 (extendAssignment b) = true := (ih split.2 bounds.2 b).mp ⟨right,rfl⟩
            have joined : formulaRead (clause::rest) (AffineClauseProduct.merge split.1 (extendAssignment a) (extendAssignment b)) = true := by
              rw [← AffineClauseProduct.grow_read clause rest]
              rw [AffineClauseProduct.merge_left,AffineClauseProduct.merge_right split.1 split.2 apart,first,second]
              rfl
            exact (AffineClauseProduct.formula_restrict n (clause::rest) inside _).trans joined
          · intro accepted
            have both := (AffineClauseProduct.grow_read clause rest (extendAssignment assignment)).trans accepted
            have facts : formulaRead split.1 (extendAssignment assignment) = true ∧
                formulaRead split.2 (extendAssignment assignment) = true := by simpa using both
            obtain ⟨first,second⟩ := facts
            obtain ⟨left,firstEq⟩ := (generate_image n split.1 bounds.1 assignment).mpr first
            obtain ⟨right,secondEq⟩ := (ih split.2 bounds.2 assignment).mpr second
            exact ⟨(left,right),lift_fixes n split.1 _ _ left right assignment firstEq secondEq⟩

def emit (n : Nat) (formula : Formula) : Pieces :=
  let cleaned := cleanRun formula
  factors n cleaned.value.length cleaned.value

theorem emit_read (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Nat → Bool) :
    piecesRead (emit n formula) assignment = formulaRead formula assignment := by
  rw [emit,cleanRun_value,factors_read n _ _ (clean_within n formula inside),clean_read]

theorem emit_possible (n : Nat) (formula : Formula) (inside : Within n formula) :
    possible (emit n formula) = true ↔ AffineClauseProduct.Satisfiable formula := by
  rw [emit,cleanRun_value,factors_possible n _ _ (clean_within n formula inside)]
  apply exists_congr
  intro assignment
  rw [clean_read]

theorem emit_image (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Assignment n) :
    (∃ p : Parameters n (emit n formula), lift n (emit n formula) p = assignment) ↔
      formulaRead formula (extendAssignment assignment) = true := by
  rw [emit,cleanRun_value,factors_image n _ _ (clean_within n formula inside),clean_read]

end SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.Joint
