import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.ForcedBranches.Cost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalFeedback.Cost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.BoundaryTree.Common

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalMessage
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open FunctionalSubstitution (Instruction)

def original {n : Nat} (formula : CNFFormula n) : Program :=
  InterferenceDecision.fromAmplitude (Acceptance.original formula)

theorem original_eval {n : Nat} (formula : CNFFormula n) (point : Nat → Bool) :
    (original formula).eval point=bit (CNFFormula.eval formula point) := by
  rw [original,InterferenceDecision.eval_fromAmplitude,Acceptance.eval_original]

theorem empty_coordinate (n : Nat) (point : Nat → Bool) (i : Fin n) :
    Gates.coordinate (Table.coordinates n []) point i.val=point i.val := by
  have index : (List.range n).idxOf i.val=i.val := by
    simpa using List.get_idxOf (List.nodup_range (n := n)) (⟨i.val,by simpa only [List.length_range] using i.isLt⟩ : Fin (List.range n).length)
  rw [Table.coordinates_value n [] (by simp [RowsWithin])]
  simp [fill,freeSeed,freeIndices,pivots,index,i.isLt]

theorem empty_formula {n : Nat} (formula : CNFFormula n) (point : Nat → Bool) :
    CNFFormula.eval formula (Gates.coordinate (Table.coordinates n []) point)=CNFFormula.eval formula point := by
  have same : (fun i : Fin n => Gates.coordinate (Table.coordinates n []) point i.val)=
      (fun i : Fin n => point i.val) := funext (empty_coordinate n point)
  rw [← formula_eval_restrict formula (Gates.coordinate (Table.coordinates n []) point),same,formula_eval_restrict]

theorem candidates_entails {n : Nat} (formula : CNFFormula n) (point : Nat → Bool)
    (accepted : truth ((original formula).eval point)=true) (item : Instruction)
    (member : item ∈ (ForcedBranches.generate formula []).value) : item.bind point=point := by
  apply ForcedBranches.generate_entails formula [] (by simp [Triangular,RowsNodup,RowsWithin]) point ?_ item member
  simpa only [Acceptance.eval_compile,truth_bit,empty_formula,original_eval] using accepted

def protect (keep : List Nat) (source : List Instruction) : List Instruction :=
  source.filter (fun item => decide (item.address ∉ keep))

theorem protect_member (keep : List Nat) (source : List Instruction) (item : Instruction) :
    item ∈ protect keep source ↔ item ∈ source ∧ item.address ∉ keep := by simp [protect]

theorem protect_sublist (keep : List Nat) (source : List Instruction) : (protect keep source).Sublist source :=
  List.filter_sublist

theorem fill_keeps (keep : List Nat) (instructions : List Instruction)
    (preserved : ∀ item ∈ instructions, item.address ∉ keep) (point : Nat → Bool) (i : Nat) (member : i ∈ keep) :
    FunctionalSubstitution.fill instructions point i=point i := by
  induction instructions with
  | nil => rfl
  | cons item rest ih =>
      have different : i≠item.address := fun same => preserved item (by simp) (same ▸ member)
      have tail := ih (fun other hit => preserved other (by simp [hit]))
      simp only [FunctionalSubstitution.fill,List.foldr_cons,FunctionalSubstitution.Instruction.bind,
        FunctionalSubstitution.bind,Function.update_of_ne different]
      exact tail

theorem execute_boundary (keep : List Nat) (instructions : List Instruction) (program : Program)
    (preserved : ∀ item ∈ instructions, item.address ∉ keep)
    (entailed : ∀ point, truth (program.eval point)=true → ∀ item ∈ instructions, item.bind point=point)
    (boundary : Nat → Bool) :
    (∃ point, truth ((FunctionalSubstitution.execute instructions program).eval point)=true ∧
      ∀ i ∈ keep, point i=boundary i) ↔
    ∃ point, truth (program.eval point)=true ∧ ∀ i ∈ keep, point i=boundary i := by
  constructor
  · rintro ⟨point,accepted,agrees⟩
    refine ⟨FunctionalSubstitution.fill instructions point,?_,?_⟩
    · simpa only [FunctionalSubstitution.eval_execute] using accepted
    · intro i member
      exact (fill_keeps keep instructions preserved point i member).trans (agrees i member)
  · rintro ⟨point,accepted,agrees⟩
    refine ⟨point,?_,agrees⟩
    rw [FunctionalSubstitution.eval_execute,FunctionalSubstitution.fill_fixes instructions point (entailed point accepted)]
    exact accepted

def residual (keep : List Nat) (program : Program) : List Nat :=
  (FunctionalSubstitution.inputs program.code).filter (fun i => decide (i ∉ keep))

theorem residual_member (keep : List Nat) (program : Program) (i : Nat) :
    i ∈ residual keep program ↔ i ∈ FunctionalSubstitution.inputs program.code ∧ i ∉ keep := by simp [residual]

structure Model where
  keep : List Nat
  instructions : List Instruction
  program : Program
  remaining : List Nat
  deriving Repr

def generate {n : Nat} (formula : CNFFormula n) (keep : List Nat) : Model :=
  let source := protect keep ((ForcedBranches.generate formula []).value)
  let instructions := FunctionalFeedback.generate source
  let program := FunctionalSubstitution.execute instructions (original formula)
  ⟨keep,instructions,program,residual keep program⟩

theorem generated_protected {n : Nat} (formula : CNFFormula n) (keep : List Nat)
    (item : Instruction) (member : item ∈ (generate formula keep).instructions) : item.address ∉ keep := by
  exact ((protect_member keep _ item).mp (FunctionalFeedback.generate_member _ item member)).2

theorem generated_entails {n : Nat} (formula : CNFFormula n) (keep : List Nat) (point : Nat → Bool)
    (accepted : truth ((original formula).eval point)=true) (item : Instruction)
    (member : item ∈ (generate formula keep).instructions) : item.bind point=point :=
  candidates_entails formula point accepted item
    (((protect_member keep _ item).mp (FunctionalFeedback.generate_member _ item member)).1)

theorem generated_small {n : Nat} (formula : CNFFormula n) (keep : List Nat) :
    BooleanValues.Code (generate formula keep).program.code := by
  apply FunctionalSubstitution.execute_small
  · exact BooleanValues.fromAmplitude _ (BooleanValues.original formula)
  · intro item member
    exact ForcedBranches.Cost.generate_small formula [] item
      (((protect_member keep _ item).mp (FunctionalFeedback.generate_member _ item member)).1)

theorem generated_fill_keeps {n : Nat} (formula : CNFFormula n) (keep : List Nat) (point : Nat → Bool)
    (i : Nat) (member : i ∈ keep) :
    FunctionalSubstitution.fill (generate formula keep).instructions point i=point i :=
  fill_keeps keep _ (generated_protected formula keep) point i member

theorem generated_realizes {n : Nat} (formula : CNFFormula n) (keep : List Nat) (boundary : Nat → Bool) :
    (∃ point, truth ((generate formula keep).program.eval point)=true ∧ ∀ i ∈ keep, point i=boundary i) ↔
      CouncilCommon.Realizes (AffineClauseImage.liftCNF formula) keep boundary := by
  change (∃ point, truth ((FunctionalSubstitution.execute (generate formula keep).instructions (original formula)).eval point)=true ∧ _) ↔ _
  rw [execute_boundary keep _ _ (generated_protected formula keep) (generated_entails formula keep)]
  simp only [original_eval,truth_bit,CouncilCommon.Realizes,AffineClauseImage.liftCNF_read]

def Model.pointRead (model : Model) (point : Nat → Bool) : Bool :=
  FunctionalAffine.legal model.instructions point && truth (model.program.eval point)

theorem generated_pointRead {n : Nat} (formula : CNFFormula n) (keep : List Nat) (point : Nat → Bool) :
    (generate formula keep).pointRead point=CNFFormula.eval formula point := by
  have read := FunctionalFeedback.prepare_read (protect keep ((ForcedBranches.generate formula []).value))
    (original formula) (fun point accepted item member =>
      candidates_entails formula point accepted item ((protect_member keep _ item).mp member).1) point
  simpa only [generate,Model.pointRead,FunctionalFeedback.prepare,original_eval,truth_bit] using read

def sourceAction {n : Nat} (formula : CNFFormula n) (keep : List Nat) (source : Source n) : Source n :=
  let model := generate formula keep
  fun point => if model.pointRead (extendAssignment point) then source point else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (keep : List Nat) (source : Source n) :
    zeroProjector formula source=sourceAction formula keep source := by
  funext point
  simp only [sourceAction,generated_pointRead,zeroProjector_apply]

theorem selected_eliminated {n : Nat} (formula : CNFFormula n) (keep : List Nat) (item : Instruction)
    (member : item ∈ (generate formula keep).instructions) :
    item.address ∉ FunctionalSubstitution.inputs (generate formula keep).program.code :=
  FunctionalFeedback.prepare_eliminates _ _ item member

theorem anyOver_agrees (indices : List Nat) (value : (Nat → Bool) → Bool) (point : Nat → Bool)
    (accepted : Boolean.anyOver indices value point=true) :
    ∃ result, value result=true ∧ ∀ i, i ∉ indices → result i=point i := by
  induction indices generalizing point with
  | nil => exact ⟨point,accepted,fun _ _ => rfl⟩
  | cons i rest ih =>
      simp only [Boolean.anyOver,Bool.or_eq_true] at accepted
      rcases accepted with accepted | accepted
      all_goals
        obtain ⟨result,realizes,agrees⟩ := ih _ accepted
        refine ⟨result,realizes,?_⟩
        intro j absent
        have outside : j ∉ rest := fun member => absent (by simp [member])
        have different : j≠i := fun same => absent (by simp [same])
        simpa [different] using agrees j outside

theorem residual_exists (keep : List Nat) (program : Program) (boundary : Nat → Bool) :
    Boolean.anyOver (residual keep program) (fun point => truth (program.eval point)) boundary=true ↔
      ∃ point, truth (program.eval point)=true ∧ ∀ i ∈ keep, point i=boundary i := by
  constructor
  · intro accepted
    obtain ⟨point,accepted,agrees⟩ := anyOver_agrees _ _ _ accepted
    refine ⟨point,accepted,?_⟩
    intro i member
    exact agrees i (fun present => ((residual_member keep program i).mp present).2 member)
  · rintro ⟨point,accepted,agrees⟩
    apply FunctionalSubstitution.anyOver_assign _ _ point boundary
    rw [FunctionalSubstitution.eval_environment_congr program _ point ?_]
    · exact accepted
    · intro i used
      by_cases internal : i ∈ residual keep program
      · exact FunctionalSubstitution.assign_member _ _ _ i internal
      · have preserved : i ∈ keep := by
          by_contra absent
          exact internal ((residual_member keep program i).mpr ⟨used,absent⟩)
        exact FunctionalSubstitution.assign_same _ _ _ i (agrees i preserved).symm

def fold : List Nat → Program → Program
  | [],program => program
  | i::rest,program => Boolean.existential (fold rest program) i

theorem fold_eval (indices : List Nat) (program : Program) (point : Nat → Bool) :
    truth ((fold indices program).eval point)=Boolean.anyOver indices (fun env => truth (program.eval env)) point := by
  induction indices generalizing point with
  | nil => rfl
  | cons i rest ih => simp only [fold,Boolean.eval_existential,truth_bit,Boolean.anyOver,ih]

def Model.read (model : Model) (boundary : Nat → Bool) : Bool :=
  truth ((fold model.remaining model.program).eval boundary)

def Model.closed (model : Model) : Bool := model.remaining.isEmpty

theorem generated_read {n : Nat} (formula : CNFFormula n) (keep : List Nat) (boundary : Nat → Bool) :
    (generate formula keep).read boundary=true ↔ CouncilCommon.Realizes (AffineClauseImage.liftCNF formula) keep boundary := by
  rw [Model.read,fold_eval]
  change Boolean.anyOver (residual keep (generate formula keep).program) _ boundary=true ↔ _
  rw [residual_exists,generated_realizes]

theorem closed_read (model : Model) (closed : model.closed=true) (boundary : Nat → Bool) :
    model.read boundary=truth (model.program.eval boundary) := by
  have empty : model.remaining=[] := by simpa only [Model.closed,List.isEmpty_iff] using closed
  simp only [Model.read,empty,fold]

theorem closed_message {n : Nat} (formula : CNFFormula n) (keep : List Nat)
    (closed : (generate formula keep).closed=true) (boundary : Nat → Bool) :
    truth ((generate formula keep).program.eval boundary)=true ↔
      CouncilCommon.Realizes (AffineClauseImage.liftCNF formula) keep boundary := by
  rw [← closed_read _ closed boundary]
  exact generated_read formula keep boundary

def boundaryTry (model : Model) (boundary : Nat → Bool) : Option Bool :=
  if model.closed then some (truth (model.program.eval boundary)) else none

theorem boundaryTry_read (model : Model) (boundary : Nat → Bool) (answer : Bool)
    (found : boundaryTry model boundary=some answer) : model.read boundary=answer := by
  unfold boundaryTry at found
  split at found
  · rename_i closed
    rw [closed_read _ closed]
    exact Option.some.inj found
  · simp at found

def bindings (keep : List Nat) (boundary : Nat → Bool) : AffineClauses.Formula :=
  keep.map (fun i => [⟨[i],boundary i⟩])

theorem bindings_read (keep : List Nat) (boundary point : Nat → Bool) :
    AffineClauses.formulaRead (bindings keep boundary) point=true ↔
      ∀ i ∈ keep, point i=boundary i := by
  simp [bindings,AffineClauses.formulaRead,AffineClauses.clauseRead,Row.holds,Row.eval,Parity.eval]

theorem generated_boundary {n : Nat} (formula : CNFFormula n) (keep : List Nat) (boundary : Nat → Bool) :
    (generate formula keep).read boundary=true ↔
      ∃ point, AffineClauses.formulaRead
        (AffineClauseImage.liftCNF formula++bindings keep boundary) point=true := by
  rw [generated_read]
  simp only [CouncilCommon.Realizes,AffineClauses.formulaRead,List.all_append,Bool.and_eq_true]
  constructor
  · rintro ⟨point,accepted,agrees⟩
    exact ⟨point,accepted,(bindings_read keep boundary point).mpr agrees⟩
  · rintro ⟨point,accepted,agrees⟩
    exact ⟨point,accepted,(bindings_read keep boundary point).mp agrees⟩

theorem generated_join {n k : Nat} (left : CNFFormula n) (right : CNFFormula k)
    (keep : List Nat) (boundary : Nat → Bool) :
    CouncilCommon.Realizes (AffineClauseImage.liftCNF left++AffineClauseImage.liftCNF right) keep boundary ↔
      ∃ middle,
        (generate left (CouncilCommon.boundary (AffineClauseImage.liftCNF left)
          (AffineClauseImage.liftCNF right) keep)).read middle=true ∧
        (generate right (CouncilCommon.boundary (AffineClauseImage.liftCNF right)
          (AffineClauseImage.liftCNF left) keep)).read middle=true ∧
        ∀ i ∈ keep, middle i=boundary i := by
  simp only [generated_read]
  exact CouncilCommon.source_message_join _ _ keep boundary

end SaturationMonoid.ComplexityProjection.SATSource.FunctionalMessage
