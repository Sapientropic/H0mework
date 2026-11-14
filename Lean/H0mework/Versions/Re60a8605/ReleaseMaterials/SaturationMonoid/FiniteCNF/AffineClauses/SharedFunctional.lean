import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.JointEmission
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.SharedSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.UnifiedFlow.Source
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ConditionalPivot

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.SharedFunctional
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open AffineClauses (Formula formulaRead Within)

/-- The actual strong seed retains its context whenever its enhanced query holds. -/
theorem emitted_joint {q : Nat} (query : CNFFormula q) (context : List Row) (target : Nat → Bool) :
    (CNFFormula.eval (AffineJointEmission.emit query context).query target &&
      (AffineJointEmission.emit query context).strong.holds target)=
        (CNFFormula.eval query target && holds context target) := by
  let enhanced := (AffineBinaryContext.generate query context).formula
  have generated := TightFeedback.generate_holds enhanced
    (context++Extract.extract enhanced++(CapacityMatching.RowCost.prepare enhanced).value) target
  have initial : (CNFFormula.eval enhanced target &&
      holds (context++Extract.extract enhanced++(CapacityMatching.RowCost.prepare enhanced).value) target)=
        (CNFFormula.eval enhanced target && holds context target) := by
    cases accepted : CNFFormula.eval enhanced target with
    | false => simp
    | true =>
        have extracted := Extract.extract_entails enhanced target accepted
        have prepared : holds (CapacityMatching.RowCost.prepare enhanced).value target=true := by
          rw [CapacityMatching.RowCost.prepare_value]
          exact CapacityMatching.SourceTight.prepare_entails enhanced target accepted
        simp only [holds,List.all_append] at extracted prepared ⊢
        rw [extracted,prepared]
        simp
  exact generated.trans (initial.trans (AffineBinaryContext.generate_value query context target))

/-- Node-record work for the actual substitution pass, including retained program copies.
Branch relation generation, candidate selection, and address-bit arithmetic are separate calls. -/
def execute : List FunctionalSubstitution.Instruction → Program → AffineProduct.Cost.Counted Program
  | [],program => ⟨program,2*program.code.size+1⟩
  | instruction::rest,program =>
      let next := FunctionalSubstitution.substitute program instruction.address instruction.body
      let tail := execute rest next
      ⟨tail.value,tail.visits+10*(program.code.size+instruction.body.code.size+next.code.size+tail.value.code.size)+12⟩

theorem execute_value (instructions : List FunctionalSubstitution.Instruction) (program : Program) :
    (execute instructions program).value=FunctionalSubstitution.execute instructions program := by
  induction instructions generalizing program with
  | nil => rfl
  | cons instruction rest ih => simp only [execute,FunctionalSubstitution.execute,ih]

theorem execute_size (instructions : List FunctionalSubstitution.Instruction) (program : Program) :
    (execute instructions program).value.code.size=program.code.size+(instructions.map (fun i => i.body.code.size)).sum := by
  rw [execute_value,FunctionalSubstitution.execute_size]

theorem execute_cells (instructions : List FunctionalSubstitution.Instruction) (program : Program) :
    (execute instructions program).visits ≤ (instructions.length+1)*
      (40*(program.code.size+(instructions.map (fun i => i.body.code.size)).sum)+13) := by
  induction instructions generalizing program with
  | nil => simp [execute]; omega
  | cons instruction rest ih =>
      have tail := ih (FunctionalSubstitution.substitute program instruction.address instruction.body)
      have output := execute_size rest (FunctionalSubstitution.substitute program instruction.address instruction.body)
      simp only [FunctionalSubstitution.substitute_size] at tail output
      simp only [execute,List.length_cons,List.map_cons,List.sum_cons]
      rw [output,FunctionalSubstitution.substitute_size]
      let total := program.code.size+(instruction.body.code.size+(rest.map (fun i => i.body.code.size)).sum)
      have tailBound : (execute rest (FunctionalSubstitution.substitute program instruction.address instruction.body)).visits ≤
          (rest.length+1)*(40*total+13) := by
        convert tail using 1
        dsimp only [total]
        ring
      have roundBound : 10*(program.code.size+instruction.body.code.size+
          (instruction.body.code.size+program.code.size)+
          (instruction.body.code.size+program.code.size+(rest.map (fun i => i.body.code.size)).sum))+12 ≤ 40*total+13 := by
        dsimp only [total]
        omega
      have combined := Nat.add_le_add tailBound roundBound
      change _ ≤ (rest.length+1+1)*(40*total+13)
      calc
        _ ≤ (rest.length+1)*(40*total+13)+(40*total+13) := by simpa only [Nat.add_assoc] using combined
        _ = _ := by ring

structure Frame (q : Nat) where
  private mk ::
  basis : List Row
  coordinates : Array Row
  instructions : List FunctionalSubstitution.Instruction
  program : Program
  executionCells : Nat
  deriving Repr

/-- Candidate generation and selection run once; both the stored program and guards use this list. -/
def compile {q : Nat} (query : CNFFormula q) (basis : List Row) : Frame q :=
  let coordinates := Table.coordinates q basis
  let candidates := ConditionalPivot.candidates query basis
  let instructions := FunctionalSubstitution.select [] candidates
  let executed := execute instructions (Acceptance.compile coordinates query)
  ⟨basis,coordinates,instructions,executed.value,executed.visits⟩

theorem compile_program {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (compile query basis).program=ConditionalPivot.compile query basis := by
  simp only [compile,execute_value,ConditionalPivot.compile,FunctionalSubstitution.prepare]

theorem compile_instructions {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (compile query basis).instructions=ConditionalPivot.selected query basis := rfl

theorem compile_coordinates {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (compile query basis).coordinates=Table.coordinates q basis := rfl

def Frame.read {q : Nat} (frame : Frame q) (target : Nat → Bool) : Bool :=
  let environment := extendAssignment (projectFree q frame.basis (fun i => target i.val))
  holds frame.basis target && FunctionalAffine.legal frame.instructions environment && truth (frame.program.eval environment)

theorem compile_read {q : Nat} (query : CNFFormula q) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin q basis) (target : Nat → Bool) :
    (compile query basis).read target=(CNFFormula.eval query target && holds basis target) := by
  simpa only [Frame.read,compile,execute_value,ConditionalPivot.readCompiled,ConditionalPivot.compile,
    FunctionalSubstitution.prepare,ConditionalPivot.selected] using
      ConditionalPivot.readCompiled_value query basis valid.2 valid.1 target

structure Model (q : Nat) where
  private mk ::
  table : Array Row
  image : AtomImage.State
  emitted : AffineJointEmission.Output q
  frame : Option (Frame q)
  deriving Repr

def assemble {q : Nat} (table : Array Row) (image : AtomImage.State) (emitted : AffineJointEmission.Output q) : Model q :=
  let frame := match emitted.strong with
    | .contradiction => none
    | .basis basis => some (compile emitted.query basis)
  ⟨table,image,emitted,frame⟩

def generate (formula : Formula) : Model (AffineClauseImage.width formula) :=
  let table := AffineClauseImage.table formula
  let image := AtomImage.generate table
  let emitted := AffineJointEmission.emit (AffineClauseImage.atomFormula formula) image.kernel
  assemble table image emitted

def read {q : Nat} (model : Model q) (target : Nat → Bool) : Bool :=
  match model.frame with | none => false | some frame => frame.read target

theorem assemble_read {q : Nat} (table : Array Row) (image : AtomImage.State)
    (emitted : AffineJointEmission.Output q) (bounded : AffineJointEmission.Bounded emitted) (target : Nat → Bool) :
    read (assemble table image emitted) target=(CNFFormula.eval emitted.query target && emitted.strong.holds target) := by
  cases seeded : emitted.strong with
  | contradiction => simp [assemble,read,seeded,Result.holds]
  | basis basis =>
      have valid : Triangular basis ∧ RowsWithin q basis := by
        simpa only [seeded,Result.triangular,Result.within] using And.intro bounded.1 bounded.2.1
      simpa only [assemble,read,seeded,Result.holds] using compile_read emitted.query basis valid target

theorem generate_read (n : Nat) (formula : Formula) (inside : Within n formula) (target : Nat → Bool) :
    read (generate formula) target=AffineSharedSource.allows (AffineSharedSource.generate formula) target := by
  rw [generate,assemble_read _ _ _ (AffineJointEmission.emit_source_bounded n formula inside),
    emitted_joint,AffineSharedSource.generate_allows,AffineClauseImage.constraints_read]

theorem source_read (n : Nat) (formula : Formula) (inside : Within n formula) (input : Nat → Bool) :
    read (generate formula) (Gates.coordinate (generate formula).table input)=formulaRead formula input := by
  rw [generate_read n formula inside]
  exact AffineSharedSource.generate_read formula input

def decide {q : Nat} (model : Model q) : Bool :=
  match model.frame with
  | none => false
  | some frame => FunctionalSubstitution.decideProgram (Cone.pruneCone frame.program)

theorem assemble_decide {q : Nat} (table : Array Row) (image : AtomImage.State) (emitted : AffineJointEmission.Output q)
    (bounded : AffineJointEmission.Bounded emitted) :
    decide (assemble table image emitted)=true ↔ ∃ point : Assignment q,
      (CNFFormula.eval emitted.query (extendAssignment point) && emitted.strong.holds (extendAssignment point))=true := by
  cases seeded : emitted.strong with
  | contradiction => simp [assemble,decide,seeded,Result.holds]
  | basis basis =>
      have valid : Triangular basis ∧ RowsWithin q basis := by
        simpa only [seeded,Result.triangular,Result.within] using And.intro bounded.1 bounded.2.1
      simpa only [assemble,decide,seeded,Result.holds,Bool.and_eq_true,compile_program] using
        ConditionalPivot.compile_correct emitted.query basis valid.2 valid.1

theorem generate_decide (n : Nat) (formula : Formula) (inside : Within n formula) :
    decide (generate formula)=true ↔ AffineClauseProduct.Satisfiable formula := by
  rw [generate,assemble_decide _ _ _ (AffineJointEmission.emit_source_bounded n formula inside)]
  simp only [emitted_joint]
  let constraints := AffineClauseImage.constraints formula (AtomImage.generate (AffineClauseImage.table formula))
  have within : Within (AffineClauseImage.width formula) constraints := AffineClauseImage.constraints_within n formula inside
  apply Iff.trans ?_ (AffineJointResidual.constraints_possible formula)
  constructor
  · rintro ⟨point,accepted⟩
    refine ⟨extendAssignment point,?_⟩
    simpa only [AffineClauseImage.constraints_read] using accepted
  · rintro ⟨point,accepted⟩
    refine ⟨fun i => point i.val,?_⟩
    have finite := (AffineClauseProduct.formula_restrict _ constraints within point).trans accepted
    simpa only [constraints,AffineClauseImage.constraints_read] using finite

def build {n : Nat} (original : CNFFormula n) : Model (AffineClauseImage.width (AffineClauseImage.liftCNF original)) :=
  generate (AffineClauseImage.liftCNF original)

def decideFormula {n : Nat} (original : CNFFormula n) : Bool := decide (build original)

theorem decideFormula_correct {n : Nat} (original : CNFFormula n) : decideFormula original=true ↔ CNFSatisfiable original := by
  rw [decideFormula,build,generate_decide n _ (AffineClauseImage.liftCNF_within original)]
  apply exists_congr
  intro point
  rw [AffineClauseImage.liftCNF_read]

theorem build_read {n : Nat} (original : CNFFormula n) (point : Nat → Bool) :
    read (build original) (Gates.coordinate (build original).table point)=CNFFormula.eval original point := by
  rw [build,source_read n _ (AffineClauseImage.liftCNF_within original),AffineClauseImage.liftCNF_read]

def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with | none => false | some input => decideFormula input.2

theorem decideBits_original (bits : List Bool) : decideBits bits=Encoding.decideBits bits := by
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits,Encoding.decideBits,parsed]
  | some input =>
      simp only [decideBits,Encoding.decideBits,parsed]
      apply Bool.eq_iff_iff.mpr
      rw [decideFormula_correct,Dense.decideFormula_correct]

theorem decideBits_verify (bits : List Bool) : decideBits bits=true ↔
    ∃ input : Encoding.Input, Encoding.parse bits=some input ∧
      ∃ point : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) point := by
  rw [decideBits_original,Encoding.decideBits_iff_rootVerify]

theorem original_source_zero {n : Nat} (original : CNFFormula n) : decideFormula original=true ↔
    ∃ point : Assignment n, (UnifiedSource.generated original point).residualTraceShare=0 := by
  rw [decideFormula_correct,satisfiable_iff_finite_assignment]
  exact exists_congr (fun point => (UnifiedSource.contact_zero_iff original point).symm)

def sourceAction {n : Nat} (original : CNFFormula n) (source : Source n) : Source n :=
  let model := build original
  fun point => if read model (Gates.coordinate model.table (extendAssignment point)) then source point else 0

theorem original_projector {n : Nat} (original : CNFFormula n) (source : Source n) :
    zeroProjector original source=sourceAction original source := by
  funext point
  simp only [sourceAction,zeroProjector_apply,build_read]

theorem compile_size {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (compile query basis).program.code.size ≤ 3+q+2*q*q+3*query.length+3*SATJoint.literalCount query+
      (3*query.length+q*q)*(12+8*q) := by
  rw [compile_program]
  exact ConditionalPivot.compile_size query basis

theorem selected_eliminated {q : Nat} (query : CNFFormula q) (basis : List Row)
    (instruction : FunctionalSubstitution.Instruction) (selected : instruction ∈ (compile query basis).instructions) :
    instruction.address ∉ FunctionalSubstitution.inputs (compile query basis).program.code := by
  rw [compile_program]
  exact ConditionalPivot.selected_eliminated query basis instruction selected

theorem compile_execution_cells {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (compile query basis).executionCells ≤ ((compile query basis).instructions.length+1)*
      (40*(compile query basis).program.code.size+13) := by
  have bound := execute_cells (ConditionalPivot.selected query basis) (Acceptance.compile (Table.coordinates q basis) query)
  rw [← execute_size] at bound
  exact bound

def programBudget (q clauses literals : Nat) : Nat :=
  3+q+2*q*q+3*clauses+3*literals+(3*clauses+q*q)*(12+8*q)

theorem compile_instruction_count {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (compile query basis).instructions.length ≤ 3*query.length+q*q :=
  (FunctionalSubstitution.select_sublist [] (ConditionalPivot.candidates query basis)).length_le.trans
    (ConditionalPivot.candidates_length query basis)

theorem emitted_program_size {q : Nat} (query : CNFFormula q) (context basis : List Row) :
    (compile (AffineJointEmission.emit query context).query basis).program.code.size ≤
      programBudget q (query.length+4*q*q) (Extract.literalCount query+8*q*q) := by
  have raw := compile_size (AffineJointEmission.emit query context).query basis
  have clauses := AffineJointEmission.emit_length query context
  have literals := AffineJointEmission.emit_literals query context
  have same : SATJoint.literalCount (AffineJointEmission.emit query context).query=
      Extract.literalCount (AffineJointEmission.emit query context).query := by
    simp [SATJoint.literalCount,Extract.literalCount]
  rw [same] at raw
  apply raw.trans
  unfold programBudget
  gcongr

theorem emitted_execution_cells {q : Nat} (query : CNFFormula q) (context basis : List Row) :
    (compile (AffineJointEmission.emit query context).query basis).executionCells ≤
      (3*(query.length+4*q*q)+q*q+1)*
        (40*programBudget q (query.length+4*q*q) (Extract.literalCount query+8*q*q)+13) := by
  have execution := compile_execution_cells (AffineJointEmission.emit query context).query basis
  have instructions := (compile_instruction_count (AffineJointEmission.emit query context).query basis).trans
    (show 3*(AffineJointEmission.emit query context).query.length+q*q ≤ 3*(query.length+4*q*q)+q*q from by
      gcongr
      exact AffineJointEmission.emit_length query context)
  have code := emitted_program_size query context basis
  exact execution.trans (by gcongr)

theorem close_size {q : Nat} (frame : Frame q) :
    (FunctionalSubstitution.close (Cone.pruneCone frame.program)).code.size ≤
      Affine.Boolean.nodeBudget (FunctionalSubstitution.inputs (Cone.pruneCone frame.program).code).length
        (Cone.pruneCone frame.program).code.size := Affine.Boolean.fold_size _ _

end SaturationMonoid.ComplexityProjection.SATSource.SharedFunctional
