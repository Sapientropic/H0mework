import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Effects.Consumer

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.EffectRelations
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine

/-- No acceptance row is added: these are relations of the actual gate source at every input. -/
def prepared (state : ArenaSource.State) : ProductRows.Prepared :=
  let frame := (ProductCost.expand (PortEmbedding.initial state)).value
  let rows := (ProductCost.equations state []).value
  ⟨frame,rows,false⟩

theorem prepared_frame (state : ArenaSource.State) : (prepared state).frame=ProductClosure.frame state := by
  simp only [prepared,ProductCost.expand_value,ProductClosure.frame]

theorem prepared_rows (state : ArenaSource.State) : (prepared state).rows=ProductRows.equations state [] := by
  simp only [prepared,ProductCost.equations_value]

def kernel (state : ArenaSource.State) : Result :=
  (ProductClosureCost.fromPrepared (PortEmbedding.initial state) (prepared state)).value

theorem kernel_valid (state : ArenaSource.State) : (kernel state).triangular ∧ (kernel state).within (prepared state).frame.state.arena.code.size :=
  ProductClosureCost.fromPrepared_valid _ _

theorem kernel_holds (state : ArenaSource.State) (point : Nat → Bool) :
    (kernel state).holds (JointCircuit.lift (prepared state).frame.state point)=true := by
  rw [kernel,ProductClosureCost.fromPrepared_value,ProductClosure.fromPrepared,prepared_frame,ProductClosure.iterateAt_source]
  have valid := ProductRows.analyze_valid (ProductClosure.frame state) (prepared state).rows
  rw [ProductClosure.iterate_holds state _ _ valid point,ProductRows.analyze_holds,prepared_rows]
  exact ProductRows.equations_holds state [] (by simp [RowsWithin]) point (by rfl)

def target (state : ArenaSource.State) : Fin (prepared state).frame.state.arena.code.size :=
  PortEmbedding.ref (prepared state).frame.state (prepared state).frame.ports state.program.weight.val

def constant (state : ArenaSource.State) : Option Bool :=
  let source := prepared state
  let generated := (ProductClosureCost.fromPrepared (PortEmbedding.initial state) source).value
  match generated with
  | .contradiction => none
  | .basis basis =>
      let index := PortEmbedding.ref source.frame.state source.frame.ports state.program.weight.val
      let row := (Table.coordinates source.frame.state.arena.code.size basis).getD index.val Gates.zeroRow
      if row.vars.isEmpty then some row.rhs else none

theorem constant_equation (state : ArenaSource.State) : constant state=
    match kernel state with
    | .contradiction => none
    | .basis basis =>
        let row := (Table.coordinates (prepared state).frame.state.arena.code.size basis).getD (target state).val Gates.zeroRow
        if row.vars.isEmpty then some row.rhs else none := rfl

theorem constant_gate (state : ArenaSource.State) (value : Bool) (found : constant state=some value) (point : Nat → Bool) :
    JointCircuit.lift (prepared state).frame.state point (target state).val=value := by
  have valid := kernel_valid state
  have accepted := kernel_holds state point
  cases generated : kernel state with
  | contradiction => simp only [constant_equation,generated,reduceCtorEq] at found
  | basis basis =>
      have basisValid : Triangular basis ∧ RowsWithin (prepared state).frame.state.arena.code.size basis := by
        simpa only [generated,Result.triangular,Result.within] using valid
      have basisHolds : holds basis (JointCircuit.lift (prepared state).frame.state point)=true := by
        simpa only [generated,Result.holds] using accepted
      have row := PortRelations.coordinate_recover _ basis basisValid _ basisHolds (target state)
      simp only [constant_equation,generated] at found
      split at found
      · rename_i empty
        have terms : ((Table.coordinates (prepared state).frame.state.arena.code.size basis).getD (target state).val Gates.zeroRow).vars=[] := by
          simpa using empty
        have bit := Option.some.inj found
        rw [← row]
        simp only [Gates.value,Row.eval,terms,Parity.eval,Bool.xor_false,bit]
      · cases found

theorem constant_source (state : ArenaSource.State) (value : Bool) (found : constant state=some value) (point : Nat → Bool) :
    truth (state.program.program.eval point)=value := by
  have result := constant_gate state value found point
  change (prepared state).frame.read point state.program.weight.val=value at result
  rw [prepared_frame,ProductClosure.frame,ProductBatch.generate_old] at result
  · rw [EffectDAG.program_truth]
    rw [BranchPorts.initial_read state point state.program.weight.val state.program.weight.isLt] at result
    exact result
  · rw [PortEmbedding.initial_size]
    exact state.program.weight.isLt

def normalize (program : Program) : Program :=
  let source := ArenaSource.build program []
  match constant source with
  | none => program
  | some value => Affine.Boolean.constant value

theorem normalize_read (program : Program) (point : Nat → Bool) :
    truth ((normalize program).eval point)=truth (program.eval point) := by
  cases result : constant (ArenaSource.build program []) with
  | none => simp only [normalize,result]
  | some value =>
      have source := constant_source (ArenaSource.build program []) value result point
      rw [ArenaSource.build_program] at source
      simp only [normalize,result,Affine.Boolean.eval_constant,truth_bit,source]

theorem normalize_correct (program : Program) :
    (∃ point, truth ((normalize program).eval point)=true) ↔ ∃ point, truth (program.eval point)=true := by
  simp only [normalize_read]

def readOutput (source : PortUpdate.Output) : Bool :=
  if source.rejected then false else EffectReading.read (normalize (EffectConsumer.step source.frame.state.program.program))

theorem readOutput_original (source : PortUpdate.Output) : readOutput source=true ↔ PortUpdate.stateDecision source.frame.state source.rejected=true := by
  cases rejected : source.rejected <;>
    simp only [readOutput,rejected,Bool.false_eq_true,if_false,if_true,PortUpdate.stateDecision,Bool.not_false,Bool.not_true,
      Bool.true_and,Bool.false_and,EffectReading.read_value,ForgettingScalar.programRead_correct,
      FunctionalSubstitution.decideProgram_correct,normalize_correct,EffectConsumer.step_correct]

def decide {n : Nat} (formula : CNFFormula n) (basis : List Row) : Bool := readOutput (ProductClosureCost.compile formula basis).value

theorem decide_correct {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    decide formula basis=true ↔ ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true :=
  (readOutput_original _).trans (ProductClosureCost.compile_decision formula basis valid)

theorem decide_original {n : Nat} (formula : CNFFormula n) : decide formula []=true ↔ CNFSatisfiable formula := by
  simpa only [FunctionalMessage.empty_formula,CNFSatisfiable] using decide_correct formula [] ⟨triangular_nil,by simp [RowsWithin]⟩

end SaturationMonoid.ComplexityProjection.SATSource.EffectRelations
