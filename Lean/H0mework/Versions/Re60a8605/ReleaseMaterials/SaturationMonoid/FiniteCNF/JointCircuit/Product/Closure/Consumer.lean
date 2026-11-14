import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Product.Closure.Source

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ProductClosed
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)

def frame (state : ArenaSource.State) : Frame := PortEmbedding.initial (ProductClosure.frame state).state

theorem frame_read (state : ArenaSource.State) (point : Nat → Bool) : JointCircuit.read (frame state).state point=JointCircuit.read state point :=
  ProductBatch.generate_read (PortEmbedding.initial state) point

theorem generated_holds (state : ArenaSource.State) (basis : List Row) (found : ProductClosure.generate state=.basis basis) :
    ProductRows.Holds (frame state) basis := by
  intro point accepted
  rw [frame_read] at accepted
  have source := ProductClosure.generate_holds state point accepted
  have valid := ProductClosure.generate_valid state
  have within : RowsWithin (ProductClosure.frame state).state.arena.code.size basis := by
    simpa only [found,Result.within] using valid.2
  rw [found] at source
  exact ProductRows.basis_initial (ProductClosure.frame state).state basis within point source

theorem generated_no (state : ArenaSource.State) (found : ProductClosure.generate state=.contradiction) (point : Nat → Bool) :
    JointCircuit.read state point=false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have source := ProductClosure.generate_holds state point accepted
  rw [found] at source
  cases source

theorem prepared_no (state : ArenaSource.State) (found : (ProductRows.prepare state).rejected=true) (point : Nat → Bool) :
    JointCircuit.read state point=false := by
  have original := ProductRows.prepare_read state point
  simpa only [found,Bool.not_true,Bool.false_and] using original.symm

def run (state : ArenaSource.State) : PortUpdate.Output :=
  let source := (ProductCost.prepare state).value
  let inventory := PortEmbedding.initial source.frame.state
  if source.rejected then ⟨inventory,true,[],some .contradiction⟩ else
    match ProductClosure.fromPrepared (PortEmbedding.initial state) source with
    | .contradiction => ⟨inventory,true,[],some .contradiction⟩
    | .basis basis => ProductRows.iterate inventory.state.arena.code.size inventory basis

theorem run_equation (state : ArenaSource.State) : run state=
  if (ProductRows.prepare state).rejected then ⟨frame state,true,[],some .contradiction⟩ else
    match ProductClosure.generate state with
    | .contradiction => ⟨frame state,true,[],some .contradiction⟩
    | .basis basis => ProductRows.iterate (frame state).state.arena.code.size (frame state) basis := by
  simp only [run,ProductCost.prepare_value,ProductClosure.fromPrepared_source,ProductRows.prepare_frame]
  rfl

theorem run_read (state : ArenaSource.State) (point : Nat → Bool) : (run state).value.read point=JointCircuit.read state point := by
  by_cases first : (ProductRows.prepare state).rejected=true
  · simp [run_equation,first,PortUpdate.Output.value,JointCircuit.Update.read,prepared_no state first point]
  · rw [run_equation,if_neg first]
    cases result : ProductClosure.generate state with
    | contradiction => simp [PortUpdate.Output.value,JointCircuit.Update.read,generated_no state result point]
    | basis basis =>
        rw [ProductRows.iterate_read _ _ _ (generated_holds state basis result),frame_read]

theorem run_transport (state : ArenaSource.State) (point : Nat → Bool) :
    (!(run state).rejected && JointCircuit.read (run state).frame.state point)=
      JointCircuit.read state (FunctionalSubstitution.fill (run state).binding point) := by
  by_cases first : (ProductRows.prepare state).rejected=true
  · simp [run_equation,first,FunctionalSubstitution.fill,prepared_no state first point]
  · rw [run_equation,if_neg first]
    cases result : ProductClosure.generate state with
    | contradiction => simp [FunctionalSubstitution.fill,generated_no state result point]
    | basis basis =>
        rw [ProductRows.iterate_transport _ _ _ (generated_holds state basis result),frame_read]

theorem run_correct (state : ArenaSource.State) :
    (∃ point, (!(run state).rejected && JointCircuit.read (run state).frame.state point)=true) ↔
      ∃ point, JointCircuit.read state point=true := by
  constructor
  · rintro ⟨point,accepted⟩
    exact ⟨FunctionalSubstitution.fill (run state).binding point,(run_transport state point).symm.trans accepted⟩
  · rintro ⟨point,accepted⟩
    have result := (run_read state point).trans accepted
    simp only [PortUpdate.Output.value,JointCircuit.Update.read,Bool.and_eq_true] at result
    exact ⟨point,by simp only [Bool.and_eq_true]; exact ⟨result.1.1,result.2⟩⟩

theorem run_size (state : ArenaSource.State) : (run state).frame.state.arena.code.size ≤
    state.arena.code.size+state.arena.code.size*state.arena.code.size+1 := by
  have size := ProductBatch.generate_size (PortEmbedding.initial state)
  simp only [PortEmbedding.initial_size] at size
  change (frame state).state.arena.code.size ≤ _ at size
  simp only [run_equation]
  split
  · exact size
  · split
    · exact size
    · rw [ProductRows.iterate_size]
      exact size

theorem run_valid (state : ArenaSource.State) (valid : ArenaSource.Valid state) : ArenaSource.Valid (run state).frame.state := by
  have original : ArenaSource.Valid (frame state).state := ProductBatch.generate_valid (PortEmbedding.initial state) valid
  simp only [run_equation]
  split
  · exact original
  · split
    · exact original
    · exact ProductRows.iterate_valid _ _ _ original

def continueFrom (previous : PortUpdate.Output) : PortUpdate.Output :=
  if previous.rejected then previous else PortUpdate.combine previous (run previous.frame.state)

theorem continueFrom_read (previous : PortUpdate.Output) (point : Nat → Bool) :
    (continueFrom previous).value.read point=previous.value.read point := by
  by_cases rejected : previous.rejected=true
  · simp only [continueFrom,if_pos rejected]
  · rw [continueFrom,if_neg rejected,PortUpdate.combine_value,JointIteration.combine_read,run_read]
    simp only [JointCircuit.Update.read,PortUpdate.Output.value,Bool.eq_false_iff.mpr rejected,Bool.not_false,Bool.true_and]

theorem continueFrom_correct (previous : PortUpdate.Output) :
    (∃ point, (!(continueFrom previous).rejected && JointCircuit.read (continueFrom previous).frame.state point)=true) ↔
      ∃ point, (!previous.rejected && JointCircuit.read previous.frame.state point)=true := by
  cases rejected : previous.rejected with
  | true => simp only [continueFrom,rejected,if_true]
  | false =>
      simp only [continueFrom,rejected,Bool.false_eq_true,if_false,PortUpdate.combine,Bool.not_false,Bool.true_and]
      exact run_correct previous.frame.state

theorem continueFrom_valid (previous : PortUpdate.Output) (valid : ArenaSource.Valid previous.frame.state) :
    ArenaSource.Valid (continueFrom previous).frame.state := by
  simp only [continueFrom]
  split
  · exact valid
  · exact run_valid previous.frame.state valid

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : PortUpdate.Output :=
  continueFrom (BranchCost.compile formula basis).value

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile formula basis).value.read point=CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) :=
  (continueFrom_read _ point).trans (BranchCost.compile_read formula basis valid point)

theorem compile_valid {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    ArenaSource.Valid (compile formula basis).frame.state := by
  apply continueFrom_valid
  rw [BranchCost.compile_value]
  exact BranchPorts.compile_valid formula basis valid

def decide {n : Nat} (formula : CNFFormula n) (basis : List Row) : Bool :=
  let output := compile formula basis
  PortUpdate.stateDecision output.frame.state output.rejected

theorem decide_correct {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    decide formula basis=true ↔ ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
  let previous := (BranchCost.compile formula basis).value
  have oldValid : ArenaSource.Valid previous.frame.state := by
    change ArenaSource.Valid (BranchCost.compile formula basis).value.frame.state
    rw [BranchCost.compile_value]
    exact BranchPorts.compile_valid formula basis valid
  have oldDecision : PortUpdate.stateDecision previous.frame.state previous.rejected=true ↔
      ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
    change PortUpdate.stateDecision (BranchCost.compile formula basis).value.frame.state (BranchCost.compile formula basis).value.rejected=true ↔ _
    rw [BranchCost.compile_value]
    exact BranchPorts.decide_correct formula basis valid
  have original := (PortUpdate.stateDecision_iff previous.frame.state oldValid previous.rejected).symm.trans oldDecision
  exact (PortUpdate.stateDecision_iff _ (compile_valid formula basis valid) _).trans ((continueFrom_correct previous).trans original)

def projector {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  let output := compile formula []
  fun point => if output.value.read (extendAssignment point) then source point else 0

theorem projector_original {n : Nat} (formula : CNFFormula n) (source : Source n) : projector formula source=zeroProjector formula source := by
  funext point
  simp only [projector,compile_read formula [] ⟨triangular_nil,by simp [RowsWithin]⟩,zeroProjector_apply]
  rw [FunctionalMessage.empty_formula]

theorem continueFrom_size (previous : PortUpdate.Output) :
    (continueFrom previous).frame.state.arena.code.size ≤
      previous.frame.state.arena.code.size+previous.frame.state.arena.code.size*previous.frame.state.arena.code.size+1 := by
  simp only [continueFrom]
  split
  · omega
  · exact run_size previous.frame.state

theorem compile_size {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).frame.state.arena.code.size ≤
      let original := BranchPorts.inventoryBound (PortCost.capacity (PortCost.capacity
        (ArenaSource.sourceBound n formula.length (Extract.literalCount formula)))) (3*formula.length+n*n)
      original+original*original+1 := by
  have bound := BranchPorts.compile_size formula basis valid
  rw [← BranchCost.compile_value] at bound
  exact (continueFrom_size (BranchCost.compile formula basis).value).trans (by dsimp only; gcongr)

end SaturationMonoid.ComplexityProjection.SATSource.ProductClosed
