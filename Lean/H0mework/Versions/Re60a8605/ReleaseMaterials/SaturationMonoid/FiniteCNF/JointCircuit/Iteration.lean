import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Feedback
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Arena.Total.Cost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalMessage

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointIteration
open InterferenceProgram
open JointCircuit (Update update read)

def done (output : Update) : Bool := output.rejected || output.binding.isEmpty

def combine (first second : Update) : Update :=
  ⟨second.state,second.rejected,first.binding++second.binding,second.joint⟩

theorem combine_read (first second : Update) (point : Nat → Bool) :
    (combine first second).read point=
      (FunctionalAffine.legal first.binding point && second.read point) := by
  simp only [combine,Update.read,FunctionalAffine.legal,List.all_append]
  cases second.rejected <;> simp [Bool.and_assoc]

def iterate : Nat → ArenaSource.State → Update
  | 0,state => ⟨state,false,[],none⟩
  | fuel+1,state =>
      let first := update state
      if done first then first else combine first (iterate fuel first.state)

theorem continue_spec (output : Update) (continuing : done output≠true) :
    output.rejected=false ∧ output.binding≠[] := by
  cases rejected : output.rejected <;> cases bindings : output.binding <;> simp_all [done]

theorem iterate_read (fuel : Nat) (state : ArenaSource.State) (point : Nat → Bool) :
    (iterate fuel state).read point=read state point := by
  induction fuel generalizing state with
  | zero => simp [iterate,Update.read,FunctionalAffine.legal]
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact JointCircuit.update_read state point
      · rename_i continuing
        have ongoing := continue_spec (update state) continuing
        rw [combine_read,ih]
        have original := JointCircuit.update_read state point
        simpa only [Update.read,ongoing.1,Bool.not_false,Bool.true_and] using original

theorem eligible_present (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena)
    (eligible : ArenaSource.eligible state item=true) : item.address ∈ ArenaTotal.support state := by
  simp only [ArenaSource.eligible,Bool.and_eq_true,decide_eq_true_eq] at eligible
  have node : state.arena.code[item.relation.left.val]=Node.input item.address := by
    simpa [Array.getD,item.relation.left.isLt] using eligible.1
  have member := Array.getElem_mem_toList item.relation.left.isLt
  rw [node] at member
  exact List.mem_toFinset.mpr ((FunctionalSubstitution.input_member _ _).mpr member)

theorem eligible_decreases (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena)
    (eligible : ArenaSource.eligible state item=true) :
    ArenaTotal.remaining (ArenaSource.next state item.address item.relation.right)<ArenaTotal.remaining state := by
  have present := eligible_present state item eligible
  simp only [ArenaSource.eligible,Bool.and_eq_true,decide_eq_true_eq] at eligible
  have free := ArenaAction.apply_free state.arena item.address item.relation.right
    ((ArenaAction.apply_performed _ _ _).mpr eligible.2)
  have absent : item.address ∉ ArenaTotal.support (ArenaSource.next state item.address item.relation.right) := by
    simpa only [ArenaTotal.support,ArenaSource.next,List.mem_toFinset] using
      FunctionalSubstitution.inputs_free _ item.address free
  apply Finset.card_lt_card
  refine ⟨ArenaTotal.next_support_subset state item.address item.relation.right,?_⟩
  intro backwards
  exact absent (backwards present)

theorem update_decreases (state : ArenaSource.State) (nonempty : (update state).binding≠[]) :
    ArenaTotal.remaining (update state).state<ArenaTotal.remaining state := by
  by_cases checked : JointCircuit.noAdd state.arena.code=true
  · cases generated : (JointCircuit.analyzed state).value with
    | contradiction => simp [update,checked,generated] at nonempty
    | basis basis =>
        cases found : JointCircuit.pick state basis with
        | none => simp [update,checked,generated,found] at nonempty
        | some item =>
            have changed : update state=⟨ArenaSource.next state item.address item.relation.right,false,
                [ArenaSource.selected state item],some (.basis basis)⟩ := by simp [update,checked,generated,found]
            rw [changed]
            exact eligible_decreases state item (JointCircuit.pick_spec state basis item found).1
  · simp [update,checked] at nonempty

theorem idle_state (state : ArenaSource.State) (empty : (update state).binding=[]) :
    (update state).state=state := by
  by_cases checked : JointCircuit.noAdd state.arena.code=true
  · cases generated : (JointCircuit.analyzed state).value with
    | contradiction => simp [update,checked,generated]
    | basis basis =>
        cases found : JointCircuit.pick state basis with
        | none => simp [update,checked,generated,found]
        | some item => simp [update,checked,generated,found] at empty
  · simp [update,checked]

def Settled (output : Update) : Prop := output.rejected=true ∨ (update output.state).binding=[]

theorem stopped_settled (state : ArenaSource.State) (stopped : done (update state)=true) :
    Settled (update state) := by
  simp only [done,Bool.or_eq_true,List.isEmpty_iff] at stopped
  rcases stopped with rejected | empty
  · exact Or.inl rejected
  · exact Or.inr ((congrArg (fun s => (update s).binding) (idle_state state empty)).trans empty)

theorem iterate_settled (fuel : Nat) (state : ArenaSource.State) (enough : ArenaTotal.remaining state≤fuel) :
    Settled (iterate fuel state) := by
  induction fuel generalizing state with
  | zero =>
      apply Or.inr
      change (update state).binding=[]
      by_contra nonempty
      have decrease := update_decreases state nonempty
      omega
  | succ fuel ih =>
      simp only [iterate]
      split
      · rename_i stopped
        exact stopped_settled state stopped
      · rename_i continuing
        have changed := update_decreases state (continue_spec (update state) continuing).2
        exact ih (update state).state (by omega)

def run (state : ArenaSource.State) : Update := iterate state.arena.code.size state

theorem run_read (state : ArenaSource.State) (point : Nat → Bool) : (run state).read point=read state point :=
  iterate_read _ state point

theorem run_settled (state : ArenaSource.State) : Settled (run state) :=
  iterate_settled _ state (ArenaTotal.remaining_le_nodes state)

theorem iterate_size (fuel : Nat) (state : ArenaSource.State) :
    (iterate fuel state).state.arena.code.size=state.arena.code.size := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact JointCircuit.update_next_size state
      · exact (ih (update state).state).trans (JointCircuit.update_next_size state)

theorem iterate_count (fuel : Nat) (state : ArenaSource.State) :
    (iterate fuel state).state.relations.length=state.relations.length := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases stopped : done (update state)=true
      · rw [iterate,if_pos stopped]
        exact JointCircuit.update_relations state
      · rw [iterate,if_neg stopped]
        exact (ih (update state).state).trans (JointCircuit.update_relations state)

theorem iterate_correct (fuel : Nat) (state : ArenaSource.State) :
    (∃ point, (!(iterate fuel state).rejected && read (iterate fuel state).state point)=true) ↔
      ∃ point, read state point=true := by
  induction fuel generalizing state with
  | zero => simp only [iterate,Bool.not_false,Bool.true_and]
  | succ fuel ih =>
      by_cases stopped : done (update state)=true
      · rw [iterate,if_pos stopped]
        exact JointCircuit.update_correct state
      · rw [iterate,if_neg stopped]
        change (∃ point, (!(iterate fuel (update state).state).rejected &&
          read (iterate fuel (update state).state).state point)=true) ↔ _
        rw [ih]
        have result := JointCircuit.update_correct state
        simpa only [(continue_spec (update state) stopped).1,Bool.not_false,Bool.true_and] using result

theorem update_valid (state : ArenaSource.State) (valid : ArenaSource.Valid state) :
    ArenaSource.Valid (update state).state := by
  by_cases checked : JointCircuit.noAdd state.arena.code=true
  · cases generated : (JointCircuit.analyzed state).value with
    | contradiction => simpa only [update,checked,if_true,generated] using valid
    | basis basis =>
        cases found : JointCircuit.pick state basis with
        | none => simpa only [update,checked,if_true,generated,found] using valid
        | some item =>
            simpa only [update,checked,if_true,generated,found] using
              ArenaSource.next_valid state valid item.address item.relation.right
  · simpa only [update,if_neg checked] using valid

theorem iterate_valid (fuel : Nat) (state : ArenaSource.State) (valid : ArenaSource.Valid state) :
    ArenaSource.Valid (iterate fuel state).state := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      by_cases stopped : done (update state)=true
      · rw [iterate,if_pos stopped]
        exact update_valid state valid
      · rw [iterate,if_neg stopped]
        exact ih _ (update_valid state valid)

open SaturationMonoid.ComplexityProjection.SATSource.Affine

theorem prepared_valid {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    ArenaSource.Valid (ArenaTotal.Cost.compile formula basis).value.state := by
  rw [ArenaTotal.Cost.compile_value]
  exact ArenaSource.drive_valid _ _ (ArenaSource.build_valid _ _ (ArenaSource.front_entails formula basis valid))

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Update :=
  let source := ArenaTotal.Cost.compile formula basis
  let generated := run source.value.state
  ⟨generated.state,generated.rejected,source.value.instructions++generated.binding,generated.joint⟩

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile formula basis).read point=CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) := by
  let source := (ArenaTotal.Cost.compile formula basis).value
  change (combine ⟨source.state,false,source.instructions,none⟩ (run source.state)).read point=_
  rw [combine_read,run_read,JointCircuit.valid_read source.state (prepared_valid formula basis valid)]
  exact ArenaTotal.Cost.compile_read formula basis valid point

set_option maxHeartbeats 1200000 in
theorem compile_settled {n : Nat} (formula : CNFFormula n) (basis : List Row) : Settled (compile formula basis) :=
  run_settled _

def decide {n : Nat} (formula : CNFFormula n) (basis : List Row) : Bool :=
  let output := compile formula basis
  !output.rejected && FunctionalSubstitution.decideProgram output.state.program.program

set_option maxHeartbeats 1200000 in
theorem decide_correct {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) : decide formula basis=true ↔
      ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
  let source := (ArenaTotal.Cost.compile formula basis).value
  have before := prepared_valid formula basis valid
  have after := iterate_valid source.state.arena.code.size source.state before
  have initial : (∃ point, read source.state point=true) ↔
      ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
    simp only [JointCircuit.valid_read source.state before]
    rw [← FunctionalSubstitution.decideProgram_correct]
    exact ArenaTotal.Cost.compile_correct formula basis valid
  have generated := (iterate_correct source.state.arena.code.size source.state).trans initial
  change (!((run source.state).rejected) &&
    FunctionalSubstitution.decideProgram (run source.state).state.program.program)=true ↔ _
  rw [Bool.and_eq_true,FunctionalSubstitution.decideProgram_correct]
  constructor
  · rintro ⟨accepted,point,possible⟩
    apply generated.mp
    refine ⟨point,?_⟩
    rw [JointCircuit.valid_read _ after]
    change (!(run source.state).rejected && truth ((run source.state).state.program.program.eval point))=true
    simp only [accepted,possible,Bool.true_and]
  · intro possible
    obtain ⟨point,accepted⟩ := generated.mpr possible
    rw [JointCircuit.valid_read _ after,Bool.and_eq_true] at accepted
    exact ⟨accepted.1,point,accepted.2⟩

def projector {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  let output := compile formula []
  fun point => if output.read (extendAssignment point) then source point else 0

theorem projector_original {n : Nat} (formula : CNFFormula n) (source : Source n) :
    projector formula source=zeroProjector formula source := by
  funext point
  simp only [projector,compile_read formula [] ⟨triangular_nil,by simp [RowsWithin]⟩,zeroProjector_apply]
  rw [FunctionalMessage.empty_formula]

end SaturationMonoid.ComplexityProjection.SATSource.JointIteration
