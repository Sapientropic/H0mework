import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.InputRelations

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointRelationUpdate
open InterferenceProgram
open FunctionalSubstitution (Free)

private theorem head_member {α : Type} (items : List α) (item : α) (found : items.head?=some item) : item ∈ items := by
  cases items with
  | nil => cases found
  | cons first rest =>
      simp only [List.head?_cons,Option.some.injEq] at found
      subst item
      exact List.mem_cons_self

private theorem mapRefs_free (i : Nat) (rename : Nat → Nat) (node : Node)
    (free : FunctionalSubstitution.Node.Free i node) : FunctionalSubstitution.Node.Free i (node.mapRefs rename) := by
  cases node <;> exact free

theorem intern_free (i : Nat) (state : Reduce.State) (node : Node)
    (old : Free i state.code) (new : FunctionalSubstitution.Node.Free i node) : Free i (Reduce.intern state node).1.code := by
  unfold Reduce.intern
  split
  · exact old
  · intro value member
    simp only [Reduce.append,Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with member | rfl
    · exact old value member
    · exact new

theorem fold_free (i : Nat) (frame : Reduce.Frame) (code : List Node)
    (old : Free i frame.state.code) (new : ∀ node ∈ code, FunctionalSubstitution.Node.Free i node) :
    Free i (Reduce.fold frame code).state.code := by
  induction code generalizing frame with
  | nil => exact old
  | cons node rest ih =>
      apply ih _ (intern_free i frame.state _ old (mapRefs_free i _ node (new node (by simp))))
        (fun node member => new node (by simp [member]))

theorem compact_free (i : Nat) (code : Array Node) (free : Free i code) : Free i (Reduce.compact code).state.code := by
  apply fold_free i Reduce.first code.toList ?_ free
  simp [Free,FunctionalSubstitution.Node.Free,Reduce.first,Reduce.initial]

theorem load_free (i : Nat) (code : Array Node) (free : Free i code) : Free i (ArenaAction.load code).arena.code :=
  compact_free i code free

theorem substitute_free (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction) (free : Free call.address call.body.code) :
    Free call.address (ArenaSource.substitute state call).arena.code :=
  load_free call.address _ (FunctionalSubstitution.substitute_free_self state.program.program call.address call.body free)

theorem substitute_inputs (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction)
    (supported : FunctionalSubstitution.inputs call.body.code ⊆ FunctionalSubstitution.inputs state.arena.code) :
    FunctionalSubstitution.inputs (ArenaSource.substitute state call).arena.code ⊆ FunctionalSubstitution.inputs state.arena.code := by
  intro i member
  by_contra absent
  have old := (FunctionalSubstitution.free_iff state.arena.code i).mpr absent
  have body := (FunctionalSubstitution.free_iff call.body.code i).mpr (fun present => absent (supported present))
  have kept := load_free i _ (FunctionalSubstitution.substitute_free state.program.program call.address i call.body old body)
  exact FunctionalSubstitution.inputs_free _ i kept member

theorem substitute_decreases (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction)
    (member : call ∈ JointInputRelations.generate state) :
    ArenaTotal.remaining (ArenaSource.substitute state call)<ArenaTotal.remaining state := by
  have generated := JointInputRelations.generate_present_size state call member
  have removed := substitute_free state call (JointInputRelations.generate_free state call member)
  have contained := substitute_inputs state call (JointInputRelations.generate_inputs state call member)
  have subset : ArenaTotal.support (ArenaSource.substitute state call) ⊆ ArenaTotal.support state := by
    intro i present
    exact List.mem_toFinset.mpr (contained (List.mem_toFinset.mp present))
  have absent : call.address ∉ ArenaTotal.support (ArenaSource.substitute state call) := by
    simpa only [ArenaTotal.support,List.mem_toFinset] using FunctionalSubstitution.inputs_free _ call.address removed
  apply Finset.card_lt_card
  refine ⟨subset,?_⟩
  intro backwards
  exact absent (backwards (List.mem_toFinset.mpr generated.1))

theorem substitute_read (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction) (point : Nat → Bool) :
    JointCircuit.read (ArenaSource.substitute state call) point=JointCircuit.read state (call.bind point) := by
  simp only [JointCircuit.read,ArenaSource.substitute_program,ArenaSource.substitute_relations]

def usePrevious (result : JointCircuit.Update) : Bool := result.rejected || !result.binding.isEmpty

def update (state : ArenaSource.State) : JointCircuit.Update :=
  let previous := JointCircuit.update state
  if usePrevious previous then previous else
    match (JointInputRelations.generate state).head? with
    | none => previous
    | some call => ⟨ArenaSource.substitute state call,false,[call],previous.joint⟩

theorem update_read (state : ArenaSource.State) (point : Nat → Bool) :
    (update state).read point=JointCircuit.read state point := by
  simp only [update]
  split
  · exact JointCircuit.update_read state point
  · cases found : (JointInputRelations.generate state).head? with
    | none => simpa only [found] using JointCircuit.update_read state point
    | some call =>
        have member := head_member _ _ found
        simp only [JointCircuit.Update.read,Bool.not_false,Bool.true_and,substitute_read]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true]
        constructor
        · rintro ⟨guard,accepted⟩
          have fixed := FunctionalAffine.legal_fixed [call] point guard
          change call.bind point=point at fixed
          rwa [fixed] at accepted
        · intro accepted
          have fixed := JointInputRelations.generate_fixes state point accepted call member
          refine ⟨FunctionalAffine.legal_of_fixed [call] point ?_,?_⟩
          · intro instruction present
            simp only [List.mem_singleton] at present
            exact present ▸ fixed
          · rwa [fixed]

theorem update_transport (state : ArenaSource.State) (point : Nat → Bool) :
    (!(update state).rejected && JointCircuit.read (update state).state point)=
      JointCircuit.read state (FunctionalSubstitution.fill (update state).binding point) := by
  simp only [update]
  split
  · exact JointCircuit.update_transport state point
  · cases found : (JointInputRelations.generate state).head? with
    | none => simpa only [found] using JointCircuit.update_transport state point
    | some call =>
        simp only [Bool.not_false,Bool.true_and,substitute_read,FunctionalSubstitution.fill,List.foldr_cons,List.foldr_nil]

theorem update_correct (state : ArenaSource.State) :
    (∃ point, (!(update state).rejected && JointCircuit.read (update state).state point)=true) ↔
      ∃ point, JointCircuit.read state point=true := by
  constructor
  · rintro ⟨point,accepted⟩
    exact ⟨FunctionalSubstitution.fill (update state).binding point,(update_transport state point).symm.trans accepted⟩
  · rintro ⟨point,accepted⟩
    have after := (update_read state point).trans accepted
    simp only [JointCircuit.Update.read,Bool.and_eq_true] at after
    exact ⟨point,by simp only [Bool.and_eq_true]; exact ⟨after.1.1,after.2⟩⟩

theorem update_decreases (state : ArenaSource.State) (nonempty : (update state).binding≠[]) :
    ArenaTotal.remaining (update state).state<ArenaTotal.remaining state := by
  by_cases previous : usePrevious (JointCircuit.update state)=true
  · simp only [update,if_pos previous] at nonempty ⊢
    exact JointIteration.update_decreases state nonempty
  · simp only [update,if_neg previous] at nonempty ⊢
    cases found : (JointInputRelations.generate state).head? with
    | none => simpa only [found] using JointIteration.update_decreases state (by simpa only [found] using nonempty)
    | some call => simpa only [found] using substitute_decreases state call (head_member _ _ found)

theorem update_size (state : ArenaSource.State) :
    (update state).state.arena.code.size ≤ state.arena.code.size+2*(FunctionalSubstitution.inputs state.arena.code).length+2 := by
  simp only [update]
  split
  · rw [JointCircuit.update_next_size]; omega
  · cases found : (JointInputRelations.generate state).head? with
    | none => simp only [JointCircuit.update_next_size]; omega
    | some call =>
        have body := (JointInputRelations.generate_present_size state call (head_member _ _ found)).2
        have size := ArenaSource.substitute_size state call
        simp only
        omega

theorem update_count (state : ArenaSource.State) : (update state).state.relations.length=state.relations.length := by
  by_cases previous : usePrevious (JointCircuit.update state)=true
  · rw [update,if_pos previous]
    exact JointCircuit.update_relations state
  · rw [update,if_neg previous]
    cases found : (JointInputRelations.generate state).head? with
    | none => simpa only [found] using JointCircuit.update_relations state
    | some call => simpa only [found] using ArenaSource.substitute_count state call


theorem idle_state (state : ArenaSource.State) (empty : (update state).binding=[]) : (update state).state=state := by
  by_cases previous : usePrevious (JointCircuit.update state)=true
  · simp only [update,if_pos previous] at empty ⊢
    exact JointIteration.idle_state state empty
  · simp only [update,if_neg previous] at empty ⊢
    cases found : (JointInputRelations.generate state).head? with
    | none => simpa only [found] using JointIteration.idle_state state (by simpa only [found] using empty)
    | some call => simp only [found,List.cons_ne_self] at empty

theorem update_remaining (state : ArenaSource.State) : ArenaTotal.remaining (update state).state ≤ ArenaTotal.remaining state := by
  by_cases empty : (update state).binding=[]
  · rw [idle_state state empty]
  · exact Nat.le_of_lt (update_decreases state empty)

theorem remaining_length (state : ArenaSource.State) :
    ArenaTotal.remaining state=(FunctionalSubstitution.inputs state.arena.code).length :=
  List.toFinset_card_of_nodup (List.nodup_dedup _)

def Settled (output : JointCircuit.Update) : Prop := output.rejected=true ∨ (update output.state).binding=[]

def iterate : Nat → ArenaSource.State → JointCircuit.Update
  | 0,state => ⟨state,false,[],none⟩
  | fuel+1,state =>
      let first := update state
      if JointIteration.done first then first else JointIteration.combine first (iterate fuel first.state)

theorem iterate_read (fuel : Nat) (state : ArenaSource.State) (point : Nat → Bool) :
    (iterate fuel state).read point=JointCircuit.read state point := by
  induction fuel generalizing state with
  | zero => simp [iterate,JointCircuit.Update.read,FunctionalAffine.legal]
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_read state point
      · rename_i continuing
        have keep := JointIteration.continue_spec (update state) continuing
        rw [JointIteration.combine_read,ih]
        simpa only [JointCircuit.Update.read,keep.1,Bool.not_false,Bool.true_and] using update_read state point

theorem iterate_correct (fuel : Nat) (state : ArenaSource.State) :
    (∃ point, (!(iterate fuel state).rejected && JointCircuit.read (iterate fuel state).state point)=true) ↔
      ∃ point, JointCircuit.read state point=true := by
  induction fuel generalizing state with
  | zero => simp only [iterate,Bool.not_false,Bool.true_and]
  | succ fuel ih =>
      by_cases stopped : JointIteration.done (update state)=true
      · rw [iterate,if_pos stopped]
        exact update_correct state
      · rw [iterate,if_neg stopped]
        change (∃ point, (!(iterate fuel (update state).state).rejected &&
          JointCircuit.read (iterate fuel (update state).state).state point)=true) ↔ _
        rw [ih]
        simpa only [(JointIteration.continue_spec (update state) stopped).1,Bool.not_false,Bool.true_and] using update_correct state

theorem iterate_settled (fuel : Nat) (state : ArenaSource.State) (enough : ArenaTotal.remaining state ≤ fuel) :
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
        simp only [JointIteration.done,Bool.or_eq_true,List.isEmpty_iff] at stopped
        rcases stopped with rejected | empty
        · exact Or.inl rejected
        · exact Or.inr ((congrArg (fun state => (update state).binding) (idle_state state empty)).trans empty)
      · rename_i continuing
        have reduced := update_decreases state (JointIteration.continue_spec (update state) continuing).2
        exact ih _ (by omega)

theorem iterate_size (fuel : Nat) (state : ArenaSource.State) (bound : Nat) (bounded : ArenaTotal.remaining state ≤ bound) :
    (iterate fuel state).state.arena.code.size ≤ state.arena.code.size+fuel*(2*bound+2) := by
  induction fuel generalizing state with
  | zero => simp [iterate]
  | succ fuel ih =>
      have first := update_size state
      have support := update_remaining state
      have later := ih (update state).state (support.trans bounded)
      rw [remaining_length] at bounded
      simp only [iterate]
      split
      · nlinarith
      · simp only [JointIteration.combine]
        nlinarith

theorem iterate_count (fuel : Nat) (state : ArenaSource.State) :
    (iterate fuel state).state.relations.length=state.relations.length := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases stopped : JointIteration.done (update state)=true
      · rw [iterate,if_pos stopped]
        exact update_count state
      · rw [iterate,if_neg stopped]
        exact (ih (update state).state).trans (update_count state)

def run (state : ArenaSource.State) : JointCircuit.Update := iterate state.arena.code.size state

theorem run_read (state : ArenaSource.State) (point : Nat → Bool) : (run state).read point=JointCircuit.read state point :=
  iterate_read _ state point

theorem run_settled (state : ArenaSource.State) : Settled (run state) :=
  iterate_settled _ state (ArenaTotal.remaining_le_nodes state)

theorem run_size (state : ArenaSource.State) :
    (run state).state.arena.code.size ≤ 2*state.arena.code.size*state.arena.code.size+3*state.arena.code.size := by
  have bound := iterate_size state.arena.code.size state state.arena.code.size (ArenaTotal.remaining_le_nodes state)
  change (run state).state.arena.code.size ≤ _ at bound
  nlinarith



theorem update_valid (state : ArenaSource.State) (valid : ArenaSource.Valid state) : ArenaSource.Valid (update state).state := by
  by_cases previous : usePrevious (JointCircuit.update state)=true
  · rw [update,if_pos previous]
    exact JointIteration.update_valid state valid
  · rw [update,if_neg previous]
    cases found : (JointInputRelations.generate state).head? with
    | none => simpa only [found] using JointIteration.update_valid state valid
    | some call => simpa only [found] using ArenaSource.substitute_valid state valid call

theorem iterate_valid (fuel : Nat) (state : ArenaSource.State) (valid : ArenaSource.Valid state) : ArenaSource.Valid (iterate fuel state).state := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      by_cases stopped : JointIteration.done (update state)=true
      · rw [iterate,if_pos stopped]
        exact update_valid state valid
      · rw [iterate,if_neg stopped]
        exact ih _ (update_valid state valid)

open SaturationMonoid.ComplexityProjection.SATSource.Affine

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : JointCircuit.Update :=
  let source := ArenaTotal.Cost.compile formula basis
  let generated := run source.value.state
  ⟨generated.state,generated.rejected,source.value.instructions++generated.binding,generated.joint⟩

set_option maxHeartbeats 1200000 in
theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile formula basis).read point=CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) := by
  let source := (ArenaTotal.Cost.compile formula basis).value
  change (JointIteration.combine ⟨source.state,false,source.instructions,none⟩ (run source.state)).read point=_
  rw [JointIteration.combine_read,run_read,JointCircuit.valid_read source.state (JointIteration.prepared_valid formula basis valid)]
  exact ArenaTotal.Cost.compile_read formula basis valid point

set_option maxHeartbeats 1200000 in
theorem compile_size {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).state.arena.code.size ≤
      let bound := ArenaSource.sourceBound n formula.length (Extract.literalCount formula)
      2*bound*bound+3*bound := by
  have size := ArenaTotal.Cost.compile_size formula basis valid
  have result := run_size (ArenaTotal.Cost.compile formula basis).value.state
  change (compile formula basis).state.arena.code.size ≤ _ at result
  exact result.trans (by dsimp only; gcongr)

set_option maxHeartbeats 1200000 in
theorem compile_settled {n : Nat} (formula : CNFFormula n) (basis : List Row) : Settled (compile formula basis) := run_settled _

def decide {n : Nat} (formula : CNFFormula n) (basis : List Row) : Bool :=
  let result := compile formula basis
  !result.rejected && FunctionalSubstitution.decideProgram result.state.program.program

set_option maxHeartbeats 1200000 in
theorem decide_correct {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) : decide formula basis=true ↔
      ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
  let source := (ArenaTotal.Cost.compile formula basis).value
  have before := JointIteration.prepared_valid formula basis valid
  have after := iterate_valid source.state.arena.code.size source.state before
  have initial : (∃ point, JointCircuit.read source.state point=true) ↔
      ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
    simp only [JointCircuit.valid_read source.state before]
    rw [← FunctionalSubstitution.decideProgram_correct]
    exact ArenaTotal.Cost.compile_correct formula basis valid
  have generated := (iterate_correct source.state.arena.code.size source.state).trans initial
  change (!(run source.state).rejected && FunctionalSubstitution.decideProgram (run source.state).state.program.program)=true ↔ _
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

set_option maxHeartbeats 1200000 in
theorem projector_original {n : Nat} (formula : CNFFormula n) (source : Source n) :
    projector formula source=zeroProjector formula source := by
  funext point
  simp only [projector,compile_read formula [] ⟨triangular_nil,by simp [RowsWithin]⟩,zeroProjector_apply]
  rw [FunctionalMessage.empty_formula]


end SaturationMonoid.ComplexityProjection.SATSource.JointRelationUpdate
