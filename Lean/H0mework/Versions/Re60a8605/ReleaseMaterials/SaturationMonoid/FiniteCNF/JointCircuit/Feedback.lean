import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Core

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointCircuit
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine

def linked (basis : List Row) (left right : Nat) : Bool :=
  let normalized := CapacityMatching.RowCost.normalize ⟨[left,right],false⟩
  let reduced := EliminateCost.reduce basis normalized.value
  decide (reduced.row=⟨[],false⟩)

theorem linked_holds (basis : List Row) (left right : Nat) (point : Nat → Bool)
    (accepted : holds basis point=true) (found : linked basis left right=true) : point left=point right := by
  have reduced : (EliminateCost.reduce basis (CapacityMatching.RowCost.normalize ⟨[left,right],false⟩).value).row=⟨[],false⟩ :=
    of_decide_eq_true found
  change (EliminateCost.reduce basis (Row.normalize ⟨[left,right],false⟩)).row=⟨[],false⟩ at reduced
  rw [EliminateCost.reduce_row] at reduced
  have same := reduceWith_holds basis (Row.normalize ⟨[left,right],false⟩) point accepted
  rw [reduced,Row.normalize_holds] at same
  simp only [Row.holds,Row.eval,Parity.eval] at same
  cases a : point left <;> cases b : point right <;> simp_all

def proposal (state : ArenaSource.State) (input root : Fin state.arena.code.size) (address : Nat) : ArenaSource.Labeled state.arena :=
  ⟨address,⟨input,root⟩⟩

def rootFor (state : ArenaSource.State) (basis : List Row) (input : Fin state.arena.code.size) (address : Nat) :
    Option (Fin state.arena.code.size) :=
  (List.finRange state.arena.code.size).find? (fun root =>
    linked basis input.val root.val && ArenaSource.eligible state (proposal state input root address))

def scan (state : ArenaSource.State) (basis : List Row) :
    List (Fin state.arena.code.size) → Option (ArenaSource.Labeled state.arena)
  | [] => none
  | input::rest =>
      match node state input with
      | .input address =>
          match rootFor state basis input address with
          | none => scan state basis rest
          | some root => some (proposal state input root address)
      | _ => scan state basis rest

def pick (state : ArenaSource.State) (basis : List Row) : Option (ArenaSource.Labeled state.arena) :=
  scan state basis (List.finRange state.arena.code.size)

theorem scan_spec (state : ArenaSource.State) (basis : List Row) (indices : List (Fin state.arena.code.size))
    (item : ArenaSource.Labeled state.arena) (found : scan state basis indices=some item) :
    ArenaSource.eligible state item=true ∧ linked basis item.relation.left.val item.relation.right.val=true := by
  induction indices with
  | nil => cases found
  | cons input rest ih =>
      cases shape : node state input <;> simp only [scan,shape] at found
      all_goals try exact ih found
      rename_i address
      cases chosen : rootFor state basis input address with
      | none => simp only [chosen] at found; exact ih found
      | some root =>
          simp only [chosen,Option.some.injEq] at found
          subst item
          have actual : (List.finRange state.arena.code.size).find? (fun root =>
              linked basis input.val root.val && ArenaSource.eligible state (proposal state input root address))=some root := chosen
          have valid := List.find?_some actual
          simp only [Bool.and_eq_true] at valid
          exact valid.symm

theorem pick_spec (state : ArenaSource.State) (basis : List Row) (item : ArenaSource.Labeled state.arena)
    (found : pick state basis=some item) :
    ArenaSource.eligible state item=true ∧ linked basis item.relation.left.val item.relation.right.val=true :=
  scan_spec state basis _ item found

theorem pick_relation (state : ArenaSource.State) (basis : List Row) (item : ArenaSource.Labeled state.arena)
    (found : pick state basis=some item) (environment : Nat → Bool)
    (held : holds basis (lift state environment)=true) : item.relation.read environment=true := by
  have equal := linked_holds basis item.relation.left.val item.relation.right.val (lift state environment) held (pick_spec state basis item found).2
  exact beq_iff_eq.mpr equal

def analyzed (state : ArenaSource.State) : CapacityMatching.SourceCost.Counted Result :=
  AffineRelationExtractionCost.iterate (formula state) (state.arena.code.size+1) (.basis [])

theorem analyzed_value (state : ArenaSource.State) :
    (analyzed state).value=JointFeedback.generate (formula state) [] := by
  rw [analyzed,AffineRelationExtractionCost.iterate_value,JointFeedback.generate]
  rfl

theorem analyzed_cells (state : ArenaSource.State) :
    (analyzed state).cells ≤ (state.arena.code.size+1)*
      (AffineRelationExtractionCost.jointBudget state.arena.code.size (formula state).length (Extract.literalCount (formula state))+2)+1 :=
  AffineRelationExtractionCost.iterate_cells _ _ _ ⟨triangular_nil,by simp [Result.within,RowsWithin]⟩

structure Update where
  state : ArenaSource.State
  rejected : Bool
  binding : List FunctionalSubstitution.Instruction
  joint : Option Result

def update (state : ArenaSource.State) : Update :=
  if noAdd state.arena.code then
    let source := analyzed state
    match source.value with
    | .contradiction => ⟨state,true,[],some source.value⟩
    | .basis basis =>
        match pick state basis with
        | none => ⟨state,false,[],some source.value⟩
        | some item =>
            ⟨ArenaSource.next state item.address item.relation.right,false,[ArenaSource.selected state item],some source.value⟩
  else ⟨state,false,[],none⟩

def Update.read (output : Update) (environment : Nat → Bool) : Bool :=
  !output.rejected && FunctionalAffine.legal output.binding environment && JointCircuit.read output.state environment

theorem next_read (state : ArenaSource.State) (address : Nat) (root : Fin state.arena.code.size) (environment : Nat → Bool) :
    read (ArenaSource.next state address root) environment=
      read state (ArenaAction.Action.environment state.arena address root environment) := by
  simp only [read,ArenaSource.next_program,ArenaSource.next_relations]

theorem update_read (state : ArenaSource.State) (environment : Nat → Bool) :
    (update state).read environment=read state environment := by
  by_cases checked : noAdd state.arena.code=true
  · simp only [update,checked,if_true]
    cases generated : (analyzed state).value with
    | contradiction =>
        simp only [Update.read,Bool.not_true,Bool.false_and]
        symm
        apply Bool.eq_false_iff.mpr
        intro accepted
        have source := generated_holds state checked environment accepted
        rw [← analyzed_value,generated] at source
        cases source
    | basis basis =>
        cases chosen : pick state basis with
        | none => simp [chosen,Update.read,FunctionalAffine.legal]
        | some item =>
            simp only [chosen,Update.read,Bool.not_false,Bool.true_and]
            have allowed := (pick_spec state basis item chosen).1
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.and_eq_true]
            constructor
            · rintro ⟨guard,accepted⟩
              have fixed := FunctionalAffine.legal_fixed [ArenaSource.selected state item] environment guard
              change (ArenaSource.selected state item).bind environment=environment at fixed
              rw [next_read,ArenaSource.selected_environment state item allowed,fixed] at accepted
              exact accepted
            · intro accepted
              have held := generated_holds state checked environment accepted
              rw [← analyzed_value,generated] at held
              have relation := pick_relation state basis item chosen environment held
              have fixed := ArenaSource.eligible_fixed state item allowed environment relation
              refine ⟨?_,?_⟩
              · apply FunctionalAffine.legal_of_fixed
                intro call member
                simp only [List.mem_singleton] at member
                subst call
                exact (ArenaSource.selected_environment state item allowed environment).symm.trans fixed
              · rw [next_read,fixed]
                exact accepted
  · simp [update,checked,Update.read,FunctionalAffine.legal]

theorem update_next_size (state : ArenaSource.State) : (update state).state.arena.code.size=state.arena.code.size := by
  by_cases checked : noAdd state.arena.code=true
  · cases generated : (analyzed state).value with
    | contradiction => simp [update,checked,generated]
    | basis basis =>
        cases found : pick state basis with
        | none => simp [update,checked,generated,found]
        | some item =>
            have changed : update state=⟨ArenaSource.next state item.address item.relation.right,false,
                [ArenaSource.selected state item],some (.basis basis)⟩ := by simp [update,checked,generated,found]
            rw [changed]
            exact ArenaSource.next_size _ _ _
  · simp [update,checked]

theorem update_relations (state : ArenaSource.State) : (update state).state.relations.length=state.relations.length := by
  by_cases checked : noAdd state.arena.code=true
  · cases generated : (analyzed state).value with
    | contradiction =>
        have unchanged : update state=⟨state,true,[],some .contradiction⟩ := by simp [update,checked,generated]
        rw [unchanged]
    | basis basis =>
        cases found : pick state basis with
        | none =>
            have unchanged : update state=⟨state,false,[],some (.basis basis)⟩ := by simp [update,checked,generated,found]
            rw [unchanged]
        | some item =>
            have changed : update state=⟨ArenaSource.next state item.address item.relation.right,false,
                [ArenaSource.selected state item],some (.basis basis)⟩ := by simp [update,checked,generated,found]
            rw [changed]
            exact ArenaSource.next_count _ _ _
  · have unchanged : update state=⟨state,false,[],none⟩ := by simp [update,checked]
    rw [unchanged]

theorem update_transport (state : ArenaSource.State) (environment : Nat → Bool) :
    (!(update state).rejected && read (update state).state environment)=
      read state (FunctionalSubstitution.fill (update state).binding environment) := by
  by_cases checked : noAdd state.arena.code=true
  · cases generated : (analyzed state).value with
    | contradiction =>
        have unchanged : update state=⟨state,true,[],some .contradiction⟩ := by simp [update,checked,generated]
        have old := update_read state environment
        rw [unchanged] at old ⊢
        simpa [Update.read,FunctionalAffine.legal,FunctionalSubstitution.fill] using old
    | basis basis =>
        cases found : pick state basis with
        | none =>
            have unchanged : update state=⟨state,false,[],some (.basis basis)⟩ := by simp [update,checked,generated,found]
            rw [unchanged]
            rfl
        | some item =>
            have changed : update state=⟨ArenaSource.next state item.address item.relation.right,false,
                [ArenaSource.selected state item],some (.basis basis)⟩ := by simp [update,checked,generated,found]
            rw [changed]
            simp only [Bool.not_false,Bool.true_and,next_read,ArenaSource.selected_environment state item (pick_spec state basis item found).1]
            rfl
  · have unchanged : update state=⟨state,false,[],none⟩ := by simp [update,checked]
    rw [unchanged]
    rfl

theorem update_correct (state : ArenaSource.State) :
    (∃ environment, (!(update state).rejected && read (update state).state environment)=true) ↔
      ∃ environment, read state environment=true := by
  constructor
  · rintro ⟨environment,accepted⟩
    refine ⟨FunctionalSubstitution.fill (update state).binding environment,?_⟩
    exact (update_transport state environment).symm.trans accepted
  · rintro ⟨environment,accepted⟩
    have result := (update_read state environment).trans accepted
    simp only [Update.read,Bool.and_eq_true] at result
    refine ⟨environment,?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨result.1.1,result.2⟩

theorem update_eliminates (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction)
    (member : call ∈ (update state).binding) : call.address ∉ FunctionalSubstitution.inputs (update state).state.arena.code := by
  by_cases checked : noAdd state.arena.code=true
  · cases generated : (analyzed state).value with
    | contradiction => simp [update,checked,generated] at member
    | basis basis =>
        cases found : pick state basis with
        | none => simp [update,checked,generated,found] at member
        | some item =>
            have changed : update state=⟨ArenaSource.next state item.address item.relation.right,false,
                [ArenaSource.selected state item],some (.basis basis)⟩ := by simp [update,checked,generated,found]
            rw [changed] at member ⊢
            simp only [List.mem_singleton] at member
            subst call
            have allowed := (pick_spec state basis item found).1
            simp only [ArenaSource.eligible,Bool.and_eq_true,decide_eq_true_eq] at allowed
            exact (FunctionalSubstitution.free_iff _ _).mp
              (ArenaAction.apply_free state.arena item.address item.relation.right
                ((ArenaAction.apply_performed _ _ _).mpr allowed.2))
  · simp [update,checked] at member

theorem valid_read (state : ArenaSource.State) (valid : ArenaSource.Valid state) (environment : Nat → Bool) :
    read state environment=truth (state.program.program.eval environment) := by
  cases accepted : truth (state.program.program.eval environment) with
  | false => simp [read,accepted]
  | true =>
      have relations := valid environment accepted
      change ArenaSource.readRelations state environment=true at relations
      simp [read,accepted,relations]

theorem original_read {n : Nat} (query : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (fuel : Nat) (environment : Nat → Bool) :
    (FunctionalAffine.legal (ArenaSource.compile query basis fuel).instructions environment &&
      (update (ArenaSource.compile query basis fuel).state).read environment)=
      CNFFormula.eval query (Gates.coordinate (Table.coordinates n basis) environment) := by
  have generated : ArenaSource.Valid (ArenaSource.compile query basis fuel).state :=
    ArenaSource.drive_valid _ _ (ArenaSource.build_valid _ _ (ArenaSource.front_entails query basis valid))
  rw [update_read,valid_read _ generated]
  exact ArenaSource.compile_read query basis valid fuel environment

def compile {n : Nat} (query : CNFFormula n) (basis : List Row) (fuel : Nat) : Update :=
  let source := ArenaSource.compile query basis fuel
  let output := update source.state
  ⟨output.state,output.rejected,source.instructions++output.binding,output.joint⟩

theorem compile_read {n : Nat} (query : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (fuel : Nat) (environment : Nat → Bool) :
    (compile query basis fuel).read environment=
      CNFFormula.eval query (Gates.coordinate (Table.coordinates n basis) environment) := by
  rw [← original_read query basis valid fuel environment]
  simp only [compile,Update.read,FunctionalAffine.legal,List.all_append]
  cases (update (ArenaSource.compile query basis fuel).state).rejected <;> simp [Bool.and_assoc]

def targetRead {n : Nat} (output : Update) (basis : List Row) (target : Assignment n) : Bool :=
  holds basis (extendAssignment target) && output.read (extendAssignment (projectFree n basis target))

theorem compile_target_read {n : Nat} (query : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (fuel : Nat) (target : Assignment n) :
    targetRead (compile query basis fuel) basis target=
      (CNFFormula.eval query (extendAssignment target) && holds basis (extendAssignment target)) := by
  rw [targetRead,compile_read query basis valid fuel]
  by_cases relations : holds basis (extendAssignment target)=true
  · have recovered := (Decision.table_lift n basis valid.2 (projectFree n basis target)).trans
      (parameterLift_projectFree n basis valid.1 target relations)
    have readback := congrArg (fun point => CNFFormula.eval query (extendAssignment point)) recovered
    have exactRead : CNFFormula.eval query (Gates.coordinate (Table.coordinates n basis)
        (extendAssignment (projectFree n basis target)))=CNFFormula.eval query (extendAssignment target) :=
      (formula_eval_restrict query _).symm.trans readback
    rw [relations,exactRead]
    simp
  · have rejected : holds basis (extendAssignment target)=false := Bool.eq_false_iff.mpr relations
    simp [rejected]

def projector {n : Nat} (query : CNFFormula n) (fuel : Nat) (source : Source n) : Source n :=
  let generated := compile query [] fuel
  fun point => if targetRead generated [] point then source point else 0

theorem projector_original {n : Nat} (query : CNFFormula n) (fuel : Nat) (source : Source n) :
    projector query fuel source=zeroProjector query source := by
  funext point
  simp only [projector,compile_target_read query [] ⟨triangular_nil,by simp [RowsWithin]⟩ fuel point,
    holds,List.all_nil,Bool.and_true,zeroProjector_apply]

end SaturationMonoid.ComplexityProjection.SATSource.JointCircuit
