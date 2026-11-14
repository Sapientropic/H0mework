import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Product.Batch

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ProductRows
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)

theorem multiply_holds (frame : Frame) (point : Nat → Bool) (i : Nat) (hi : i < frame.ports.size)
    (row : Row) (within : Parity.Within frame.ports.size row.vars) (accepted : row.holds (frame.read point)=true) :
    (ProductSource.multiplyRow frame i row).holds ((ProductBatch.generate frame).read point)=true := by
  have equation := (Row.holds_iff row (frame.read point)).mp accepted
  have product : Parity.eval ((ProductBatch.generate frame).read point) (row.vars.map (ProductSource.index frame i))=
      (frame.read point i && row.eval (frame.read point)) := by
    rw [Parity.eval_map]
    have same := Parity.eval_congr (fun j => (ProductBatch.generate frame).read point (ProductSource.index frame i j))
      (fun j => frame.read point i && frame.read point j) row.vars
      (fun j member => ProductBatch.generate_product frame point i j hi (within j member))
    exact same.trans (ProductSource.product_distributes (frame.read point) (frame.read point i) row.vars)
  rw [Row.holds_iff]
  simp only [ProductSource.multiplyRow,Row.eval,ProductSource.parity_append]
  rw [product,equation]
  cases rhs : row.rhs <;> simp only [Bool.false_eq_true,if_false,if_true,Parity.eval,Bool.xor_false,
    Bool.and_false,Bool.and_true,ProductBatch.generate_old frame point i hi,Bool.xor_self]

theorem rows_holds (frame : Frame) (basis : List Row) (within : RowsWithin frame.ports.size basis) (point : Nat → Bool)
    (accepted : holds basis (frame.read point)=true) : holds (ProductSource.rows frame basis) ((ProductBatch.generate frame).read point)=true := by
  apply (holds_iff _ _).mpr
  intro row member
  simp only [ProductSource.rows,List.mem_flatMap,List.mem_range,List.mem_map] at member
  obtain ⟨i,hi,original,hit,rfl⟩ := member
  exact multiply_holds frame point i hi original (within original hit) ((holds_iff _ _).mp accepted original hit)

def diagonal (frame : Frame) (i : Nat) : Row := ⟨[ProductSource.index frame i i,i],false⟩

theorem diagonal_holds (frame : Frame) (point : Nat → Bool) (i : Nat) (inside : i < frame.ports.size) :
    (diagonal frame i).holds ((ProductBatch.generate frame).read point)=true := by
  simp only [diagonal,Row.holds,Row.eval,Parity.eval,ProductBatch.generate_product frame point i i inside inside,
    ProductBatch.generate_old frame point i inside,Bool.and_self,Bool.xor_false,Bool.xor_self,beq_self_eq_true]

def symmetric (frame : Frame) (pair : Nat × Nat) : Row :=
  ⟨[ProductSource.index frame pair.1 pair.2,ProductSource.index frame pair.2 pair.1],false⟩

theorem symmetric_holds (frame : Frame) (point : Nat → Bool) (i j : Nat) (hi : i < frame.ports.size) (hj : j < frame.ports.size) :
    (symmetric frame (i,j)).holds ((ProductBatch.generate frame).read point)=true := by
  simp only [symmetric,Row.holds,Row.eval,Parity.eval,ProductBatch.generate_product frame point i j hi hj,
    ProductBatch.generate_product frame point j i hj hi,Bool.and_comm,Bool.xor_false,Bool.xor_self,beq_self_eq_true]

def gate (frame : Frame) (output : Nat) : Node → List Row
  | .constant z => [⟨[output],truth z⟩]
  | .input _ | .add _ _ => []
  | .mul a b | .band a b => [⟨[output,ProductSource.index frame a b],false⟩,
      ⟨[ProductSource.index frame output a,output],false⟩,⟨[ProductSource.index frame output b,output],false⟩]
  | .neg a => [⟨[output,a],false⟩]
  | .bxor a b => [⟨[output,a,b],false⟩]
  | .bnot a => [⟨[output,a],true⟩]
  | .phase _ => [⟨[output],true⟩]
  | .select c a b => [⟨[output,a,ProductSource.index frame c a,ProductSource.index frame c b],false⟩,
      ⟨[ProductSource.index frame c output,ProductSource.index frame c b],false⟩]

theorem gate_equation (frame : Frame) (point : Nat → Bool) (output : Nat) (ho : output < frame.ports.size) (node : Node)
    (refs : ∀ i ∈ node.refs, i < frame.ports.size) :
    holds (gate frame output node) ((ProductBatch.generate frame).read point)=
      if JointCircuit.allowed node then JointCircuit.equation (frame.read point) (frame.read point output) node else true := by
  cases node with
  | constant z => simp [gate,holds,Row.holds,Row.eval,Parity.eval,ProductBatch.generate_old frame point output ho,JointCircuit.allowed,JointCircuit.equation]
  | input i => simp [gate,holds,JointCircuit.allowed,JointCircuit.equation]
  | add a b => rfl
  | phase a => simp [gate,holds,Row.holds,Row.eval,Parity.eval,ProductBatch.generate_old frame point output ho,JointCircuit.allowed,JointCircuit.equation]
  | mul a b | band a b =>
      have ha := refs a (by simp [Node.refs])
      have hb := refs b (by simp [Node.refs])
      simp only [gate,holds,List.all_cons,List.all_nil,Bool.and_true,Row.holds,Row.eval,Parity.eval,
        ProductBatch.generate_old frame point output ho,ProductBatch.generate_product frame point a b ha hb,
        ProductBatch.generate_product frame point output a ho ha,ProductBatch.generate_product frame point output b ho hb,
        JointCircuit.allowed,if_true,JointCircuit.equation]
      cases frame.read point output <;> cases frame.read point a <;> cases frame.read point b <;> rfl
  | neg a | bnot a =>
      have ha := refs a (by simp [Node.refs])
      simp only [gate,holds,List.all_cons,List.all_nil,Bool.and_true,Row.holds,Row.eval,Parity.eval,
        ProductBatch.generate_old frame point output ho,ProductBatch.generate_old frame point a ha,JointCircuit.allowed,if_true,JointCircuit.equation]
      cases frame.read point output <;> cases frame.read point a <;> rfl
  | bxor a b =>
      have ha := refs a (by simp [Node.refs])
      have hb := refs b (by simp [Node.refs])
      simp only [gate,holds,List.all_cons,List.all_nil,Bool.and_true,Row.holds,Row.eval,Parity.eval,
        ProductBatch.generate_old frame point output ho,ProductBatch.generate_old frame point a ha,ProductBatch.generate_old frame point b hb,
        JointCircuit.allowed,if_true,JointCircuit.equation]
      cases frame.read point output <;> cases frame.read point a <;> cases frame.read point b <;> rfl
  | select c a b =>
      have hc := refs c (by simp [Node.refs])
      have ha := refs a (by simp [Node.refs])
      have hb := refs b (by simp [Node.refs])
      simp only [gate,holds,List.all_cons,List.all_nil,Bool.and_true,Row.holds,Row.eval,Parity.eval,
        ProductBatch.generate_old frame point output ho,ProductBatch.generate_old frame point a ha,
        ProductBatch.generate_product frame point c a hc ha,ProductBatch.generate_product frame point c b hc hb,
        ProductBatch.generate_product frame point c output hc ho,
        JointCircuit.allowed,if_true,JointCircuit.equation]
      cases frame.read point output <;> cases frame.read point c <;> cases frame.read point a <;> cases frame.read point b <;> rfl

def gates (state : ArenaSource.State) : List Row :=
  (List.finRange state.arena.code.size).flatMap (fun i => gate (PortEmbedding.initial state) i.val (JointCircuit.node state i))

theorem gates_holds (state : ArenaSource.State) (point : Nat → Bool) :
    holds (gates state) ((ProductBatch.generate (PortEmbedding.initial state)).read point)=true := by
  simp only [gates,holds,List.all_flatMap]
  apply List.all_eq_true.mpr
  intro i _
  change holds (gate (PortEmbedding.initial state) i.val (JointCircuit.node state i)) _=true
  rw [gate_equation _ point i.val (by rw [PortEmbedding.initial_size]; exact i.isLt) _ ?_]
  · split
    · rename_i allowed
      have equation := JointCircuit.equation_run (JointCircuit.node state i) allowed point (run point state.arena.code)
      rw [← JointCircuit.node_read state point i] at equation
      rw [BranchPorts.initial_read state point i.val i.isLt]
      apply (JointCircuit.equation_congr _ (JointCircuit.node state i) _ (JointCircuit.lift state point) ?_).trans equation
      intro j present
      exact BranchPorts.initial_read state point j ((state.arena.forward i.val i.isLt j present).trans i.isLt)
    · rfl
  · intro j present
    rw [PortEmbedding.initial_size]
    exact (state.arena.forward i.val i.isLt j present).trans i.isLt

def laws (frame : Frame) : List Row :=
  (List.range frame.ports.size).map (diagonal frame)++(ProductSource.pairs frame.ports.size).map (symmetric frame)

theorem laws_holds (frame : Frame) (point : Nat → Bool) : holds (laws frame) ((ProductBatch.generate frame).read point)=true := by
  simp only [laws,holds,List.all_append,List.all_map,Bool.and_eq_true]
  constructor
  · exact List.all_eq_true.mpr (fun i member => diagonal_holds frame point i (List.mem_range.mp member))
  · exact List.all_eq_true.mpr (fun pair member => symmetric_holds frame point pair.1 pair.2
      ((ProductSource.pairs_mem _ _ _).mp member).1 ((ProductSource.pairs_mem _ _ _).mp member).2)

theorem basis_initial (state : ArenaSource.State) (basis : List Row) (within : RowsWithin state.arena.code.size basis)
    (point : Nat → Bool) (accepted : holds basis (JointCircuit.lift state point)=true) :
    holds basis ((PortEmbedding.initial state).read point)=true := by
  apply (holds_iff _ _).mpr
  intro row member
  have same := Parity.eval_congr ((PortEmbedding.initial state).read point) (JointCircuit.lift state point) row.vars
    (fun i hit => BranchPorts.initial_read state point i (within row member i hit))
  have original := (holds_iff _ _).mp accepted row member
  simpa only [Row.holds,Row.eval,same] using original

theorem basis_expanded (frame : Frame) (basis : List Row) (within : RowsWithin frame.ports.size basis)
    (point : Nat → Bool) (accepted : holds basis (frame.read point)=true) :
    holds basis ((ProductBatch.generate frame).read point)=true := by
  apply (holds_iff _ _).mpr
  intro row member
  have same := Parity.eval_congr ((ProductBatch.generate frame).read point) (frame.read point) row.vars
    (fun i hit => ProductBatch.generate_old frame point i (within row member i hit))
  have original := (holds_iff _ _).mp accepted row member
  simpa only [Row.holds,Row.eval,same] using original

def equations (state : ArenaSource.State) (basis : List Row) : List Row :=
  laws (PortEmbedding.initial state)++gates state++basis++ProductSource.rows (PortEmbedding.initial state) basis

theorem equations_holds (state : ArenaSource.State) (basis : List Row) (within : RowsWithin state.arena.code.size basis)
    (point : Nat → Bool) (accepted : holds basis (JointCircuit.lift state point)=true) :
    holds (equations state basis) ((ProductBatch.generate (PortEmbedding.initial state)).read point)=true := by
  have original := basis_initial state basis within point accepted
  have width : RowsWithin (PortEmbedding.initial state).ports.size basis := by rw [PortEmbedding.initial_size]; exact within
  have a := laws_holds (PortEmbedding.initial state) point
  have b := gates_holds state point
  have c := basis_expanded (PortEmbedding.initial state) basis width point original
  have d := rows_holds (PortEmbedding.initial state) basis width point original
  simp only [holds] at a b c d
  simp only [equations,holds,List.all_append,a,b,c,d,Bool.and_self]

def mapped (frame : Frame) (row : Row) : Row :=
  ⟨row.vars.map (fun i => (PortEmbedding.ref frame.state frame.ports i).val),row.rhs⟩

theorem mapped_holds (frame : Frame) (row : Row) (point : Nat → Bool) :
    (mapped frame row).holds (JointCircuit.lift frame.state point)=row.holds (frame.read point) := by
  simp only [mapped,Row.holds,Row.eval,Parity.eval_map]
  rfl

theorem mapped_within (frame : Frame) (row : Row) : Parity.Within frame.state.arena.code.size (mapped frame row).vars := by
  intro i member
  obtain ⟨j,hit,rfl⟩ := List.mem_map.mp member
  exact (PortEmbedding.ref frame.state frame.ports j).isLt

def analyze (frame : Frame) (rows : List Row) : Result := Affine.eliminate (rows.map (mapped frame))

theorem analyze_holds (frame : Frame) (rows : List Row) (point : Nat → Bool) :
    (analyze frame rows).holds (JointCircuit.lift frame.state point)=holds rows (frame.read point) := by
  simp only [analyze,Affine.eliminate_holds,holds,List.all_map,Function.comp_def,mapped_holds]

theorem analyze_valid (frame : Frame) (rows : List Row) :
    (analyze frame rows).triangular ∧ (analyze frame rows).within frame.state.arena.code.size := by
  exact ⟨Affine.eliminate_triangular _,Affine.eliminate_within _ _ (by
    intro row member
    obtain ⟨old,hit,rfl⟩ := List.mem_map.mp member
    exact mapped_within frame old)⟩

def seed (state : ArenaSource.State) : Result :=
  if JointCircuit.noAdd state.arena.code then (JointCircuitCost.analyzed state).value else .basis []

theorem seed_valid (state : ArenaSource.State) : (seed state).triangular ∧ (seed state).within state.arena.code.size := by
  unfold seed
  split
  · exact JointCircuitCost.analyzed_valid state
  · exact ⟨triangular_nil,by simp [Result.within,RowsWithin]⟩

theorem seed_holds (state : ArenaSource.State) (point : Nat → Bool) (accepted : JointCircuit.read state point=true) :
    (seed state).holds (JointCircuit.lift state point)=true := by
  unfold seed
  split
  · rename_i checked
    have source := JointCircuit.generated_holds state checked point accepted
    rw [JointCircuitCost.analyzed_value,JointCircuit.analyzed_value]
    exact source
  · rfl

def Holds (frame : Frame) (rows : List Row) : Prop :=
  ∀ point, JointCircuit.read frame.state point=true → holds rows (frame.read point)=true

structure Prepared where
  frame : Frame
  rows : List Row
  rejected : Bool

def prepare (state : ArenaSource.State) : Prepared :=
  let frame := ProductBatch.generate (PortEmbedding.initial state)
  match seed state with
  | .contradiction => ⟨frame,[],true⟩
  | .basis basis => ⟨frame,equations state basis,false⟩

theorem prepare_frame (state : ArenaSource.State) : (prepare state).frame=ProductBatch.generate (PortEmbedding.initial state) := by
  unfold prepare
  split <;> rfl

theorem prepare_read (state : ArenaSource.State) (point : Nat → Bool) :
    (!(prepare state).rejected && JointCircuit.read (prepare state).frame.state point)=JointCircuit.read state point := by
  cases generated : seed state with
  | contradiction =>
      have impossible : JointCircuit.read state point=false := by
        apply Bool.eq_false_iff.mpr
        intro accepted
        have bad := seed_holds state point accepted
        rw [generated] at bad
        cases bad
      simp [prepare,generated,impossible]
  | basis basis =>
      simp only [prepare,generated,Bool.not_false,Bool.true_and,ProductBatch.generate_read]
      rfl

theorem prepare_holds (state : ArenaSource.State) : Holds (prepare state).frame (prepare state).rows := by
  intro point accepted
  cases generated : seed state with
  | contradiction => simp [prepare,generated,holds]
  | basis basis =>
      have same : prepare state=⟨ProductBatch.generate (PortEmbedding.initial state),equations state basis,false⟩ := by
        simp [prepare,generated]
      rw [same] at accepted ⊢
      have valid := seed_valid state
      have within : RowsWithin state.arena.code.size basis := by simpa only [generated,Result.within] using valid.2
      rw [ProductBatch.generate_read] at accepted
      have source := seed_holds state point accepted
      rw [generated] at source
      exact equations_holds state basis within point source

def apply (frame : Frame) (item : ArenaSource.Labeled frame.state.arena) : PortUpdate.Output :=
  ⟨PortEmbedding.bind frame item.address item.relation.right,false,[ArenaSource.selected frame.state item],none⟩

theorem apply_read (frame : Frame) (item : ArenaSource.Labeled frame.state.arena) (allowed : ArenaSource.eligible frame.state item=true)
    (entailed : ∀ point, JointCircuit.read frame.state point=true → item.relation.read point=true) (point : Nat → Bool) :
    (apply frame item).value.read point=JointCircuit.read frame.state point := by
  change (FunctionalAffine.legal [ArenaSource.selected frame.state item] point &&
    JointCircuit.read (ArenaSource.next frame.state item.address item.relation.right) point)=_
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨guard,accepted⟩
    have fixed := FunctionalAffine.legal_fixed [ArenaSource.selected frame.state item] point guard
    change (ArenaSource.selected frame.state item).bind point=point at fixed
    rw [JointCircuit.next_read,ArenaSource.selected_environment frame.state item allowed,fixed] at accepted
    exact accepted
  · intro accepted
    have fixed := ArenaSource.eligible_fixed frame.state item allowed point (entailed point accepted)
    refine ⟨FunctionalAffine.legal_of_fixed _ point ?_,?_⟩
    · intro call member
      simp only [List.mem_singleton] at member
      subst call
      exact (ArenaSource.selected_environment frame.state item allowed point).symm.trans fixed
    · rw [JointCircuit.next_read,fixed]
      exact accepted

theorem apply_transport (frame : Frame) (item : ArenaSource.Labeled frame.state.arena)
    (allowed : ArenaSource.eligible frame.state item=true) (point : Nat → Bool) :
    JointCircuit.read (apply frame item).frame.state point=
      JointCircuit.read frame.state (FunctionalSubstitution.fill (apply frame item).binding point) := by
  change JointCircuit.read (ArenaSource.next frame.state item.address item.relation.right) point=
    JointCircuit.read frame.state ((ArenaSource.selected frame.state item).bind point)
  rw [JointCircuit.next_read,ArenaSource.selected_environment frame.state item allowed]

theorem apply_holds (frame : Frame) (rows : List Row) (known : Holds frame rows) (item : ArenaSource.Labeled frame.state.arena) :
    Holds (apply frame item).frame rows := by
  intro point accepted
  change holds rows ((PortEmbedding.bind frame item.address item.relation.right).read point)=true
  rw [BranchPorts.bind_read]
  apply known
  change JointCircuit.read (ArenaSource.next frame.state item.address item.relation.right) point=true at accepted
  rwa [JointCircuit.next_read] at accepted

def update (frame : Frame) (rows : List Row) : PortUpdate.Output :=
  match analyze frame rows with
  | .contradiction => ⟨frame,true,[],some .contradiction⟩
  | .basis basis =>
      match JointCircuit.pick frame.state basis with
      | none => ⟨frame,false,[],some (.basis basis)⟩
      | some item =>
          let changed := apply frame item
          ⟨changed.frame,changed.rejected,changed.binding,some (.basis basis)⟩

theorem update_read (frame : Frame) (rows : List Row) (known : Holds frame rows) (point : Nat → Bool) :
    (update frame rows).value.read point=JointCircuit.read frame.state point := by
  cases source : analyze frame rows with
  | contradiction =>
      have impossible : JointCircuit.read frame.state point=false := by
        apply Bool.eq_false_iff.mpr
        intro accepted
        have held := (analyze_holds frame rows point).trans (known point accepted)
        rw [source] at held
        cases held
      simp [update,source,PortUpdate.Output.value,JointCircuit.Update.read,impossible]
  | basis basis =>
      cases picked : JointCircuit.pick frame.state basis with
      | none => simp [update,source,picked,PortUpdate.Output.value,JointCircuit.Update.read,FunctionalAffine.legal]
      | some item =>
          have allowed := (JointCircuit.pick_spec frame.state basis item picked).1
          have entailed : ∀ point, JointCircuit.read frame.state point=true → item.relation.read point=true := by
            intro point accepted
            apply JointCircuit.pick_relation frame.state basis item picked point
            have held := (analyze_holds frame rows point).trans (known point accepted)
            simpa only [source,Result.holds] using held
          simp only [update,source,picked]
          exact apply_read frame item allowed entailed point

theorem update_transport (frame : Frame) (rows : List Row) (known : Holds frame rows) (point : Nat → Bool) :
    (!(update frame rows).rejected && JointCircuit.read (update frame rows).frame.state point)=
      JointCircuit.read frame.state (FunctionalSubstitution.fill (update frame rows).binding point) := by
  cases source : analyze frame rows with
  | contradiction =>
      have same := update_read frame rows known point
      simpa only [update,source,PortUpdate.Output.value,JointCircuit.Update.read,FunctionalAffine.legal,
        FunctionalSubstitution.fill,List.foldr_nil,Bool.not_true,Bool.false_and] using same
  | basis basis =>
      cases picked : JointCircuit.pick frame.state basis with
      | none => simp only [update,source,picked,Bool.not_false,Bool.true_and,FunctionalSubstitution.fill,List.foldr_nil]
      | some item =>
          have same := apply_transport frame item (JointCircuit.pick_spec frame.state basis item picked).1 point
          simpa only [update,source,picked,apply,Bool.not_false,Bool.true_and] using same

theorem update_holds (frame : Frame) (rows : List Row) (known : Holds frame rows) : Holds (update frame rows).frame rows := by
  cases source : analyze frame rows with
  | contradiction => simpa only [update,source] using known
  | basis basis =>
      cases picked : JointCircuit.pick frame.state basis with
      | none => simpa only [update,source,picked] using known
      | some item => simpa only [update,source,picked] using apply_holds frame rows known item

theorem update_size (frame : Frame) (rows : List Row) : (update frame rows).frame.state.arena.code.size=frame.state.arena.code.size := by
  cases source : analyze frame rows with
  | contradiction => simp only [update,source]
  | basis basis =>
      cases picked : JointCircuit.pick frame.state basis with
      | none => simp only [update,source,picked]
      | some item =>
          simp only [update,source,picked]
          change (PortEmbedding.bind frame item.address item.relation.right).state.arena.code.size=frame.state.arena.code.size
          exact ArenaSource.next_size _ _ _

theorem update_decreases (frame : Frame) (rows : List Row) (nonempty : (update frame rows).binding≠[]) :
    ArenaTotal.remaining (update frame rows).frame.state<ArenaTotal.remaining frame.state := by
  cases source : analyze frame rows with
  | contradiction => simp only [update,source,ne_eq,not_true_eq_false] at nonempty
  | basis basis =>
      cases picked : JointCircuit.pick frame.state basis with
      | none => simp only [update,source,picked,ne_eq,not_true_eq_false] at nonempty
      | some item =>
          simp only [update,source,picked]
          exact JointIteration.eligible_decreases frame.state item (JointCircuit.pick_spec frame.state basis item picked).1

theorem update_idle (frame : Frame) (rows : List Row) (empty : (update frame rows).binding=[]) : (update frame rows).frame=frame := by
  cases source : analyze frame rows with
  | contradiction => simp only [update,source]
  | basis basis =>
      cases picked : JointCircuit.pick frame.state basis with
      | none => simp only [update,source,picked]
      | some item => simp only [update,source,picked,apply,List.cons_ne_self] at empty

def iterate : Nat → Frame → List Row → PortUpdate.Output
  | 0,frame,_ => ⟨frame,false,[],none⟩
  | fuel+1,frame,rows =>
      let first := update frame rows
      if JointIteration.done first.value then first else PortUpdate.combine first (iterate fuel first.frame rows)

theorem iterate_read (fuel : Nat) (frame : Frame) (rows : List Row) (known : Holds frame rows) (point : Nat → Bool) :
    (iterate fuel frame rows).value.read point=JointCircuit.read frame.state point := by
  induction fuel generalizing frame with
  | zero => simp [iterate,PortUpdate.Output.value,JointCircuit.Update.read,FunctionalAffine.legal]
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_read frame rows known point
      · rename_i active
        have live := (JointIteration.continue_spec (update frame rows).value active).1
        change (update frame rows).rejected=false at live
        rw [PortUpdate.combine_value,JointIteration.combine_read,ih _ (update_holds frame rows known)]
        have first := update_read frame rows known point
        simpa only [PortUpdate.Output.value,JointCircuit.Update.read,live,Bool.not_false,Bool.true_and] using first

theorem iterate_transport (fuel : Nat) (frame : Frame) (rows : List Row) (known : Holds frame rows) (point : Nat → Bool) :
    (!(iterate fuel frame rows).rejected && JointCircuit.read (iterate fuel frame rows).frame.state point)=
      JointCircuit.read frame.state (FunctionalSubstitution.fill (iterate fuel frame rows).binding point) := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_transport frame rows known point
      · rename_i active
        have live := (JointIteration.continue_spec (update frame rows).value active).1
        change (update frame rows).rejected=false at live
        change (!(iterate fuel (update frame rows).frame rows).rejected && JointCircuit.read (iterate fuel (update frame rows).frame rows).frame.state point)=_
        rw [ih _ (update_holds frame rows known)]
        have first := update_transport frame rows known (FunctionalSubstitution.fill (iterate fuel (update frame rows).frame rows).binding point)
        simpa only [live,Bool.not_false,Bool.true_and,PortUpdate.combine,PortUpdate.fill_append] using first

theorem iterate_correct (fuel : Nat) (frame : Frame) (rows : List Row) (known : Holds frame rows) :
    (∃ point, (!(iterate fuel frame rows).rejected && JointCircuit.read (iterate fuel frame rows).frame.state point)=true) ↔
      ∃ point, JointCircuit.read frame.state point=true := by
  constructor
  · rintro ⟨point,accepted⟩
    exact ⟨FunctionalSubstitution.fill (iterate fuel frame rows).binding point,(iterate_transport fuel frame rows known point).symm.trans accepted⟩
  · rintro ⟨point,accepted⟩
    have result := (iterate_read fuel frame rows known point).trans accepted
    simp only [PortUpdate.Output.value,JointCircuit.Update.read,Bool.and_eq_true] at result
    exact ⟨point,by simp only [Bool.and_eq_true]; exact ⟨result.1.1,result.2⟩⟩

theorem iterate_size (fuel : Nat) (frame : Frame) (rows : List Row) : (iterate fuel frame rows).frame.state.arena.code.size=frame.state.arena.code.size := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_size frame rows
      · exact (ih (update frame rows).frame).trans (update_size frame rows)

def Settled (rows : List Row) (output : PortUpdate.Output) : Prop := output.rejected=true ∨ (update output.frame rows).binding=[]

theorem iterate_settled (fuel : Nat) (frame : Frame) (rows : List Row)
    (enough : ArenaTotal.remaining frame.state ≤ fuel) : Settled rows (iterate fuel frame rows) := by
  induction fuel generalizing frame with
  | zero =>
      apply Or.inr
      change (update frame rows).binding=[]
      by_contra nonempty
      have less := update_decreases frame rows nonempty
      omega
  | succ fuel ih =>
      simp only [iterate]
      split
      · rename_i stopped
        simp only [JointIteration.done,PortUpdate.Output.value,Bool.or_eq_true,List.isEmpty_iff] at stopped
        rcases stopped with rejected | empty
        · exact Or.inl rejected
        · apply Or.inr
          rw [update_idle frame rows empty]
          exact empty
      · rename_i active
        have less := update_decreases frame rows (JointIteration.continue_spec (update frame rows).value active).2
        exact ih (update frame rows).frame (by omega)

def run (state : ArenaSource.State) : PortUpdate.Output :=
  let source := prepare state
  if source.rejected then ⟨source.frame,true,[],none⟩ else
    iterate source.frame.state.arena.code.size source.frame source.rows

theorem run_read (state : ArenaSource.State) (point : Nat → Bool) : (run state).value.read point=JointCircuit.read state point := by
  have source := prepare_read state point
  by_cases rejected : (prepare state).rejected=true
  · simpa only [run,rejected,if_true,PortUpdate.Output.value,JointCircuit.Update.read,Bool.not_true,Bool.false_and] using source
  · rw [run,if_neg rejected,iterate_read _ _ _ (prepare_holds state)]
    simpa only [Bool.eq_false_iff.mpr rejected,Bool.not_false,Bool.true_and] using source

theorem run_correct (state : ArenaSource.State) :
    (∃ point, (!(run state).rejected && JointCircuit.read (run state).frame.state point)=true) ↔
      ∃ point, JointCircuit.read state point=true := by
  by_cases rejected : (prepare state).rejected=true
  · simp only [run,if_pos rejected,Bool.not_true,Bool.false_and,Bool.false_eq_true,exists_false,false_iff]
    rintro ⟨point,accepted⟩
    have source := prepare_read state point
    simp only [rejected,Bool.not_true,Bool.false_and,accepted] at source
    cases source
  · rw [run,if_neg rejected,iterate_correct _ _ _ (prepare_holds state)]
    apply exists_congr
    intro point
    have source := prepare_read state point
    simpa only [Bool.eq_false_iff.mpr rejected,Bool.not_false,Bool.true_and] using Eq.to_iff (congrArg (·=true) source)

theorem run_size (state : ArenaSource.State) :
    (run state).frame.state.arena.code.size ≤ state.arena.code.size+state.arena.code.size*state.arena.code.size+1 := by
  have size := ProductBatch.generate_size (PortEmbedding.initial state)
  simp only [PortEmbedding.initial_size] at size
  change (ProductBatch.generate (PortEmbedding.initial state)).state.arena.code.size ≤ _ at size
  rw [← prepare_frame] at size
  simp only [run]
  split
  · exact size
  · rw [iterate_size]
    exact size

theorem run_settled (state : ArenaSource.State) : Settled (prepare state).rows (run state) := by
  simp only [run]
  split
  · exact Or.inl rfl
  · exact iterate_settled _ _ _ (ArenaTotal.remaining_le_nodes _)

theorem update_ports (frame : Frame) (rows : List Row) : (update frame rows).frame.ports.size=frame.ports.size := by
  cases source : analyze frame rows with
  | contradiction =>
      have same : update frame rows=⟨frame,true,[],some .contradiction⟩ := by simp [update,source]
      rw [same]
  | basis basis =>
      cases picked : JointCircuit.pick frame.state basis with
      | none =>
          have same : update frame rows=⟨frame,false,[],some (.basis basis)⟩ := by simp [update,source,picked]
          rw [same]
      | some item =>
          have same : update frame rows=⟨(apply frame item).frame,false,(apply frame item).binding,some (.basis basis)⟩ := by
            simp [update,source,picked,apply]
          rw [same]
          exact PortEmbedding.bind_size frame item.address item.relation.right

theorem update_count (frame : Frame) (rows : List Row) : (update frame rows).frame.state.relations.length=frame.state.relations.length := by
  cases source : analyze frame rows with
  | contradiction =>
      have same : update frame rows=⟨frame,true,[],some .contradiction⟩ := by simp [update,source]
      rw [same]
  | basis basis =>
      cases picked : JointCircuit.pick frame.state basis with
      | none =>
          have same : update frame rows=⟨frame,false,[],some (.basis basis)⟩ := by simp [update,source,picked]
          rw [same]
      | some item =>
          have same : update frame rows=⟨(apply frame item).frame,false,(apply frame item).binding,some (.basis basis)⟩ := by
            simp [update,source,picked,apply]
          rw [same]
          exact ArenaSource.next_count frame.state item.address item.relation.right

theorem update_valid (frame : Frame) (rows : List Row) (valid : ArenaSource.Valid frame.state) : ArenaSource.Valid (update frame rows).frame.state := by
  cases source : analyze frame rows with
  | contradiction => simpa only [update,source] using valid
  | basis basis =>
      cases picked : JointCircuit.pick frame.state basis with
      | none => simpa only [update,source,picked] using valid
      | some item =>
          simp only [update,source,picked]
          change ArenaSource.Valid (ArenaSource.next frame.state item.address item.relation.right)
          exact ArenaSource.next_valid frame.state valid item.address item.relation.right

theorem iterate_valid (fuel : Nat) (frame : Frame) (rows : List Row) (valid : ArenaSource.Valid frame.state) :
    ArenaSource.Valid (iterate fuel frame rows).frame.state := by
  induction fuel generalizing frame with
  | zero => exact valid
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_valid frame rows valid
      · exact ih _ (update_valid frame rows valid)

theorem iterate_ports (fuel : Nat) (frame : Frame) (rows : List Row) : (iterate fuel frame rows).frame.ports.size=frame.ports.size := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      by_cases stopped : JointIteration.done (update frame rows).value=true
      · have same : iterate (fuel+1) frame rows=update frame rows := by simp [iterate,stopped]
        rw [same]
        exact update_ports frame rows
      · have same : iterate (fuel+1) frame rows=PortUpdate.combine (update frame rows) (iterate fuel (update frame rows).frame rows) := by simp [iterate,stopped]
        rw [same]
        exact (ih _).trans (update_ports frame rows)

theorem iterate_count (fuel : Nat) (frame : Frame) (rows : List Row) :
    (iterate fuel frame rows).frame.state.relations.length=frame.state.relations.length := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      by_cases stopped : JointIteration.done (update frame rows).value=true
      · have same : iterate (fuel+1) frame rows=update frame rows := by simp [iterate,stopped]
        rw [same]
        exact update_count frame rows
      · have same : iterate (fuel+1) frame rows=PortUpdate.combine (update frame rows) (iterate fuel (update frame rows).frame rows) := by simp [iterate,stopped]
        rw [same]
        exact (ih _).trans (update_count frame rows)

theorem update_port_read (frame : Frame) (rows : List Row) (point : Nat → Bool) :
    (update frame rows).frame.read point=frame.read (FunctionalSubstitution.fill (update frame rows).binding point) := by
  cases source : analyze frame rows with
  | contradiction => simp [update,source,FunctionalSubstitution.fill]
  | basis basis =>
      cases picked : JointCircuit.pick frame.state basis with
      | none => simp [update,source,picked,FunctionalSubstitution.fill]
      | some item =>
          simp only [update,source,picked,apply,FunctionalSubstitution.fill,List.foldr_cons,List.foldr_nil]
          have action := BranchPorts.bind_read frame item.address item.relation.right point
          exact action.trans (congrArg frame.read
            (ArenaSource.selected_environment frame.state item (JointCircuit.pick_spec frame.state basis item picked).1 point))

theorem iterate_port_read (fuel : Nat) (frame : Frame) (rows : List Row) (point : Nat → Bool) :
    (iterate fuel frame rows).frame.read point=frame.read (FunctionalSubstitution.fill (iterate fuel frame rows).binding point) := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_port_read frame rows point
      · change (iterate fuel (update frame rows).frame rows).frame.read point=
          frame.read (FunctionalSubstitution.fill ((update frame rows).binding++(iterate fuel (update frame rows).frame rows).binding) point)
        rw [PortUpdate.fill_append,ih]
        exact update_port_read frame rows _

theorem prepare_valid (state : ArenaSource.State) (valid : ArenaSource.Valid state) : ArenaSource.Valid (prepare state).frame.state := by
  rw [prepare_frame]
  exact ProductBatch.generate_valid (PortEmbedding.initial state) valid

theorem run_valid (state : ArenaSource.State) (valid : ArenaSource.Valid state) : ArenaSource.Valid (run state).frame.state := by
  simp only [run]
  split
  · exact prepare_valid state valid
  · exact iterate_valid _ _ _ (prepare_valid state valid)

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
      let bound := BranchPorts.inventoryBound (PortCost.capacity (PortCost.capacity
        (ArenaSource.sourceBound n formula.length (Extract.literalCount formula)))) (3*formula.length+n*n)
      bound+bound*bound+1 := by
  have first := BranchPorts.compile_size formula basis valid
  rw [← BranchCost.compile_value] at first
  exact (continueFrom_size (BranchCost.compile formula basis).value).trans (by dsimp only; gcongr)

open CapacityMatching.RowCost (rowCells rowsCells)

theorem flatMap_storage {α : Type} (source : List α) (build : α → List Row) (size : Nat)
    (bounded : ∀ a ∈ source, rowsCells (build a) ≤ size) : rowsCells (source.flatMap build) ≤ source.length*size := by
  induction source with
  | nil => simp [rowsCells]
  | cons first rest ih =>
      have head := bounded first (by simp)
      have tail := ih (fun a member => bounded a (by simp [member]))
      simp only [List.flatMap_cons,CapacityMatching.RowCost.rowsCells_append,List.length_cons]
      nlinarith

theorem mapped_storage (frame : Frame) (row : Row) : rowCells (mapped frame row)=rowCells row := by
  simp only [mapped,rowCells,List.length_map]

theorem gate_storage (frame : Frame) (output : Nat) (node : Node) : rowsCells (gate frame output node) ≤ 12 := by
  cases node <;> simp [gate,CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil,rowCells]

theorem gates_storage (state : ArenaSource.State) : rowsCells (gates state) ≤ 12*state.arena.code.size := by
  have bound := flatMap_storage (List.finRange state.arena.code.size)
    (fun i => gate (PortEmbedding.initial state) i.val (JointCircuit.node state i)) 12 (fun i _ => gate_storage _ _ _)
  simpa only [gates,List.length_finRange,Nat.mul_comm] using bound

theorem map_storage {α : Type} (source : List α) (build : α → Row) (size : Nat)
    (bounded : ∀ a ∈ source, rowCells (build a) ≤ size) : rowsCells (source.map build) ≤ source.length*size := by
  induction source with
  | nil => simp [rowsCells]
  | cons first rest ih =>
      have head := bounded first (by simp)
      have tail := ih (fun a member => bounded a (by simp [member]))
      simp only [List.map_cons,CapacityMatching.RowCost.rowsCells_cons,List.length_cons]
      nlinarith

theorem laws_storage (frame : Frame) : rowsCells (laws frame) ≤ 4*(frame.ports.size+frame.ports.size*frame.ports.size) := by
  have diagonal := map_storage (List.range frame.ports.size) (diagonal frame) 4 (by intro i _; simp [diagonal,rowCells])
  have symmetric := map_storage (ProductSource.pairs frame.ports.size) (symmetric frame) 4 (by intro pair _; simp [symmetric,rowCells])
  simp only [List.length_range,ProductSource.pairs_length] at diagonal symmetric
  simp only [laws,CapacityMatching.RowCost.rowsCells_append]
  nlinarith

theorem multiply_storage (frame : Frame) (i : Nat) (row : Row) : rowCells (ProductSource.multiplyRow frame i row) ≤ rowCells row+1 := by
  simp only [ProductSource.multiplyRow,rowCells,List.length_append,List.length_map]
  split <;> simp only [List.length_nil,List.length_singleton] <;> omega

theorem multiplyRows_storage (frame : Frame) (basis : List Row) :
    rowsCells (ProductSource.rows frame basis) ≤ frame.ports.size*(rowsCells basis+basis.length) := by
  have one (i : Nat) : rowsCells (basis.map (ProductSource.multiplyRow frame i)) ≤ rowsCells basis+basis.length := by
    induction basis with
    | nil => simp [rowsCells]
    | cons row rest ih =>
        have first := multiply_storage frame i row
        simp only [List.map_cons,CapacityMatching.RowCost.rowsCells_cons,List.length_cons]
        omega
  have result := flatMap_storage (List.range frame.ports.size) (fun i => basis.map (ProductSource.multiplyRow frame i))
    (rowsCells basis+basis.length) (fun i _ => one i)
  simpa only [ProductSource.rows,List.length_range] using result

def rowBound (nodes : Nat) : Nat := nodes*nodes*nodes+8*nodes*nodes+18*nodes

theorem equations_storage (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) : rowsCells (equations state basis) ≤ rowBound state.arena.code.size := by
  have count := basis_length_le state.arena.code.size basis valid.1 valid.2
  have basisValid : ∀ row ∈ basis, Table.RowValid state.arena.code.size row :=
    fun row member => ⟨valid.1.1 row member,valid.2 row member⟩
  have basisStored := AffineClauses.Cost.source_storage state.arena.code.size basis basisValid
  have stored : rowsCells basis ≤ state.arena.code.size*(state.arena.code.size+2) := basisStored.trans (by gcongr)
  have laws := laws_storage (PortEmbedding.initial state)
  have gates := gates_storage state
  have generated := multiplyRows_storage (PortEmbedding.initial state) basis
  simp only [PortEmbedding.initial_size] at laws generated
  have multiplied : rowsCells (ProductSource.rows (PortEmbedding.initial state) basis) ≤
      state.arena.code.size*(state.arena.code.size*(state.arena.code.size+2)+state.arena.code.size) := generated.trans (by gcongr)
  simp only [equations,CapacityMatching.RowCost.rowsCells_append,rowBound]
  nlinarith only [stored,laws,gates,multiplied]

theorem prepare_storage (state : ArenaSource.State) : rowsCells (prepare state).rows ≤ rowBound state.arena.code.size := by
  cases source : seed state with
  | contradiction => simp [prepare,source,rowsCells]
  | basis basis =>
      have valid : Triangular basis ∧ RowsWithin state.arena.code.size basis := by
        simpa only [source,Result.triangular,Result.within] using seed_valid state
      simp only [prepare,source]
      exact equations_storage state basis valid

end SaturationMonoid.ComplexityProjection.SATSource.ProductRows
