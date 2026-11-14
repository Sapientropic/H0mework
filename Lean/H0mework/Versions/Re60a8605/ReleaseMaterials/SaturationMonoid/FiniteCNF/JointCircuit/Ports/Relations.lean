import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Ports.Embedding

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.PortRelations
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)

def independent (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) : Array Bool :=
  frame.ports.map (fun root => ArenaSource.eligible frame.state (JointCircuit.proposal frame.state input root address))

def table (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) : Array Row :=
  let source := Table.coordinates frame.state.arena.code.size basis
  Array.ofFn (fun i : Fin (frame.ports.size+1) =>
    if i.val=0 then source.getD input.val Gates.zeroRow
    else if flags.getD (i.val-1) false then source.getD (PortEmbedding.ref frame.state frame.ports (i.val-1)).val Gates.zeroRow
    else Gates.zeroRow)

theorem table_size (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) :
    (table frame input flags basis).size=frame.ports.size+1 := by simp only [table,Array.size_ofFn]

theorem table_valid (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) :
    Table.Valid (freeIndices frame.state.arena.code.size basis).length (table frame input flags basis) := by
  intro row member
  simp only [table,Array.toList_ofFn,List.mem_ofFn] at member
  obtain ⟨i,rfl⟩ := member
  split
  · exact Table.read_valid _ _ (Table.coordinates_valid _ _) _
  · split
    · exact Table.read_valid _ _ (Table.coordinates_valid _ _) _
    · exact Table.zero_valid _

theorem table_row (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row)
    (i : Nat) (inside : i < frame.ports.size+1) :
    (table frame input flags basis).getD i Gates.zeroRow=
      if i=0 then (Table.coordinates frame.state.arena.code.size basis).getD input.val Gates.zeroRow
      else if flags.getD (i-1) false then
        (Table.coordinates frame.state.arena.code.size basis).getD (PortEmbedding.ref frame.state frame.ports (i-1)).val Gates.zeroRow
      else Gates.zeroRow := by simp [table,Array.getD,inside]

def parameters (n : Nat) (basis : List Row) (point : Nat → Bool) : Nat → Bool :=
  extendAssignment (projectFree n basis (fun i => point i.val))

theorem coordinates_recover (n : Nat) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (point : Nat → Bool) (accepted : holds basis point=true) :
    Gates.coordinate (Table.coordinates n basis) (parameters n basis point)=extendAssignment (fun i : Fin n => point i.val) := by
  have finite := (AtomSource.holds_restrict n basis valid.2 point).trans accepted
  simp only [parameters,Table.coordinates_value n basis valid.2,← extend_parameterLift n basis valid.2,
    parameterLift_projectFree n basis valid.1 _ finite]

theorem coordinate_recover (n : Nat) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (point : Nat → Bool) (accepted : holds basis point=true) (i : Fin n) :
    Gates.value ((Table.coordinates n basis).getD i.val Gates.zeroRow) (parameters n basis point)=point i.val := by
  rw [← Table.coordinate_getD,coordinates_recover n basis valid point accepted,extendAssignment_apply]

def observed (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (point : Nat → Bool) : Nat → Bool :=
  fun i => if i=0 then JointCircuit.lift frame.state point input.val
    else if i ≤ frame.ports.size then
      if flags.getD (i-1) false then frame.read point (i-1) else false
    else false

theorem table_realizes (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift frame.state point)=true) :
    AtomImage.Realizes (table frame input flags basis)
      (parameters frame.state.arena.code.size basis (JointCircuit.lift frame.state point)) (observed frame input flags point) := by
  intro i
  have inside : i.val < frame.ports.size+1 := by simpa only [table_size] using i.isLt
  rw [Table.coordinate_getD,table_row frame input flags basis i.val inside]
  by_cases zero : i.val=0
  · simp only [zero,if_true,observed]
    exact coordinate_recover _ basis valid _ accepted input
  · simp only [zero,if_false,observed,show i.val ≤ frame.ports.size from by omega,if_true]
    by_cases flag : flags.getD (i.val-1) false=true
    · rw [if_pos flag,if_pos flag,coordinate_recover _ basis valid _ accepted]
      rfl
    · rw [if_neg flag,if_neg flag]
      rfl

def rows (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) : List Row :=
  (AtomImage.generate (table frame input flags basis)).kernel

theorem rows_holds (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift frame.state point)=true) :
    holds (rows frame input flags basis) (observed frame input flags point)=true :=
  (AtomImage.image_iff_kernel _ _).mp ⟨parameters _ basis (JointCircuit.lift frame.state point),
    table_realizes frame input flags basis valid point accepted⟩

theorem rows_valid (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row)
    (row : Row) (member : row ∈ rows frame input flags basis) : Table.RowValid (frame.ports.size+1) row := by
  have valid := (AtomImage.generate_valid _ (table frame input flags basis) (fun row member => (table_valid frame input flags basis row member).2)).2 row member
  simpa only [table_size] using valid

theorem rows_count (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) :
    (rows frame input flags basis).length ≤ frame.ports.size+1 := by
  have count := AtomImage.generate_count (table frame input flags basis)
  rw [table_size] at count
  change _+(rows frame input flags basis).length=frame.ports.size+1 at count
  omega


def terms (flags : Array Bool) : List Nat → List Nat
  | [] => []
  | i::rest =>
      if i=0 then terms flags rest
      else if flags.getD (i-1) false then (i-1)::terms flags rest else terms flags rest

theorem terms_length (flags : Array Bool) (indices : List Nat) : (terms flags indices).length ≤ indices.length := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      by_cases zero : i=0
      · simp only [terms,if_pos zero,List.length_cons]; omega
      · by_cases active : flags.getD (i-1) false=true
        · simp only [terms,if_neg zero,if_pos active,List.length_cons]; omega
        · simp only [terms,if_neg zero,if_neg active,List.length_cons]; omega

theorem terms_read (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (point : Nat → Bool)
    (indices : List Nat) (inside : ∀ i ∈ indices, i ≤ frame.ports.size) (nonzero : 0 ∉ indices) :
    Parity.eval (frame.read point) (terms flags indices)=Parity.eval (observed frame input flags point) indices := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      have valid := inside i (by simp)
      have nz : i≠0 := fun same => nonzero (by simp [same])
      have tail := ih (fun j member => inside j (by simp [member])) (fun hit => nonzero (by simp [hit]))
      simp only [terms,if_neg nz,Parity.eval,observed,if_pos valid]
      cases flag : flags.getD (i-1) false <;> simp only [Bool.false_eq_true,if_false,if_true,Parity.eval,tail,Bool.false_xor]

def body (flags : Array Bool) (row : Row) : Fragment := Gates.compileRow ⟨terms flags (row.vars.erase 0),row.rhs⟩

theorem body_size (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row)
    (row : Row) (member : row ∈ rows frame input flags basis) (pivot : 0 ∈ row.vars) :
    (body flags row).code.size ≤ 2*frame.ports.size+1 := by
  have size := Table.row_length_le _ row (rows_valid frame input flags basis row member)
  have erased := List.length_erase_add_one pivot
  have length := terms_length flags (row.vars.erase 0)
  simp only [body,Gates.compileRow_size]
  omega

theorem body_value (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift frame.state point)=true)
    (row : Row) (member : row ∈ rows frame input flags basis) (pivot : 0 ∈ row.vars) :
    truth ((body flags row).eval (frame.read point))=JointCircuit.lift frame.state point input.val := by
  have rowValid := rows_valid frame input flags basis row member
  have held := (holds_iff _ _).mp (rows_holds frame input flags basis valid point accepted) row member
  have equation := (Row.holds_iff row _).mp held
  rw [Row.eval,Parity.eval_erase _ _ 0 pivot] at equation
  have missing : 0 ∉ row.vars.erase 0 := rowValid.1.not_mem_erase
  have bounded : ∀ i ∈ row.vars.erase 0, i ≤ frame.ports.size := by
    intro i member
    exact Nat.le_of_lt_succ (rowValid.2 i (List.mem_of_mem_erase member))
  have remaining := terms_read frame input flags point (row.vars.erase 0) bounded missing
  simp only [body,Gates.eval_compileRow,truth_bit,Gates.value,Row.eval,remaining]
  change (JointCircuit.lift frame.state point input.val ^^ Parity.eval (observed frame input flags point) (row.vars.erase 0))=row.rhs at equation
  cases a : JointCircuit.lift frame.state point input.val <;>
    cases b : Parity.eval (observed frame input flags point) (row.vars.erase 0) <;> cases c : row.rhs <;> simp_all

structure Offer (frame : Frame) where
  input : Fin frame.state.arena.code.size
  address : Nat
  body : Fragment

def Offer.emission {frame : Frame} (offer : Offer frame) : PortEmbedding.Emission frame.state :=
  PortEmbedding.append frame.state frame.ports offer.body

def Offer.item {frame : Frame} (offer : Offer frame) : ArenaSource.Labeled offer.emission.target.arena :=
  ⟨offer.address,⟨offer.emission.ref offer.input,offer.emission.root⟩⟩

def Offer.allowed {frame : Frame} (offer : Offer frame) : Bool := ArenaSource.eligible offer.emission.target offer.item

def fromRow (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) (flags : Array Bool) (row : Row) : Offer frame :=
  ⟨input,address,body flags row⟩

theorem fromRow_holds (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) (flags : Array Bool) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift frame.state point)=true)
    (row : Row) (member : row ∈ rows frame input flags basis) (pivot : 0 ∈ row.vars) :
    (fromRow frame input address flags row).item.relation.read point=true := by
  have value := body_value frame input flags basis valid point accepted row member pivot
  simp only [fromRow,Offer.item,Offer.emission,ArenaAction.Relation.read,PortEmbedding.append_old,PortEmbedding.append_root]
  change (JointCircuit.lift frame.state point input.val==truth ((body flags row).eval (frame.read point)))=true
  simp only [value,beq_self_eq_true]


def scanRows (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) (flags : Array Bool) : List Row → Option (Offer frame)
  | [] => none
  | row::rest =>
      if 0 ∈ row.vars then
        let offer := fromRow frame input address flags row
        if offer.allowed then some offer else scanRows frame input address flags rest
      else scanRows frame input address flags rest

def Good (frame : Frame) (basis : List Row) (offer : Offer frame) : Prop :=
  offer.allowed=true ∧ offer.body.code.size ≤ 2*frame.ports.size+1 ∧
    ∀ point, holds basis (JointCircuit.lift frame.state point)=true → offer.item.relation.read point=true

theorem scanRows_spec (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) (flags : Array Bool) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) (available : List Row)
    (included : available ⊆ rows frame input flags basis) (offer : Offer frame)
    (found : scanRows frame input address flags available=some offer) : Good frame basis offer := by
  induction available with
  | nil => cases found
  | cons row rest ih =>
      have remaining : rest ⊆ rows frame input flags basis := fun row member => included (by simp [member])
      by_cases pivot : 0 ∈ row.vars
      · by_cases allowed : (fromRow frame input address flags row).allowed=true
        · simp only [scanRows,if_pos pivot,if_pos allowed,Option.some.injEq] at found
          subst offer
          exact ⟨allowed,body_size frame input flags basis row (included (by simp)) pivot,
            fun point held => fromRow_holds frame input address flags basis valid point held row (included (by simp)) pivot⟩
        · apply ih remaining
          simpa only [scanRows,if_pos pivot,if_neg allowed] using found
      · apply ih remaining
        simpa only [scanRows,if_neg pivot] using found

def forInput (frame : Frame) (basis : List Row) (input : Fin frame.state.arena.code.size) (address : Nat) : Option (Offer frame) :=
  let flags := independent frame input address
  scanRows frame input address flags (rows frame input flags basis)

theorem forInput_spec (frame : Frame) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis)
    (input : Fin frame.state.arena.code.size) (address : Nat) (offer : Offer frame) (found : forInput frame basis input address=some offer) :
    Good frame basis offer := scanRows_spec frame input address _ basis valid _ (by intro row member; exact member) offer found

def scan (frame : Frame) (basis : List Row) : List (Fin frame.state.arena.code.size) → Option (Offer frame)
  | [] => none
  | input::rest =>
      match JointCircuit.node frame.state input with
      | .input address =>
          match forInput frame basis input address with
          | some offer => some offer
          | none => scan frame basis rest
      | _ => scan frame basis rest

def pick (frame : Frame) (basis : List Row) : Option (Offer frame) := scan frame basis (List.finRange frame.state.arena.code.size)

theorem scan_spec (frame : Frame) (basis : List Row) (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis)
    (inputs : List (Fin frame.state.arena.code.size)) (offer : Offer frame) (found : scan frame basis inputs=some offer) : Good frame basis offer := by
  induction inputs with
  | nil => cases found
  | cons input rest ih =>
      cases shape : JointCircuit.node frame.state input <;> simp only [scan,shape] at found
      all_goals try exact ih found
      rename_i address
      cases selected : forInput frame basis input address with
      | none => exact ih (by simpa only [selected] using found)
      | some chosen =>
          simp only [selected,Option.some.injEq] at found
          subst offer
          exact forInput_spec frame basis valid input address chosen selected

theorem pick_spec (frame : Frame) (basis : List Row) (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis)
    (offer : Offer frame) (found : pick frame basis=some offer) : Good frame basis offer := scan_spec frame basis valid _ offer found

def generate (frame : Frame) : Option (Offer frame) :=
  if JointCircuit.noAdd frame.state.arena.code then
    match (JointCircuitCost.analyzed frame.state).value with
    | .contradiction => none
    | .basis basis => pick frame basis
  else none

theorem generate_spec (frame : Frame) (offer : Offer frame) (found : generate frame=some offer) :
    offer.allowed=true ∧ offer.body.code.size ≤ 2*frame.ports.size+1 ∧
      ∀ point, JointCircuit.read frame.state point=true → offer.item.relation.read point=true := by
  by_cases checked : JointCircuit.noAdd frame.state.arena.code=true
  · cases source : (JointCircuitCost.analyzed frame.state).value with
    | contradiction => simp [generate,checked,source] at found
    | basis basis =>
        have valid := JointCircuitCost.analyzed_valid frame.state
        have vb : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis := by simpa only [source,Result.triangular,Result.within] using valid
        have selected : pick frame basis=some offer := by simpa only [generate,checked,if_true,source] using found
        have good := pick_spec frame basis vb offer selected
        refine ⟨good.1,good.2.1,?_⟩
        intro point accepted
        have held := JointCircuit.generated_holds frame.state checked point accepted
        rw [← JointCircuit.analyzed_value,← JointCircuitCost.analyzed_value,source] at held
        exact good.2.2 point held
  · simp [generate,checked] at found

end SaturationMonoid.ComplexityProjection.SATSource.PortRelations
