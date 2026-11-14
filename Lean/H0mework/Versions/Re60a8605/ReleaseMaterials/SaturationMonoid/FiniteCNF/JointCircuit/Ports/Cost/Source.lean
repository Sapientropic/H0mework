import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Ports.Cost.Core

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.PortCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)
open CapacityMatching.RowCost (rowCells rowsCells)

def rows (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) : Counted (List Row) :=
  let source := table frame input flags basis
  let generated := image frame.state.arena.code.size source.value
  ⟨generated.value.kernel,source.cells+generated.cells+
    8*(AffineCollect.tableSize source.value+AffineForget.Cost.imageSize generated.value+rowsCells generated.value.kernel+1)+16⟩

theorem rows_value (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) :
    (rows frame input flags basis).value=PortRelations.rows frame input flags basis := by
  simp only [rows,image_value,table_value,PortRelations.rows]

theorem rows_storage (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) :
    rowsCells (rows frame input flags basis).value ≤ (frame.ports.size+1)*(frame.ports.size+3) := by
  rw [rows_value]
  exact (AffineClauses.Cost.source_storage (frame.ports.size+1) _ (PortRelations.rows_valid frame input flags basis)).trans
    (by gcongr; exact PortRelations.rows_count frame input flags basis)

def rowsBudget (n p f : Nat) : Nat := tableBudget n p f+imageBudget n (p+1)+
  8*((p+1)*(n+2)+1+((n+(p+1))*(2*(n+(p+1))+3)+2)+(p+1)*(p+3)+1)+16

theorem rows_cells (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) :
    (rows frame input flags basis).cells ≤ rowsBudget frame.state.arena.code.size frame.ports.size flags.size := by
  let source := table frame input flags basis
  have known := table_valid frame input flags basis
  have size : source.value.size=frame.ports.size+1 := by rw [table_value,PortRelations.table_size]
  have first := table_cells frame input flags basis valid
  have second := image_cells frame.state.arena.code.size source.value known
  rw [size] at second
  have tableStored := table_storage frame input flags basis
  have count := AtomImage.generate_count source.value
  have generated := image_valid_mono frame.state.arena.code.size source.value.size
    (frame.state.arena.code.size+(frame.ports.size+1)) (AtomImage.generate source.value)
    (AtomImage.generate_valid _ source.value (fun row member => (known row member).2)) (by omega) (by omega)
  have imageStored := AffineForget.Cost.imageSize_bound _ (AtomImage.generate source.value) generated (by omega)
  have kernel := rows_storage frame input flags basis
  change rowsCells (image frame.state.arena.code.size source.value).value.kernel ≤ _ at kernel
  rw [← image_value frame.state.arena.code.size source.value] at imageStored
  simp only [rows,rowsBudget]
  change source.cells+(image frame.state.arena.code.size source.value).cells+
    8*(AffineCollect.tableSize source.value+AffineForget.Cost.imageSize (image frame.state.arena.code.size source.value).value+
      rowsCells (image frame.state.arena.code.size source.value).value.kernel+1)+16 ≤ _
  change source.cells ≤ _ at first
  change AffineCollect.tableSize source.value ≤ _ at tableStored
  omega

def terms (flags : Array Bool) : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | i::rest =>
      let tail := terms flags rest
      let output := if i=0 then tail.value else if flags.getD (i-1) false then (i-1)::tail.value else tail.value
      ⟨output,tail.cells+8*(flags.size+tail.value.length+1)+16⟩

theorem terms_value (flags : Array Bool) (indices : List Nat) : (terms flags indices).value=PortRelations.terms flags indices := by
  induction indices <;> simp_all only [terms,PortRelations.terms]

theorem terms_cells (flags : Array Bool) (indices : List Nat) :
    (terms flags indices).cells ≤ indices.length*(8*(flags.size+indices.length+1)+16)+1 := by
  induction indices with
  | nil => simp [terms]
  | cons i rest ih =>
      have length := PortRelations.terms_length flags rest
      simp only [terms,terms_value,List.length_cons]
      nlinarith

def body (flags : Array Bool) (row : Row) : Counted Fragment :=
  let indices := terms flags (row.vars.erase 0)
  let generated := ConditionalCandidateCost.Code.compileRow ⟨indices.value,row.rhs⟩
  ⟨generated.value,indices.cells+generated.cells+16*(row.vars.length+indices.value.length+generated.value.code.size+1)+24⟩

theorem body_value (flags : Array Bool) (row : Row) : (body flags row).value=PortRelations.body flags row := by
  simp only [body,terms_value,ConditionalCandidateCost.Code.compileRow_value,PortRelations.body]

def bodyBudget (p f : Nat) : Nat := (p+1)*(8*(f+(p+1)+1)+16)+1+
  ConditionalCandidateCost.Code.compileBudget (p+1)+16*((p+1)+(p+1)+(2*(p+1)+1)+1)+24

theorem body_cells (flags : Array Bool) (row : Row) (p : Nat) (bound : row.vars.length ≤ p+1) :
    (body flags row).cells ≤ bodyBudget p flags.size := by
  have erased : (row.vars.erase 0).length ≤ row.vars.length := List.length_erase_le
  have length := PortRelations.terms_length flags (row.vars.erase 0)
  have first := terms_cells flags (row.vars.erase 0)
  have firstBound : (terms flags (row.vars.erase 0)).cells ≤ (p+1)*(8*(flags.size+(p+1)+1)+16)+1 :=
    first.trans (by gcongr <;> omega)
  have second := ConditionalCandidateCost.Code.compileRow_cells (⟨(terms flags (row.vars.erase 0)).value,row.rhs⟩ : Row)
  have generated := ConditionalCandidateCost.Code.compileRow_size (⟨(terms flags (row.vars.erase 0)).value,row.rhs⟩ : Row)
  have boundTerms : (terms flags (row.vars.erase 0)).value.length ≤ p+1 := by rw [terms_value]; omega
  have secondBound := second.trans (ConditionalCandidateCost.Code.compileBudget_mono _ _ boundTerms)
  simp only [body,generated,bodyBudget]
  omega

def offerSize {frame : Frame} : Option (PortRelations.Offer frame) → Nat
  | none => 1
  | some offer => offer.body.code.size+9

def scanRows (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) (flags : Array Bool) :
    List Row → Counted (Option (PortRelations.Offer frame))
  | [] => ⟨none,1⟩
  | row::rest =>
      let contains := AffineClauseProduct.Cost.member 0 row.vars
      if contains.value then
        let compiled := body flags row
        let offer : PortRelations.Offer frame := ⟨input,address,compiled.value⟩
        let checked := allowed frame offer
        if checked.value then
          ⟨some offer,contains.visits+compiled.cells+checked.cells+16*(row.vars.length+compiled.value.code.size+1)+24⟩
        else
          let tail := scanRows frame input address flags rest
          ⟨tail.value,contains.visits+compiled.cells+checked.cells+tail.cells+
            16*(row.vars.length+compiled.value.code.size+offerSize tail.value+1)+24⟩
      else
        let tail := scanRows frame input address flags rest
        ⟨tail.value,contains.visits+tail.cells+16*(row.vars.length+offerSize tail.value+1)+24⟩

theorem scanRows_value (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) (flags : Array Bool) (available : List Row) :
    (scanRows frame input address flags available).value=PortRelations.scanRows frame input address flags available := by
  induction available with
  | nil => rfl
  | cons row rest ih =>
      simp only [scanRows,AffineClauseProduct.Cost.member_value,body_value,allowed_value,ih,PortRelations.scanRows,PortRelations.fromRow]
      split
      · split <;> simp_all
      · simp_all

theorem scanRows_storage (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) (flags : Array Bool)
    (basis available : List Row) (included : available ⊆ PortRelations.rows frame input flags basis) :
    offerSize (scanRows frame input address flags available).value ≤ 2*frame.ports.size+10 := by
  induction available with
  | nil => simp [scanRows,offerSize]
  | cons row rest ih =>
      have tail := ih (fun other member => included (by simp [member]))
      have member : row ∈ PortRelations.rows frame input flags basis := included (by simp)
      simp only [scanRows,AffineClauseProduct.Cost.member_value]
      split
      · rename_i pivot
        have size := PortRelations.body_size frame input flags basis row member (by simpa using pivot)
        split
        · simp only [offerSize,body_value]; omega
        · exact tail
      · exact tail

def scanRowBudget (n p c f : Nat) : Nat := 2*(p+1)+1+bodyBudget p f+allowedBudget n p c (2*p+1)+
  16*((p+1)+(2*p+1)+(2*p+10)+1)+24

theorem allowedBudget_mono (n N p P c C b B : Nat) (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) (hb : b ≤ B) :
    allowedBudget n p c b ≤ allowedBudget N P C B := by
  unfold allowedBudget appendBudget codeBudget ArenaCost.Reduction.budget
  gcongr
  exact eligibleBudget_mono _ _ (by omega)

theorem scanRows_cells (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) (flags : Array Bool)
    (basis available : List Row) (included : available ⊆ PortRelations.rows frame input flags basis) :
    (scanRows frame input address flags available).cells ≤
      available.length*scanRowBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length flags.size+1 := by
  induction available with
  | nil => simp [scanRows]
  | cons row rest ih =>
      have retained : rest ⊆ PortRelations.rows frame input flags basis := fun other member => included (by simp [member])
      have tail := ih retained
      have tailStored := scanRows_storage frame input address flags basis rest retained
      have member : row ∈ PortRelations.rows frame input flags basis := included (by simp)
      have length := Table.row_length_le _ row (PortRelations.rows_valid frame input flags basis row member)
      have scanned := AffineClauseProduct.Cost.member_visits 0 row.vars
      simp only [scanRows,AffineClauseProduct.Cost.member_value]
      split
      · rename_i pivot
        have compiled := body_cells flags row frame.ports.size length
        have size : (body flags row).value.code.size ≤ 2*frame.ports.size+1 := by
          rw [body_value]
          exact PortRelations.body_size frame input flags basis row member (by simpa using pivot)
        have checked := allowed_cells frame (⟨input,address,(body flags row).value⟩ : PortRelations.Offer frame)
        have work := checked.trans (allowedBudget_mono _ _ _ _ _ _ _ _ (by rfl) (by rfl) (by rfl) size)
        split <;> simp only [List.length_cons,scanRowBudget] at * <;> nlinarith
      · simp only [List.length_cons,scanRowBudget] at *
        nlinarith

def forInput (frame : Frame) (basis : List Row) (input : Fin frame.state.arena.code.size) (address : Nat) : Counted (Option (PortRelations.Offer frame)) :=
  let flags := independent frame input address
  let source := rows frame input flags.value basis
  let output := scanRows frame input address flags.value source.value
  ⟨output.value,flags.cells+source.cells+output.cells+16*(flags.value.size+rowsCells source.value+offerSize output.value+1)+24⟩

theorem forInput_value (frame : Frame) (basis : List Row) (input : Fin frame.state.arena.code.size) (address : Nat) :
    (forInput frame basis input address).value=PortRelations.forInput frame basis input address := by
  simp only [forInput,independent_value,rows_value,scanRows_value,PortRelations.forInput]

theorem forInput_storage (frame : Frame) (basis : List Row) (input : Fin frame.state.arena.code.size) (address : Nat) :
    offerSize (forInput frame basis input address).value ≤ 2*frame.ports.size+10 := by
  exact scanRows_storage frame input address (independent frame input address).value basis
    (rows frame input (independent frame input address).value basis).value (by rw [rows_value]; exact List.Subset.refl _)

def inputBudget (n p c : Nat) : Nat := independentBudget n p+rowsBudget n p p+(p+1)*scanRowBudget n p c p+1+
  16*(p+(p+1)*(p+3)+(2*p+10)+1)+24

theorem forInput_cells (frame : Frame) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis)
    (input : Fin frame.state.arena.code.size) (address : Nat) :
    (forInput frame basis input address).cells ≤ inputBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length := by
  let flags := independent frame input address
  let source := rows frame input flags.value basis
  have size : flags.value.size=frame.ports.size := by simp only [flags,independent_value,PortRelations.independent,Array.size_map]
  have first := independent_cells frame input address
  have second := rows_cells frame input flags.value basis valid
  have generated := scanRows_cells frame input address flags.value basis source.value (by rw [rows_value]; exact List.Subset.refl _)
  have count : source.value.length ≤ frame.ports.size+1 := by rw [rows_value]; exact PortRelations.rows_count _ _ _ _
  have bound := generated.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ count) 1)
  have rowsStored := rows_storage frame input flags.value basis
  have outputStored := forInput_storage frame basis input address
  change offerSize (scanRows frame input address flags.value source.value).value ≤ _ at outputStored
  rw [size] at second bound
  change flags.cells+source.cells+(scanRows frame input address flags.value source.value).cells+
    16*(flags.value.size+rowsCells source.value+offerSize (scanRows frame input address flags.value source.value).value+1)+24 ≤ _
  rw [size]
  change flags.cells ≤ _ at first
  change source.cells ≤ _ at second
  change rowsCells source.value ≤ _ at rowsStored
  unfold inputBudget
  omega

def scan (frame : Frame) (basis : List Row) : List (Fin frame.state.arena.code.size) → Counted (Option (PortRelations.Offer frame))
  | [] => ⟨none,1⟩
  | input::rest =>
      match JointCircuit.node frame.state input with
      | .input address =>
          let found := forInput frame basis input address
          match found.value with
          | some offer => ⟨some offer,found.cells+16*(frame.state.arena.code.size+offerSize found.value+1)+24⟩
          | none =>
              let tail := scan frame basis rest
              ⟨tail.value,found.cells+tail.cells+16*(frame.state.arena.code.size+offerSize tail.value+1)+24⟩
      | _ =>
          let tail := scan frame basis rest
          ⟨tail.value,tail.cells+16*(frame.state.arena.code.size+offerSize tail.value+1)+24⟩

theorem scan_value (frame : Frame) (basis : List Row) (inputs : List (Fin frame.state.arena.code.size)) :
    (scan frame basis inputs).value=PortRelations.scan frame basis inputs := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      cases shape : JointCircuit.node frame.state input <;> simp only [scan,shape,forInput_value,PortRelations.scan,ih]
      split <;> simp_all

theorem scan_storage (frame : Frame) (basis : List Row) (inputs : List (Fin frame.state.arena.code.size)) :
    offerSize (scan frame basis inputs).value ≤ 2*frame.ports.size+10 := by
  induction inputs with
  | nil => simp [scan,offerSize]
  | cons input rest ih =>
      cases shape : JointCircuit.node frame.state input <;> simp only [scan,shape]
      all_goals try exact ih
      rename_i address
      have first := forInput_storage frame basis input address
      cases found : (forInput frame basis input address).value with
      | none => exact ih
      | some offer => simpa only [found] using first

def scanBudget (n p c : Nat) : Nat := n*(inputBudget n p c+16*(n+(2*p+10)+1)+24)+1

theorem scan_cells (frame : Frame) (basis : List Row) (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis)
    (inputs : List (Fin frame.state.arena.code.size)) :
    (scan frame basis inputs).cells ≤ inputs.length*(inputBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length+
      16*(frame.state.arena.code.size+(2*frame.ports.size+10)+1)+24)+1 := by
  induction inputs with
  | nil => simp [scan]
  | cons input rest ih =>
      have tailStored := scan_storage frame basis rest
      cases shape : JointCircuit.node frame.state input <;> simp only [scan,shape,List.length_cons]
      all_goals try nlinarith
      rename_i address
      have first := forInput_cells frame basis valid input address
      have firstStored := forInput_storage frame basis input address
      cases found : (forInput frame basis input address).value with
      | none => simp only; nlinarith
      | some offer => simp only [found] at firstStored; simp only; nlinarith

def pick (frame : Frame) (basis : List Row) : Counted (Option (PortRelations.Offer frame)) :=
  let output := scan frame basis (List.finRange frame.state.arena.code.size)
  ⟨output.value,output.cells+16*frame.state.arena.code.size+16⟩

theorem pick_value (frame : Frame) (basis : List Row) : (pick frame basis).value=PortRelations.pick frame basis := by
  simp only [pick,scan_value,PortRelations.pick]

def generate (frame : Frame) : Counted (Option (PortRelations.Offer frame)) :=
  let checked := JointCircuitCost.checked frame.state.arena.code.toList
  if checked.value then
    let joint := JointCircuitCost.analyzed frame.state
    match joint.value with
    | .contradiction => ⟨none,checked.cells+joint.cells+16*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+1)+24⟩
    | .basis basis =>
        let output := pick frame basis
        ⟨output.value,checked.cells+joint.cells+output.cells+
          16*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+AffineCarrier.cellSize basis+offerSize output.value+1)+24⟩
  else ⟨none,checked.cells+16*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+1)+24⟩

theorem generate_value (frame : Frame) : (generate frame).value=PortRelations.generate frame := by
  simp only [generate,JointCircuitCost.checked_value,PortRelations.generate,JointCircuit.noAdd,pick_value]
  split
  · split <;> simp_all
  · simp_all

def generateBudget (n p c : Nat) : Nat := 4*n+1+JointCircuitCost.analysisBudget n c+scanBudget n p c+16*n+16+
  16*(n+c+p+AffineCarrier.Cost.cellBound n+(2*p+10)+1)+24

theorem generate_cells (frame : Frame) :
    (generate frame).cells ≤ generateBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length := by
  have checked := JointCircuitCost.checked_cells frame.state.arena.code.toList
  simp only [Array.length_toList] at checked
  have joint := JointCircuitCost.analyzed_cells frame.state
  have valid := JointCircuitCost.analyzed_valid frame.state
  simp only [generate]
  split
  · cases source : (JointCircuitCost.analyzed frame.state).value with
    | contradiction => simp only [generateBudget]; omega
    | basis basis =>
        have vb : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis := by
          simpa only [source,Result.triangular,Result.within] using valid
        have picked := scan_cells frame basis vb (List.finRange frame.state.arena.code.size)
        have kept := scan_storage frame basis (List.finRange frame.state.arena.code.size)
        have basisStored := AffineCarrier.Cost.cell_size frame.state.arena.code.size basis vb.1 vb.2
        simp only [List.length_finRange] at picked
        simp only [pick,generateBudget,scanBudget]
        omega
  · simp only [generateBudget]; omega

theorem generate_storage (frame : Frame) : offerSize (generate frame).value ≤ 2*frame.ports.size+10 := by
  simp only [generate]
  split
  · split
    · simp [offerSize]
    · exact scan_storage frame _ _
  · simp [offerSize]

end SaturationMonoid.ComplexityProjection.SATSource.PortCost
