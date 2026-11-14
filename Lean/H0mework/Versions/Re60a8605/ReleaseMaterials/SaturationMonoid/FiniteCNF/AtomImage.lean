import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Table

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AtomImage

open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine

structure Tagged where
  vars : List Nat
  label : Row
  deriving DecidableEq, Repr

def Tagged.coeff (row : Tagged) : Row := ⟨row.vars,false⟩
def Tagged.at (row : Tagged) (target : Nat → Bool) : Row := ⟨row.vars,Gates.value row.label target⟩

def Tagged.normalize (row : Tagged) : Tagged :=
  ⟨Parity.merge row.vars [],row.label.normalize⟩

def Tagged.xor (left right : Tagged) : Tagged :=
  ⟨Parity.merge left.vars right.vars,left.label.xor right.label⟩

theorem Tagged.normalize_coeff (row : Tagged) : row.normalize.coeff = row.coeff.normalize := rfl

theorem Tagged.xor_coeff (left right : Tagged) : (left.xor right).coeff = left.coeff.xor right.coeff := rfl

theorem Tagged.normalize_at (row : Tagged) (target : Nat → Bool) :
    row.normalize.at target = (row.at target).normalize := by
  change Row.mk _ (row.label.rhs ^^ row.label.normalize.eval target) = _
  rw [Row.normalize_eval]
  rfl

theorem Tagged.xor_at (left right : Tagged) (target : Nat → Bool) :
    (left.xor right).at target = (left.at target).xor (right.at target) := by
  change Row.mk _ (Gates.value (left.label.xor right.label) target) = _
  rw [Table.value_xor]
  rfl

def reduce : List Tagged → Tagged → Tagged
  | [], row => row
  | pivot :: rest, row =>
      match pivot.vars with
      | [] => reduce rest row
      | p :: _ => reduce rest (if p ∈ row.vars then row.xor pivot else row)

theorem reduce_coeff (basis : List Tagged) (row : Tagged) :
    (reduce basis row).coeff = reduceWith (basis.map Tagged.coeff) row.coeff := by
  induction basis generalizing row with
  | nil => rfl
  | cons pivot rest ih =>
      cases shape : pivot.vars with
      | nil => simpa [reduce, reduceWith, Tagged.coeff, shape] using ih row
      | cons p tail =>
          by_cases member : p ∈ row.vars
          · simpa [reduce, reduceWith, Tagged.coeff, shape, member, Tagged.xor, Row.xor] using ih (row.xor pivot)
          · simpa [reduce, reduceWith, Tagged.coeff, shape, member] using ih row

theorem reduce_at (basis : List Tagged) (row : Tagged) (target : Nat → Bool) :
    (reduce basis row).at target = reduceWith (basis.map (fun row => row.at target)) (row.at target) := by
  induction basis generalizing row with
  | nil => rfl
  | cons pivot rest ih =>
      cases shape : pivot.vars with
      | nil => simpa [reduce, reduceWith, Tagged.at, shape] using ih row
      | cons p tail =>
          by_cases member : p ∈ row.vars
          · have next := ih (row.xor pivot)
            rw [Tagged.xor_at] at next
            simpa [reduce, reduceWith, Tagged.at, shape, member] using next
          · simpa [reduce, reduceWith, Tagged.at, shape, member] using ih row

structure State where
  basis : List Tagged
  kernel : List Row
  deriving DecidableEq, Repr

def State.coeffs (state : State) : List Row := state.basis.map Tagged.coeff

def State.rows (state : State) (target : Nat → Bool) : List Row := state.basis.map (fun row => row.at target)

def State.holds (state : State) (input target : Nat → Bool) : Bool :=
  Affine.holds (state.rows target) input && Affine.holds state.kernel target

def initial : State := ⟨[],[]⟩

def insert (state : State) (row : Tagged) : State :=
  let reduced := reduce state.basis row.normalize
  match reduced.vars with
  | [] => ⟨state.basis,state.kernel ++ [reduced.label]⟩
  | _ :: _ => ⟨state.basis ++ [reduced],state.kernel⟩

theorem insert_coeffs (state : State) (row : Tagged) :
    Affine.Result.basis (insert state row).coeffs = (Affine.Result.basis state.coeffs).insert row.coeff := by
  simp only [Affine.Result.insert, State.coeffs, ← Tagged.normalize_coeff, ← reduce_coeff]
  cases shape : (reduce state.basis row.normalize).vars with
  | nil => simp [insert, shape, Tagged.coeff]
  | cons p rest => simp [insert, shape, Tagged.coeff]

theorem label_zero (row : Row) (input target : Nat → Bool) :
    (Row.mk [] (Gates.value row target)).holds input = row.holds target := by
  rw [empty_holds]
  simp only [Gates.value, Row.holds]
  cases row.rhs <;> cases row.eval target <;> rfl

theorem insert_holds (state : State) (row : Tagged) (input target : Nat → Bool) :
    (insert state row).holds input target = (state.holds input target && (row.at target).holds input) := by
  by_cases accepted : Affine.holds (state.rows target) input = true
  · have reduced : ((reduce state.basis row.normalize).at target).holds input = (row.at target).holds input := by
      rw [reduce_at, Tagged.normalize_at]
      exact (reduceWith_holds (state.rows target) (row.at target).normalize input accepted).trans
        (Row.normalize_holds (row.at target) input)
    have old : state.basis.all (fun row => (row.at target).holds input) = true := by
      simpa only [State.rows, Affine.holds, List.all_map, Function.comp_def] using accepted
    cases shape : (reduce state.basis row.normalize).vars with
    | nil =>
        have value : (reduce state.basis row.normalize).label.holds target = (row.at target).holds input := by
          rw [Tagged.at, shape, label_zero] at reduced
          exact reduced
        simp only [insert, shape, State.holds, State.rows, Affine.holds, List.all_append,
          List.all_cons, List.all_nil, Bool.and_true, List.all_map, Function.comp_def, old,
          Bool.true_and, value]
    | cons p rest =>
        simp only [insert, shape, State.holds, State.rows, List.map_append, List.map_cons, List.map_nil,
          Affine.holds, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
          List.all_map, Function.comp_def, old, Bool.true_and, reduced]
        exact Bool.and_comm _ _
  · have rejected := Bool.eq_false_iff.mpr accepted
    have old : state.basis.all (fun row => (row.at target).holds input) = false := by
      simpa only [State.rows, Affine.holds, List.all_map, Function.comp_def] using rejected
    cases shape : (reduce state.basis row.normalize).vars <;>
      simp [insert, shape, State.holds, State.rows, Affine.holds, List.all_append, Function.comp_def, old]

def runFrom : State → List Tagged → State
  | state, [] => state
  | state, row :: rest => runFrom (insert state row) rest

def run (rows : List Tagged) : State := runFrom initial rows

theorem runFrom_coeffs (state : State) (rows : List Tagged) :
    Affine.Result.basis (runFrom state rows).coeffs =
      eliminateFrom (.basis state.coeffs) (rows.map Tagged.coeff) := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih =>
      rw [runFrom, ih, insert_coeffs]
      rfl

theorem run_coeffs (rows : List Tagged) :
    eliminate (rows.map Tagged.coeff) = .basis (run rows).coeffs := (runFrom_coeffs initial rows).symm

theorem runFrom_holds (state : State) (rows : List Tagged) (input target : Nat → Bool) :
    (runFrom state rows).holds input target =
      (state.holds input target && Affine.holds (rows.map (fun row => row.at target)) input) := by
  induction rows generalizing state with
  | nil => simp [runFrom, Affine.holds]
  | cons row rest ih =>
      rw [runFrom, ih, insert_holds]
      simp [Affine.holds, Bool.and_assoc]

theorem run_holds (rows : List Tagged) (input target : Nat → Bool) :
    (run rows).holds input target = Affine.holds (rows.map (fun row => row.at target)) input := by
  rw [run, runFrom_holds]
  rfl

theorem rows_triangular (basis : List Tagged) (target : Nat → Bool)
    (triangular : Triangular (basis.map Tagged.coeff)) : Triangular (basis.map (fun row => row.at target)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro row member
    obtain ⟨tag,hit,rfl⟩ := List.mem_map.mp member
    exact triangular.1 tag.coeff (List.mem_map.mpr ⟨tag,hit,rfl⟩)
  · intro row member
    obtain ⟨tag,hit,rfl⟩ := List.mem_map.mp member
    exact triangular.2.1 tag.coeff (List.mem_map.mpr ⟨tag,hit,rfl⟩)
  · simpa only [List.pairwise_map, Above, Tagged.at, Tagged.coeff] using triangular.2.2

theorem run_triangular (rows : List Tagged) : Triangular (run rows).coeffs := by
  have result := eliminate_triangular (rows.map Tagged.coeff)
  simpa only [run_coeffs, Affine.Result.triangular] using result

def tagged (source : Array Row) : List Tagged :=
  List.ofFn fun i : Fin source.size => ⟨source[i].vars,⟨[i.val],source[i].rhs⟩⟩

def generate (source : Array Row) : State := run (tagged source)

def decode (source : Array Row) (target : Nat → Bool) : Nat → Bool :=
  fill ((generate source).rows target) (fun _ => false)

def Realizes (source : Array Row) (input target : Nat → Bool) : Prop :=
  ∀ i : Fin source.size, Gates.coordinate source input i.val = target i.val

theorem tagged_at (source : Array Row) (i : Fin source.size) (input target : Nat → Bool) :
    ((⟨source[i].vars,⟨[i.val],source[i].rhs⟩⟩ : Tagged).at target).holds input = true ↔
      Gates.coordinate source input i.val = target i.val := by
  rw [Row.holds_iff, Table.coordinate_getD]
  simp only [Tagged.at, Gates.value, Row.eval, Parity.eval, Bool.xor_false, Array.getD, i.isLt, ↓reduceDIte]
  cases source[i].rhs <;> cases Parity.eval input source[i].vars <;> cases target i.val <;> decide

theorem tagged_holds (source : Array Row) (input target : Nat → Bool) :
    Affine.holds ((tagged source).map (fun row => row.at target)) input = true ↔ Realizes source input target := by
  simp only [holds_iff, tagged, List.mem_map, List.mem_ofFn, Realizes]
  constructor
  · intro accepted i
    exact (tagged_at source i input target).mp (accepted _ ⟨_,⟨i,rfl⟩,rfl⟩)
  · rintro accepted row ⟨_,⟨i,rfl⟩,rfl⟩
    exact (tagged_at source i input target).mpr (accepted i)

theorem decode_realizes (source : Array Row) (target : Nat → Bool)
    (accepted : Affine.holds (generate source).kernel target = true) : Realizes source (decode source target) target := by
  apply (tagged_holds source _ target).mp
  rw [← run_holds]
  have filled := fill_holds ((generate source).rows target)
    (rows_triangular _ target (run_triangular (tagged source))) (fun _ => false)
  change (Affine.holds ((generate source).rows target) (decode source target) &&
    Affine.holds (generate source).kernel target) = true
  change Affine.holds ((generate source).rows target) (decode source target) = true at filled
  rw [filled, accepted]
  rfl

theorem image_iff_kernel (source : Array Row) (target : Nat → Bool) :
    (∃ input : Nat → Bool, Realizes source input target) ↔ Affine.holds (generate source).kernel target = true := by
  constructor
  · rintro ⟨input,realizes⟩
    have accepted := (tagged_holds source input target).mpr realizes
    rw [← run_holds] at accepted
    simp only [State.holds, Bool.and_eq_true] at accepted
    exact accepted.2
  · exact fun accepted => ⟨decode source target,decode_realizes source target accepted⟩

def Tagged.Valid (n q : Nat) (row : Tagged) : Prop :=
  Table.RowValid n row.coeff ∧ Table.RowValid q row.label

def State.Valid (n q : Nat) (state : State) : Prop :=
  (∀ row ∈ state.basis, row.Valid n q) ∧ ∀ row ∈ state.kernel, Table.RowValid q row

def SourceWithin (n : Nat) (source : Array Row) : Prop :=
  ∀ row ∈ source.toList, Parity.Within n row.vars

theorem Tagged.normalize_valid (n q : Nat) (row : Tagged)
    (coeff : Parity.Within n row.vars) (label : Parity.Within q row.label.vars) : row.normalize.Valid n q := by
  constructor
  · rw [Tagged.normalize_coeff]
    exact ⟨row.coeff.normalize_nodup,Row.normalize_within n row.coeff coeff⟩
  · exact ⟨row.label.normalize_nodup,Row.normalize_within q row.label label⟩

theorem Tagged.xor_valid (n q : Nat) (left right : Tagged) (a : left.Valid n q) (b : right.Valid n q) :
    (left.xor right).Valid n q := by
  constructor
  · rw [Tagged.xor_coeff]
    exact Table.xor_valid n left.coeff right.coeff a.1 b.1
  · exact Table.xor_valid q left.label right.label a.2 b.2

theorem reduce_valid (n q : Nat) (basis : List Tagged) (valid : ∀ row ∈ basis, row.Valid n q)
    (row : Tagged) (rowValid : row.Valid n q) : (reduce basis row).Valid n q := by
  induction basis generalizing row with
  | nil => exact rowValid
  | cons pivot rest ih =>
      have head := valid pivot (by simp)
      have tail : ∀ other ∈ rest, other.Valid n q := fun other member => valid other (by simp [member])
      cases shape : pivot.vars with
      | nil => simpa only [reduce,shape] using ih tail row rowValid
      | cons p vars =>
          simp only [reduce, shape]
          apply ih tail
          split
          · exact Tagged.xor_valid n q row pivot rowValid head
          · exact rowValid

theorem insert_valid (n q : Nat) (state : State) (valid : state.Valid n q) (row : Tagged)
    (coeff : Parity.Within n row.vars) (label : Parity.Within q row.label.vars) : (insert state row).Valid n q := by
  have reduced := reduce_valid n q state.basis valid.1 row.normalize (row.normalize_valid n q coeff label)
  cases shape : (reduce state.basis row.normalize).vars with
  | nil =>
    simp only [insert,shape]
    refine ⟨valid.1, ?_⟩
    intro other member
    rcases List.mem_append.mp member with old | last
    · exact valid.2 other old
    · simpa only [List.mem_singleton.mp last] using reduced.2
  | cons p rest =>
    simp only [insert,shape]
    refine ⟨?_,valid.2⟩
    intro other member
    rcases List.mem_append.mp member with old | last
    · exact valid.1 other old
    · simpa only [List.mem_singleton.mp last] using reduced

theorem runFrom_valid (n q : Nat) (state : State) (valid : state.Valid n q) (rows : List Tagged)
    (inside : ∀ row ∈ rows, Parity.Within n row.vars ∧ Parity.Within q row.label.vars) :
    (runFrom state rows).Valid n q := by
  induction rows generalizing state with
  | nil => exact valid
  | cons row rest ih =>
      exact ih (insert state row) (insert_valid n q state valid row (inside row (by simp)).1 (inside row (by simp)).2)
        (fun other member => inside other (by simp [member]))

theorem tagged_within (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    ∀ row ∈ tagged source, Parity.Within n row.vars ∧ Parity.Within source.size row.label.vars := by
  intro row member
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  refine ⟨inside source[i] (Array.getElem_mem_toList i.isLt), ?_⟩
  intro j member
  have same : j = i.val := by simpa using member
  exact same ▸ i.isLt

theorem generate_valid (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    (generate source).Valid n source.size :=
  runFrom_valid n source.size initial (by simp [State.Valid,initial]) (tagged source) (tagged_within n source inside)

theorem generate_within (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    RowsWithin n (generate source).coeffs := by
  intro row member
  obtain ⟨tag,hit,rfl⟩ := List.mem_map.mp member
  exact ((generate_valid n source inside).1 tag hit).1.2

theorem generate_rank (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    (generate source).basis.length ≤ n := by
  have bound := basis_length_le n (generate source).coeffs (run_triangular (tagged source))
    (generate_within n source inside)
  simpa only [State.coeffs,List.length_map] using bound

theorem insert_count (state : State) (row : Tagged) :
    (insert state row).basis.length + (insert state row).kernel.length = state.basis.length + state.kernel.length + 1 := by
  cases shape : (reduce state.basis row.normalize).vars <;> simp [insert,shape] <;> omega

theorem runFrom_count (state : State) (rows : List Tagged) :
    (runFrom state rows).basis.length + (runFrom state rows).kernel.length =
      state.basis.length + state.kernel.length + rows.length := by
  induction rows generalizing state with
  | nil => simp [runFrom]
  | cons row rest ih =>
      rw [runFrom, ih, insert_count]
      simp only [List.length_cons]
      omega

theorem generate_count (source : Array Row) :
    (generate source).basis.length + (generate source).kernel.length = source.size := by
  simpa only [generate,run,initial,List.length_nil,tagged,List.length_ofFn,Nat.zero_add] using
    runFrom_count initial (tagged source)

theorem generate_support (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    (∀ row ∈ (generate source).basis, row.vars.length ≤ n ∧ row.label.vars.length ≤ source.size) ∧
      ∀ row ∈ (generate source).kernel, row.vars.length ≤ source.size := by
  have valid := generate_valid n source inside
  constructor
  · intro row member
    exact ⟨Table.row_length_le n row.coeff (valid.1 row member).1,
      Table.row_length_le source.size row.label (valid.1 row member).2⟩
  · exact fun row member => Table.row_length_le source.size row (valid.2 row member)

def truncate (width : Nat) (target : Nat → Bool) : Nat → Bool := fun i => if i < width then target i else false

theorem coordinate_outside (source : Array Row) (input : Nat → Bool) (i : Nat) (outside : source.size ≤ i) :
    Gates.coordinate source input i = false := by
  rw [Table.coordinate_getD]
  simp [Array.getD, Nat.not_lt_of_ge outside, Gates.zeroRow, Gates.value, Row.eval, Parity.eval]

theorem decode_coordinate (source : Array Row) (target : Nat → Bool)
    (accepted : Affine.holds (generate source).kernel target = true) :
    Gates.coordinate source (decode source target) = truncate source.size target := by
  funext i
  by_cases inside : i < source.size
  · exact (decode_realizes source target accepted ⟨i,inside⟩).trans (by simp [truncate,inside])
  · simp [coordinate_outside source _ i (by omega), truncate, inside]

def bindTable (row : Tagged) (table : Array Row) : Array Row :=
  match row.vars with
  | [] => table
  | p :: tail => table.setIfInBounds p (Table.combine table tail row.label)

@[simp] theorem bindTable_size (row : Tagged) (table : Array Row) : (bindTable row table).size = table.size := by
  unfold bindTable
  split <;> simp

theorem bindTable_value (row : Tagged) (table : Array Row) (target : Nat → Bool)
    (inside : Parity.Within table.size row.vars) :
    Gates.coordinate (bindTable row table) target = (row.at target).bind (Gates.coordinate table target) := by
  cases shape : row.vars with
  | nil => simp [bindTable,Tagged.at,Row.bind,shape]
  | cons p tail =>
      have bound := inside p (by simp [shape])
      simp only [bindTable, Tagged.at, Row.bind, shape]
      rw [Table.coordinate_set table target p _ bound,Table.combine_value]

def backTable (basis : List Tagged) (table : Array Row) : Array Row := basis.foldr bindTable table

@[simp] theorem backTable_size (basis : List Tagged) (table : Array Row) : (backTable basis table).size = table.size := by
  induction basis with
  | nil => rfl
  | cons row rest ih => simpa only [backTable,List.foldr_cons,bindTable_size] using ih

theorem backTable_value (basis : List Tagged) (table : Array Row) (target : Nat → Bool)
    (inside : ∀ row ∈ basis, Parity.Within table.size row.vars) :
    Gates.coordinate (backTable basis table) target =
      fill (basis.map (fun row => row.at target)) (Gates.coordinate table target) := by
  induction basis with
  | nil => rfl
  | cons row rest ih =>
      have tail := ih (fun other member => inside other (by simp [member]))
      have head : Parity.Within (backTable rest table).size row.vars := by simpa using inside row (by simp)
      change Gates.coordinate (bindTable row (backTable rest table)) target =
        (row.at target).bind (fill (rest.map (fun row => row.at target)) (Gates.coordinate table target))
      rw [bindTable_value row _ target head,tail]

def zeroTable (n : Nat) : Array Row := (List.replicate n Gates.zeroRow).toArray

theorem zeroTable_value (n : Nat) (target : Nat → Bool) : Gates.coordinate (zeroTable n) target = fun _ => false := by
  funext i
  rw [Table.coordinate_getD]
  simp [zeroTable, Array.getD, Gates.value, Gates.zeroRow, Row.eval, Parity.eval]

def decoder (n : Nat) (source : Array Row) : Array Row := backTable (generate source).basis (zeroTable n)

@[simp] theorem decoder_size (n : Nat) (source : Array Row) : (decoder n source).size = n := by simp [decoder,zeroTable]

theorem decoder_value (n : Nat) (source : Array Row) (inside : SourceWithin n source) (target : Nat → Bool) :
    Gates.coordinate (decoder n source) target = decode source target := by
  rw [decoder, backTable_value, zeroTable_value]
  · rfl
  · intro row member
    simpa [zeroTable,Tagged.coeff] using ((generate_valid n source inside).1 row member).1.2

theorem decoder_recovers (n : Nat) (source : Array Row) (inside : SourceWithin n source) (target : Nat → Bool)
    (accepted : Affine.holds (generate source).kernel target = true) :
    Gates.coordinate source (Gates.coordinate (decoder n source) target) = truncate source.size target := by
  rw [decoder_value n source inside target]
  exact decode_coordinate source target accepted

theorem bindTable_valid (q : Nat) (row : Tagged) (label : Table.RowValid q row.label)
    (table : Array Row) (valid : Table.Valid q table) : Table.Valid q (bindTable row table) := by
  unfold bindTable
  split
  · exact valid
  · rename_i p tail shape
    have combined := Table.combine_valid q table valid tail row.label label
    intro other member
    have selected : other ∈ table.setIfInBounds p (Table.combine table tail row.label) := Array.mem_def.mpr member
    rcases Array.mem_or_eq_of_mem_setIfInBounds selected with old | last
    · exact valid other (Array.mem_def.mp old)
    · simpa only [last] using combined

theorem backTable_valid (q : Nat) (basis : List Tagged) (labels : ∀ row ∈ basis, Table.RowValid q row.label)
    (table : Array Row) (valid : Table.Valid q table) : Table.Valid q (backTable basis table) := by
  induction basis with
  | nil => exact valid
  | cons row rest ih =>
      exact bindTable_valid q row (labels row (by simp)) _ (ih (fun other member => labels other (by simp [member])))

theorem decoder_valid (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    Table.Valid source.size (decoder n source) := by
  apply backTable_valid source.size (generate source).basis
  · exact fun row member => ((generate_valid n source inside).1 row member).2
  · intro row member
    simp only [zeroTable,List.toList_toArray,List.mem_replicate] at member
    exact member.2 ▸ Table.zero_valid source.size

theorem decoder_storage (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    Gates.rowTerms (decoder n source).toList ≤ n * source.size := by
  simpa only [decoder_size] using Table.rowTerms_bound source.size (decoder n source) (decoder_valid n source inside)

theorem generated_label_storage (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    Gates.rowTerms ((generate source).basis.map Tagged.label ++ (generate source).kernel) ≤ source.size * source.size := by
  let labels := (generate source).basis.map Tagged.label ++ (generate source).kernel
  have valid : Table.Valid source.size labels.toArray := by
    intro row member
    simp only [labels,List.mem_append,List.mem_map] at member
    rcases member with ⟨tag,hit,rfl⟩ | old
    · exact ((generate_valid n source inside).1 tag hit).2
    · exact (generate_valid n source inside).2 row old
  have bound := Table.rowTerms_bound source.size labels.toArray valid
  have count : labels.length = source.size := by
    simpa only [labels,List.length_append,List.length_map] using generate_count source
  simpa only [List.toList_toArray,List.size_toArray,count] using bound

theorem generated_coeff_storage (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    Gates.rowTerms (generate source).coeffs ≤ n*n := by
  have valid : Table.Valid n (generate source).coeffs.toArray := by
    intro row member
    simp only [State.coeffs,List.mem_map] at member
    obtain ⟨tag,hit,rfl⟩ := member
    exact ((generate_valid n source inside).1 tag hit).1
  have bound := Table.rowTerms_bound n (generate source).coeffs.toArray valid
  have rank := generate_rank n source inside
  simp only [List.size_toArray,State.coeffs,List.length_map] at bound
  exact bound.trans (Nat.mul_le_mul_right n rank)

theorem kernel_false_iff (source : Array Row) (target : Nat → Bool) :
    Affine.holds (generate source).kernel target = false ↔ ¬ ∃ input : Nat → Bool, Realizes source input target := by
  rw [image_iff_kernel]
  exact Bool.eq_false_iff

def representative (n : Nat) (source : Array Row) (target : Assignment source.size) : Assignment n :=
  Gates.lift n (decoder n source) target

theorem representative_extends (n : Nat) (source : Array Row) (target : Assignment source.size) :
    extendAssignment (representative n source target) = Gates.coordinate (decoder n source) (extendAssignment target) := by
  funext i
  by_cases bounded : i < n
  · simp only [extendAssignment,bounded,↓reduceDIte,representative,Gates.lift]
  · have outside : (decoder n source).size ≤ i := by simp only [decoder_size]; omega
    simp only [extendAssignment,bounded,↓reduceDIte]
    exact (coordinate_outside _ _ i outside).symm

theorem representative_recovers (n : Nat) (source : Array Row) (inside : SourceWithin n source)
    (target : Assignment source.size) (accepted : Affine.holds (generate source).kernel (extendAssignment target) = true)
    (i : Fin source.size) :
    Gates.coordinate source (extendAssignment (representative n source target)) i.val = target i := by
  rw [representative_extends,decoder_recovers n source inside _ accepted]
  simp [truncate,extendAssignment,i.isLt]

theorem finite_image_iff_kernel (n : Nat) (source : Array Row) (inside : SourceWithin n source)
    (target : Assignment source.size) :
    (∃ input : Assignment n, ∀ i : Fin source.size, Gates.coordinate source (extendAssignment input) i.val = target i) ↔
      Affine.holds (generate source).kernel (extendAssignment target) = true := by
  constructor
  · rintro ⟨input,read⟩
    apply (image_iff_kernel source (extendAssignment target)).mp
    refine ⟨extendAssignment input,?_⟩
    intro i
    simpa [extendAssignment,i.isLt] using read i
  · intro accepted
    exact ⟨representative n source target,representative_recovers n source inside target accepted⟩

structure Model where
  state : State
  decoder : Array Row
  deriving Repr

/-- Elimination is performed once and its actual tagged basis generates the finite decoder. -/
def build (n : Nat) (source : Array Row) : Model :=
  let generated := generate source
  ⟨generated,backTable generated.basis (zeroTable n)⟩

/-- Conservative source-cell ledgers follow the actual two-sided row operations.
Computing these counters, address-bit operations and allocation microsteps have separate costs. -/
def reduceVisits : List Tagged → Tagged → Nat
  | [], _ => 1
  | pivot :: rest, row =>
      match pivot.vars with
      | [] => reduceVisits rest row + 2
      | p :: _ =>
          if p ∈ row.vars then reduceVisits rest (row.xor pivot) + pivotMemberVisits p row.vars +
            Table.mergeVisits row.vars pivot.vars + Table.mergeVisits row.label.vars pivot.label.vars + 4
          else reduceVisits rest row + pivotMemberVisits p row.vars + 2

def stepBudget (n q : Nat) : Nat := n*(2*n+5) + q*(2*q+5) + n + 7

theorem reduceVisits_bound (n q : Nat) (basis : List Tagged) (valid : ∀ row ∈ basis, row.Valid n q)
    (row : Tagged) (bounded : row.Valid n q) :
    reduceVisits basis row ≤ basis.length * stepBudget n q + 1 := by
  induction basis generalizing row with
  | nil => simp [reduceVisits]
  | cons pivot rest ih =>
      have first := valid pivot (by simp)
      have tail : ∀ other ∈ rest, other.Valid n q := fun other member => valid other (by simp [member])
      have noChange := ih tail row bounded
      have changed := ih tail (row.xor pivot) (Tagged.xor_valid n q row pivot bounded first)
      have coeffLength := Table.row_length_le n row.coeff bounded.1
      have labelLength := Table.row_length_le q row.label bounded.2
      have coeffScan := Table.mergeVisits_bound n row.vars pivot.vars bounded.1.2 first.1.1 first.1.2
      have labelScan := Table.mergeVisits_bound q row.label.vars pivot.label.vars bounded.2.2 first.2.1 first.2.2
      have coeffBound : Table.mergeVisits row.vars pivot.vars ≤ n*(2*n+5)+1 :=
        coeffScan.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ coeffLength) 1)
      have labelBound : Table.mergeVisits row.label.vars pivot.label.vars ≤ q*(2*q+5)+1 :=
        labelScan.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ labelLength) 1)
      cases shape : pivot.vars with
      | nil => simp only [reduceVisits,shape,List.length_cons]; unfold stepBudget at *; nlinarith
      | cons p restVars =>
          rw [shape] at coeffBound
          have members := pivotMemberVisits_bound p row.vars
          change row.vars.length ≤ n at coeffLength
          simp only [reduceVisits,shape,List.length_cons]
          split <;> unfold stepBudget at * <;> nlinarith

def tagTerms (rows : List Tagged) : Nat := (rows.map (fun row => row.vars.length + row.label.vars.length)).sum

def insertVisits (state : State) (row : Tagged) : Nat :=
  Table.mergeVisits row.vars [] + Table.mergeVisits row.label.vars [] +
    reduceVisits state.basis row.normalize + state.basis.length + state.kernel.length + 3

theorem insertVisits_bound (n q : Nat) (state : State) (valid : state.Valid n q)
    (rank : state.basis.length ≤ n) (count : state.basis.length+state.kernel.length ≤ q)
    (row : Tagged) (coeff : Parity.Within n row.vars) (label : Parity.Within q row.label.vars) :
    insertVisits state row ≤ (row.vars.length+row.label.vars.length)*(2*(n+q)+5) + n*stepBudget n q + q + 6 := by
  have coeffScan := Table.mergeVisits_bound n row.vars [] coeff (by simp) (by simp [Parity.Within])
  have labelScan := Table.mergeVisits_bound q row.label.vars [] label (by simp) (by simp [Parity.Within])
  have sourceBound : row.vars.length*(2*n+5) ≤ row.vars.length*(2*(n+q)+5) := Nat.mul_le_mul_left _ (by omega)
  have targetBound : row.label.vars.length*(2*q+5) ≤ row.label.vars.length*(2*(n+q)+5) := Nat.mul_le_mul_left _ (by omega)
  have reduced := reduceVisits_bound n q state.basis valid.1 row.normalize (row.normalize_valid n q coeff label)
  have reducedBound := Nat.mul_le_mul_right (stepBudget n q) rank
  unfold insertVisits
  nlinarith

def runVisits : State → List Tagged → Nat
  | _, [] => 1
  | state, row :: rest => insertVisits state row + runVisits (insert state row) rest + 1

theorem state_rank (n q : Nat) (state : State) (valid : state.Valid n q) (triangular : Triangular state.coeffs) :
    state.basis.length ≤ n := by
  have inside : RowsWithin n state.coeffs := by
    intro row member
    obtain ⟨tag,hit,rfl⟩ := List.mem_map.mp member
    exact (valid.1 tag hit).1.2
  simpa only [State.coeffs,List.length_map] using basis_length_le n state.coeffs triangular inside

theorem insert_triangular (state : State) (triangular : Triangular state.coeffs) (row : Tagged) :
    Triangular (insert state row).coeffs := by
  have result := Affine.Result.insert_triangular (.basis state.coeffs) triangular row.coeff
  rw [← insert_coeffs] at result
  exact result

theorem runVisits_bound (n q : Nat) (state : State) (valid : state.Valid n q) (triangular : Triangular state.coeffs)
    (rows : List Tagged) (inside : ∀ row ∈ rows, Parity.Within n row.vars ∧ Parity.Within q row.label.vars)
    (count : state.basis.length+state.kernel.length+rows.length ≤ q) :
    runVisits state rows ≤ tagTerms rows*(2*(n+q)+5) + rows.length*(n*stepBudget n q+q+7)+1 := by
  induction rows generalizing state with
  | nil => simp [runVisits,tagTerms]
  | cons row rest ih =>
      have first := inside row (by simp)
      have nextValid := insert_valid n q state valid row first.1 first.2
      have nextTriangular := insert_triangular state triangular row
      have nextCount : (insert state row).basis.length + (insert state row).kernel.length + rest.length ≤ q := by
        rw [insert_count]
        simp only [List.length_cons] at count
        omega
      have later := ih (insert state row) nextValid nextTriangular
        (fun other member => inside other (by simp [member])) nextCount
      have cost := insertVisits_bound n q state valid (state_rank n q state valid triangular) (by omega) row first.1 first.2
      simp only [runVisits,tagTerms,List.map_cons,List.sum_cons,List.length_cons]
      simp only [tagTerms] at later
      nlinarith

theorem tagged_terms (source : Array Row) : tagTerms (tagged source) = Gates.rowTerms source.toList + source.size := by
  have reads : List.ofFn (fun i : Fin source.size => source[i].vars.length) = source.toList.map (fun row => row.vars.length) := by
    simpa only [Array.length_toList,Array.getElem_toList,Fin.getElem_fin] using
      List.ofFn_getElem_eq_map source.toList (fun row => row.vars.length)
  simp only [tagTerms,tagged,List.map_ofFn]
  rw [show Gates.rowTerms source.toList = (List.ofFn (fun i : Fin source.size => source[i].vars.length)).sum by
    rw [reads]; rfl]
  simp [List.sum_ofFn,Finset.sum_add_distrib]

def generateVisits (source : Array Row) : Nat := runVisits initial (tagged source) + 4*source.size + 1

theorem generateVisits_bound (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    generateVisits source ≤
      (Gates.rowTerms source.toList+source.size)*(2*(n+source.size)+5) +
      source.size*(n*stepBudget n source.size+source.size+11)+2 := by
  have cost := runVisits_bound n source.size initial (by simp [State.Valid,initial]) triangular_nil (tagged source)
    (tagged_within n source inside) (by simp [initial,tagged])
  rw [tagged_terms] at cost
  have count : (tagged source).length = source.size := by simp [tagged]
  rw [count] at cost
  unfold generateVisits
  nlinarith

def bindVisits (row : Tagged) (table : Array Row) : Nat :=
  match row.vars with
  | [] => 1
  | _ :: tail => Table.combineVisits table tail row.label + table.size + 2

theorem bindVisits_bound (q : Nat) (row : Tagged) (label : Table.RowValid q row.label)
    (table : Array Row) (valid : Table.Valid q table) :
    bindVisits row table ≤ row.vars.length*(q*(2*q+5)+4)+table.size+3 := by
  cases shape : row.vars with
  | nil => simp [bindVisits,shape]
  | cons p rest =>
      have cost := Table.combineVisits_bound q table valid rest row.label label
      simp only [bindVisits,shape,List.length_cons]
      nlinarith

def backVisits : List Tagged → Array Row → Nat
  | [], _ => 1
  | row :: rest, table => backVisits rest table + bindVisits row (backTable rest table) + 1

theorem backVisits_bound (n q : Nat) (basis : List Tagged)
    (valid : ∀ row ∈ basis, row.Valid n q) (table : Array Row) (tableValid : Table.Valid q table) :
    backVisits basis table ≤ basis.length*(n*(q*(2*q+5)+4)+table.size+4)+1 := by
  induction basis with
  | nil => simp [backVisits]
  | cons row rest ih =>
      have first := valid row (by simp)
      have tail : ∀ other ∈ rest, other.Valid n q := fun other member => valid other (by simp [member])
      have later := ih tail
      have nextValid := backTable_valid q rest (fun other member => (tail other member).2) table tableValid
      have current := bindVisits_bound q row first.2 (backTable rest table) nextValid
      have short := Table.row_length_le n row.coeff first.1
      change row.vars.length ≤ n at short
      have scale := Nat.mul_le_mul_right (q*(2*q+5)+4) short
      simp only [backTable_size] at current
      simp only [backVisits,List.length_cons]
      nlinarith

def decoderVisits (n : Nat) (source : Array Row) : Nat := backVisits (generate source).basis (zeroTable n) + n + 1

theorem decoderVisits_bound (n : Nat) (source : Array Row) (inside : SourceWithin n source) :
    decoderVisits n source ≤ n*(n*(source.size*(2*source.size+5)+4)+n+4)+n+2 := by
  have zero : Table.Valid source.size (zeroTable n) := by
    intro row member
    simp only [zeroTable,List.toList_toArray,List.mem_replicate] at member
    exact member.2 ▸ Table.zero_valid source.size
  have cost := backVisits_bound n source.size (generate source).basis (generate_valid n source inside).1 (zeroTable n) zero
  have rank := generate_rank n source inside
  have size : (zeroTable n).size = n := by simp [zeroTable]
  rw [size] at cost
  have scaled := Nat.mul_le_mul_right (n*(source.size*(2*source.size+5)+4)+n+4) rank
  unfold decoderVisits
  omega

end SaturationMonoid.ComplexityProjection.SATSource.AtomImage
