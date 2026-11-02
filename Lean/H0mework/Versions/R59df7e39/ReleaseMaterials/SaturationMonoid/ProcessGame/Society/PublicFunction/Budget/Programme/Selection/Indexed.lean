import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Selection

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Selection.Indexed

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

private def readValue {Key : Type} [DecidableEq Key] : List (Key × ℚ) → Key → ℚ
  | [],_ => 0
  | (key,value)::rest,wanted => if key = wanted then value else readValue rest wanted

private theorem readValue_map {Key : Type} [DecidableEq Key] (keys : List Key) (value : Key → ℚ)
    (key : Key) (inside : key ∈ keys) : readValue (keys.map fun key => (key,value key)) key = value key := by
  induction keys with
  | nil => simp only [List.not_mem_nil] at inside
  | cons first rest ih =>
    by_cases same : first = key
    · subst first; simp [readValue]
    · have later : key ∈ rest := (List.mem_cons.mp inside).resolve_left (Ne.symm same)
      simp only [List.map_cons,readValue,if_neg same,ih later]

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local instance materialEq : DecidableEq (Settlement.Material Party Good) := by
  intro first second
  cases first <;> cases second <;> simp <;> infer_instance

local instance economicEq (code : Code Party Good Port (Mandate.State Party Technology) Instrument) :
    DecidableEq (EconomicAxis code) := by
  intro first second
  cases first <;> cases second <;> simp <;> infer_instance

structure Reading (code : Code Party Good Port (Mandate.State Party Technology) Instrument) where
  full : Evaluation code
  inventory : Authority.Trace.Lawful.Inventory (Authority.Trace.Lawful.Key Party Good Port Technology Instrument)
  values : List (EconomicAxis code × ℚ)

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (reference : Program model.source.code) (alternatives : List (Program model.source.code))

abbrev pool := reference :: alternatives
abbrev ProgramIndex := Fin (pool model reference alternatives).length

private def reading (world : Replanning.Point model domain)
    (table : Selection.TableAt model domain fallback (pool model reference alternatives) world)
    (program : Program model.source.code) : Reading model.source.code :=
  let full := Finite.tableEvaluation model world.val fallback (pool model reference alternatives) program table.val
  ⟨full,Authority.Trace.Lawful.inventory full.native,
    (economicAxes world.val.source world.val.cut).map fun axis => (axis,full.value axis)⟩

structure Row where
  world : Replanning.Point model domain
  table : Selection.TableAt model domain fallback (pool model reference alternatives) world
  cache : Array (Reading model.source.code)
  original : cache = ((pool model reference alternatives).map (reading model domain fallback reference alternatives world table)).toArray

namespace Row
variable {model domain fallback reference alternatives}

def generate (world : Replanning.Point model domain)
    (table : Selection.TableAt model domain fallback (pool model reference alternatives) world) :
    Row model domain fallback reference alternatives :=
  ⟨world,table,((pool model reference alternatives).map (reading model domain fallback reference alternatives world table)).toArray,rfl⟩

private theorem size (row : Row model domain fallback reference alternatives) : row.cache.size = (pool model reference alternatives).length := by
  rw [row.original]
  simp only [List.size_toArray,List.length_map]

def get (row : Row model domain fallback reference alternatives) (index : ProgramIndex model reference alternatives) : Reading model.source.code :=
  row.cache[index.val]'(by rw [size];exact index.isLt)

private theorem get_exact (row : Row model domain fallback reference alternatives) (index : ProgramIndex model reference alternatives) :
    row.get index = reading model domain fallback reference alternatives row.world row.table ((pool model reference alternatives)[index.val]) := by
  unfold get
  simp only [row.original,List.getElem_toArray,List.getElem_map]

theorem full_exact (row : Row model domain fallback reference alternatives) (index : ProgramIndex model reference alternatives) :
    (row.get index).full = Selection.readTable model domain fallback (pool model reference alternatives)
      row.world ((pool model reference alternatives)[index.val]) row.table := by rw [get_exact];rfl

theorem inventory_exact (row : Row model domain fallback reference alternatives) (index : ProgramIndex model reference alternatives) :
    (row.get index).inventory = Authority.Trace.Lawful.inventory
      (Selection.readTable model domain fallback (pool model reference alternatives) row.world ((pool model reference alternatives)[index.val]) row.table).native := by
  rw [get_exact];rfl

theorem value_exact (row : Row model domain fallback reference alternatives) (index : ProgramIndex model reference alternatives)
    (axis : Replanning.EconomicAt model domain row.world) :
    readValue (row.get index).values axis.val =
      (Selection.readTable model domain fallback (pool model reference alternatives) row.world ((pool model reference alternatives)[index.val]) row.table).value axis.val := by
  rw [get_exact]
  exact readValue_map _ _ axis.val axis.property

end Row

def rows : List (Row model domain fallback reference alternatives) :=
  (Replanning.points model domain).flatMap fun world =>
    (Finite.tables world.val fallback (pool model reference alternatives)).attach.map fun table => Row.generate (model := model) (domain := domain) (fallback := fallback) (reference := reference) (alternatives := alternatives) world table

theorem every_source_row_is_generated (world : Replanning.Point model domain)
    (table : Selection.TableAt model domain fallback (pool model reference alternatives) world) :
    Row.generate (model := model) (domain := domain) (fallback := fallback) (reference := reference) (alternatives := alternatives) world table ∈ rows model domain fallback reference alternatives :=
  List.mem_flatMap.mpr ⟨world,List.mem_attach _ _,List.mem_map.mpr ⟨table,List.mem_attach _ _,rfl⟩⟩

structure Snapshot where
  rows : List (Row model domain fallback reference alternatives)
  original : rows = Indexed.rows model domain fallback reference alternatives

def snapshot : Snapshot model domain fallback reference alternatives :=
  ⟨rows model domain fallback reference alternatives,rfl⟩

private def zero : ProgramIndex model reference alternatives := ⟨0,by simp only [pool,List.length_cons];omega⟩

def holds (row : Row model domain fallback reference alternatives) (index : ProgramIndex model reference alternatives) : Prop :=
  let current := row.get index
  let original := row.get (zero model reference alternatives)
  current.full.legal = true ∧ current.full.complete = true ∧ current.full.profile = original.full.profile ∧
    current.inventory.NoWorse original.inventory ∧
      ∀ axis ∈ economicAxes row.world.val.source row.world.val.cut,readValue current.values axis ≤ readValue original.values axis

instance (row : Row model domain fallback reference alternatives) (index : ProgramIndex model reference alternatives) :
    Decidable (holds model domain fallback reference alternatives row index) := by unfold holds;infer_instance

theorem holds_iff (row : Row model domain fallback reference alternatives) (index : ProgramIndex model reference alternatives) :
    holds model domain fallback reference alternatives row index ↔
    Synthesis.accepts model.source.code (economicAxes row.world.val.source row.world.val.cut)
      (Selection.readTable model domain fallback (pool model reference alternatives) row.world
        ((pool model reference alternatives)[index.val]) row.table)
      (Selection.readTable model domain fallback (pool model reference alternatives) row.world reference row.table) := by
  have prior : (pool model reference alternatives)[(zero model reference alternatives).val] = reference := rfl
  simp only [holds,Synthesis.accepts,Row.full_exact,Row.inventory_exact,prior,Authority.Trace.Lawful.NoWorse]
  constructor
  · rintro ⟨a,b,c,d,values⟩
    refine ⟨a,b,c,d,?_⟩
    intro axis inside
    have rowValue := values axis inside
    rw [Row.value_exact row index ⟨axis,inside⟩,Row.value_exact row (zero model reference alternatives) ⟨axis,inside⟩] at rowValue
    simpa only [prior] using rowValue
  · rintro ⟨a,b,c,d,values⟩
    refine ⟨a,b,c,d,?_⟩
    intro axis inside
    rw [Row.value_exact row index ⟨axis,inside⟩,Row.value_exact row (zero model reference alternatives) ⟨axis,inside⟩]
    simpa only [prior] using values axis inside

variable (saved : Snapshot model domain fallback reference alternatives)

def accepted (index : ProgramIndex model reference alternatives) : Prop :=
  ∀ row ∈ saved.rows,holds model domain fallback reference alternatives row index

instance (index : ProgramIndex model reference alternatives) :
    Decidable (accepted model domain fallback reference alternatives saved index) := by unfold accepted;infer_instance

theorem accepted_iff (index : ProgramIndex model reference alternatives) :
    accepted model domain fallback reference alternatives saved index ↔
      Selection.acceptable model domain fallback (pool model reference alternatives) reference ((pool model reference alternatives)[index.val]) := by
  rw [Selection.acceptable_iff_every_generated_cursor]
  constructor
  · intro all world table
    exact (holds_iff model domain fallback reference alternatives (Row.generate (model := model) (domain := domain) (fallback := fallback) (reference := reference) (alternatives := alternatives) world table) index).mp
      (all _ (saved.original ▸ every_source_row_is_generated model domain fallback reference alternatives world table))
  · intro all row _
    exact (holds_iff model domain fallback reference alternatives row index).mpr (all row.world row.table)

structure Candidate where
  index : ProgramIndex model reference alternatives
  accepted : Indexed.accepted model domain fallback reference alternatives saved index

def Candidate.original (candidate : Candidate model domain fallback reference alternatives saved) :
    Selection.Candidate model domain fallback (pool model reference alternatives) reference :=
  ⟨(pool model reference alternatives)[candidate.index.val],List.getElem_mem _,
    (accepted_iff model domain fallback reference alternatives saved candidate.index).mp candidate.accepted⟩

def check (index : ProgramIndex model reference alternatives) : Option (Candidate model domain fallback reference alternatives saved) :=
  if valid : accepted model domain fallback reference alternatives saved index then some ⟨index,valid⟩ else none

def candidates := (List.finRange (pool model reference alternatives).length).filterMap
  (check model domain fallback reference alternatives saved)

theorem every_accepted_index_is_generated (index : ProgramIndex model reference alternatives)
    (valid : accepted model domain fallback reference alternatives saved index) :
    (⟨index,valid⟩ : Candidate model domain fallback reference alternatives saved) ∈
      candidates model domain fallback reference alternatives saved := by
  apply List.mem_filterMap.mpr
  refine ⟨index,List.mem_finRange _,?_⟩
  simp only [check,dif_pos valid]

inductive Coordinate where
  | economic (row : Row model domain fallback reference alternatives) (axis : Replanning.EconomicAt model domain row.world)
  | native (row : Row model domain fallback reference alternatives) (anchor : ProgramIndex model reference alternatives)

def coordinates : List (Coordinate model domain fallback reference alternatives) := saved.rows.flatMap fun row =>
  (economicAxes row.world.val.source row.world.val.cut).attach.map (Coordinate.economic row) ++
    (List.finRange (pool model reference alternatives).length).map (Coordinate.native row)

def axis : Coordinate model domain fallback reference alternatives → Selection.Axis model domain fallback (pool model reference alternatives)
  | .economic row field => .economic row.world row.table field
  | .native row anchor => .native row.world row.table ((pool model reference alternatives)[anchor.val])

def benefit (candidate : Candidate model domain fallback reference alternatives saved) :
    Coordinate model domain fallback reference alternatives → ℚ
  | .economic row field => readValue (row.get candidate.index).values field.val
  | .native row anchor => if (row.get candidate.index).inventory.due.Subperm (row.get anchor).inventory.due then 0 else 1

theorem benefit_exact (candidate : Candidate model domain fallback reference alternatives saved)
    (coordinate : Coordinate model domain fallback reference alternatives) :
    benefit model domain fallback reference alternatives saved candidate coordinate =
      Selection.benefit model domain fallback (pool model reference alternatives)
        candidate.original.protocol (axis model domain fallback reference alternatives coordinate) := by
  cases coordinate with
  | economic row field => exact Row.value_exact row candidate.index field
  | native row anchor =>
    simp only [benefit,axis,Candidate.original,Row.inventory_exact,Selection.benefit,Selection.readTable]
    rfl

private theorem row_is_canonical (row : Row model domain fallback reference alternatives) :
    row = Row.generate (model := model) (domain := domain) (fallback := fallback) (reference := reference) (alternatives := alternatives) row.world row.table := by
  cases row with
  | mk world table cache original => cases original;rfl

private theorem each_cached_row_is_generated (row : Row model domain fallback reference alternatives) : row ∈ saved.rows := by
  rw [row_is_canonical model domain fallback reference alternatives row,saved.original]
  exact every_source_row_is_generated model domain fallback reference alternatives row.world row.table

theorem every_coordinate_is_generated (coordinate : Coordinate model domain fallback reference alternatives) :
    coordinate ∈ coordinates model domain fallback reference alternatives saved := by
  cases coordinate with
  | economic row field =>
    exact List.mem_flatMap.mpr ⟨row,each_cached_row_is_generated model domain fallback reference alternatives saved row,
      List.mem_append_left _ (List.mem_map.mpr ⟨field,List.mem_attach _ _,rfl⟩)⟩
  | native row anchor =>
    exact List.mem_flatMap.mpr ⟨row,each_cached_row_is_generated model domain fallback reference alternatives saved row,
      List.mem_append_right _ (List.mem_map.mpr ⟨anchor,List.mem_finRange _,rfl⟩)⟩

theorem each_axis_is_original (coordinate : Coordinate model domain fallback reference alternatives) :
    axis model domain fallback reference alternatives coordinate ∈ Selection.axes model domain fallback (pool model reference alternatives) := by
  cases coordinate with
  | economic row field =>
    exact List.mem_flatMap.mpr ⟨row.world,List.mem_attach _ _,List.mem_flatMap.mpr
      ⟨row.table,List.mem_attach _ _,List.mem_append_left _ (List.mem_map.mpr ⟨field,List.mem_attach _ _,rfl⟩)⟩⟩
  | native row anchor =>
    exact List.mem_flatMap.mpr ⟨row.world,List.mem_attach _ _,List.mem_flatMap.mpr
      ⟨row.table,List.mem_attach _ _,List.mem_append_right _ (List.mem_map.mpr
        ⟨(pool model reference alternatives)[anchor.val],List.getElem_mem _,rfl⟩)⟩⟩

private def nativeAnchor : Selection.Axis model domain fallback (pool model reference alternatives) → Option (Program model.source.code)
  | .economic _ _ _ => none
  | .native _ _ program => some program

private theorem native_anchor_is_original (world : Replanning.Point model domain)
    (table : Selection.TableAt model domain fallback (pool model reference alternatives) world)
    (program : Program model.source.code)
    (inside : Selection.Axis.native world table program ∈ Selection.axes model domain fallback (pool model reference alternatives)) :
    program ∈ pool model reference alternatives := by
  obtain ⟨_,_,entry⟩ := List.mem_flatMap.mp inside
  obtain ⟨_,_,entry⟩ := List.mem_flatMap.mp entry
  rcases List.mem_append.mp entry with economic | native
  · obtain ⟨field,_,same⟩ := List.mem_map.mp economic
    have impossible := congrArg (nativeAnchor model domain fallback reference alternatives) same
    cases impossible
  · obtain ⟨anchor,member,same⟩ := List.mem_map.mp native
    have exactAnchor := Option.some.inj (congrArg (nativeAnchor model domain fallback reference alternatives) same)
    exact exactAnchor ▸ member

theorem every_original_axis_has_a_cached_representative
    (original : Selection.Axis model domain fallback (pool model reference alternatives))
    (inside : original ∈ Selection.axes model domain fallback (pool model reference alternatives)) :
    ∃ coordinate : Coordinate model domain fallback reference alternatives,
      axis model domain fallback reference alternatives coordinate = original := by
  cases original with
  | economic world table field =>
    exact ⟨.economic (Row.generate (model := model) (domain := domain) (fallback := fallback) (reference := reference) (alternatives := alternatives) world table) field,rfl⟩
  | native world table program =>
    have member := native_anchor_is_original model domain fallback reference alternatives world table program inside
    obtain ⟨index,bounded,same⟩ := List.getElem_of_mem member
    exact ⟨.native (Row.generate (model := model) (domain := domain) (fallback := fallback) (reference := reference) (alternatives := alternatives) world table) ⟨index,bounded⟩,
      congrArg (Selection.Axis.native world table) same⟩

theorem noWorse_iff (left right : Candidate model domain fallback reference alternatives saved) :
    Distributed.NoWorse (coordinates model domain fallback reference alternatives saved)
      (benefit model domain fallback reference alternatives saved) left right ↔
    Distributed.NoWorse (Selection.axes model domain fallback (pool model reference alternatives))
      (fun candidate : Selection.Candidate model domain fallback (pool model reference alternatives) reference =>
        Selection.benefit model domain fallback (pool model reference alternatives) candidate.protocol)
      left.original right.original := by
  constructor
  · intro all original inside
    obtain ⟨coordinate,rfl⟩ := every_original_axis_has_a_cached_representative model domain fallback reference alternatives original inside
    have comparison := all coordinate (every_coordinate_is_generated model domain fallback reference alternatives saved coordinate)
    simpa only [benefit_exact] using comparison
  · intro all coordinate _
    rw [benefit_exact,benefit_exact]
    exact all _ (each_axis_is_original model domain fallback reference alternatives coordinate)

theorem improves_iff (left right : Candidate model domain fallback reference alternatives saved) :
    Distributed.Improves (coordinates model domain fallback reference alternatives saved)
      (benefit model domain fallback reference alternatives saved) left right ↔
    Distributed.Improves (Selection.axes model domain fallback (pool model reference alternatives))
      (fun candidate : Selection.Candidate model domain fallback (pool model reference alternatives) reference =>
        Selection.benefit model domain fallback (pool model reference alternatives) candidate.protocol)
      left.original right.original := by
  simp only [Distributed.Improves,noWorse_iff]

private theorem original_candidate_ext
    (left right : Selection.Candidate model domain fallback (pool model reference alternatives) reference)
    (same : left.protocol = right.protocol) : left = right := by
  cases left
  cases right
  cases same
  rfl

private theorem every_cached_candidate_is_original (candidate : Candidate model domain fallback reference alternatives saved) :
    candidate.original ∈ Selection.candidates model domain fallback (pool model reference alternatives) reference := by
  obtain ⟨other,inside,same⟩ := Selection.every_accepted_protocol_is_generated model domain fallback (pool model reference alternatives)
    reference candidate.original.protocol candidate.original.generated candidate.original.accepted
  exact original_candidate_ext model domain fallback reference alternatives other candidate.original same ▸ inside

private theorem every_original_candidate_has_a_cached_representative
    (candidate : Selection.Candidate model domain fallback (pool model reference alternatives) reference) :
    ∃ cached ∈ candidates model domain fallback reference alternatives saved, cached.original = candidate := by
  obtain ⟨index,bounded,same⟩ := List.getElem_of_mem candidate.generated
  let position : ProgramIndex model reference alternatives := ⟨index,bounded⟩
  have valid : accepted model domain fallback reference alternatives saved position :=
    (accepted_iff model domain fallback reference alternatives saved position).mpr (same ▸ candidate.accepted)
  let cached : Candidate model domain fallback reference alternatives saved := ⟨position,valid⟩
  refine ⟨cached,every_accepted_index_is_generated model domain fallback reference alternatives saved position valid,?_⟩
  apply original_candidate_ext model domain fallback reference alternatives
  exact same

/-- Compile the original complete relation from one source-generated evaluation tensor. -/
def compileWith (saved : Snapshot model domain fallback reference alternatives) :
    Selection.Outcome model domain fallback (pool model reference alternatives) reference :=
  match chosen : Distributed.choose (coordinates model domain fallback reference alternatives saved)
      (benefit model domain fallback reference alternatives saved) (candidates model domain fallback reference alternatives saved) with
  | some selection => .selected
      { policy := selection.policy.original
        original := every_cached_candidate_is_original model domain fallback reference alternatives saved selection.policy
        maximal := by
          intro other _ better
          obtain ⟨cached,inside,same⟩ := every_original_candidate_has_a_cached_representative model domain fallback reference alternatives saved other
          apply selection.maximal cached inside
          apply (improves_iff model domain fallback reference alternatives saved selection.policy cached).mpr
          simpa only [same] using better }
  | none => .blocked (fun program generated =>
      match Distributed.inspect (Selection.holds model domain fallback (pool model reference alternatives) reference program)
          (Selection.rows model domain fallback (pool model reference alternatives)) with
      | .rejected row inside broken => ⟨row,inside,broken⟩
      | .accepted all => False.elim (by
          let original : Selection.Candidate model domain fallback (pool model reference alternatives) reference := ⟨program,generated,all⟩
          obtain ⟨cached,inside,_⟩ := every_original_candidate_has_a_cached_representative model domain fallback reference alternatives saved original
          rw [Distributed.choose_none_iff_empty] at chosen
          simp only [chosen,List.not_mem_nil] at inside))

def compile : Selection.Outcome model domain fallback (pool model reference alternatives) reference :=
  compileWith model domain fallback reference alternatives (snapshot model domain fallback reference alternatives)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Selection.Indexed
