import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Review
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Selection.Indexed

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Review.Tensor
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

private def lookup {Key : Type} [DecidableEq Key] : List (Key × ℚ) → Key → ℚ
  | [],_ => 0
  | (key,value)::rest,wanted => if key = wanted then value else lookup rest wanted

private theorem lookup_map {Key : Type} [DecidableEq Key] (keys : List Key) (value : Key → ℚ)
    (key : Key) (inside : key ∈ keys) : lookup (keys.map fun key => (key,value key)) key = value key := by
  induction keys with
  | nil => cases inside
  | cons first rest ih =>
    by_cases same : first = key
    · subst first;simp [lookup]
    · have later := (List.mem_cons.mp inside).resolve_left (Ne.symm same)
      simp only [List.map_cons,lookup,if_neg same,ih later]

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
local instance materialEq : DecidableEq (Settlement.Material Party Good) := by
  intro first second;cases first <;> cases second <;> simp <;> infer_instance
local instance economicEq (code : Code Party Good Port (Mandate.State Party Technology) Instrument) :
    DecidableEq (EconomicAxis code) := by
  intro first second;cases first <;> cases second <;> simp <;> infer_instance

variable {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (reference : Program model.source.code fuel)

abbrev programmes := reference :: programs model.source.code fuel
abbrev Index := Fin (programmes model reference).length
abbrev Reading := Budget.Programme.Selection.Indexed.Reading model.source.code
abbrev Context (point : Cursor model.source.code) := Option (Cut.Table point.source point.entry point.cut)

def evaluation (point : Cursor model.source.code) (table : Context model point)
    (programme : Program model.source.code fuel) : Evaluation model.source.code :=
  match table with
  | none => actualEvaluation model point original programme PublicDomain.silent
  | some table => tableEvaluation model point original programme table

/-- Force every scalar and the complete native inventory once, before comparison. -/
def reading (point : Cursor model.source.code) (table : Context model point)
    (programme : Program model.source.code fuel) : Reading model :=
  let full := evaluation model original point table programme
  ⟨full,Authority.Trace.Lawful.inventory full.native,
    (economicAxes point.source point.cut).map fun axis => (axis,full.value axis)⟩

structure Row where
  world : Replanning.Point model domain
  table : Context model world.val
  cache : Array (Reading model)
  original : cache = ((programmes model reference).map (reading model original world.val table)).toArray

namespace Row
variable {model domain original reference}
def generate (world : Replanning.Point model domain) (table : Context model world.val) :
    Row model domain original reference :=
  ⟨world,table,((programmes model reference).map (reading model original world.val table)).toArray,rfl⟩
private theorem size (row : Row model domain original reference) :
    row.cache.size = (programmes model reference).length := by
  rw [row.original];simp only [List.size_toArray,List.length_map]
def get (row : Row model domain original reference) (index : Index model reference) : Reading model :=
  row.cache[index.val]'(by rw [size];exact index.isLt)
theorem get_exact (row : Row model domain original reference) (index : Index model reference) :
    row.get index = reading model original row.world.val row.table ((programmes model reference)[index.val]) := by
  unfold get
  simp only [row.original,List.getElem_toArray,List.getElem_map]
theorem full_exact (row : Row model domain original reference) (index : Index model reference) :
    (row.get index).full = evaluation model original row.world.val row.table ((programmes model reference)[index.val]) := by
  rw [get_exact];rfl
theorem inventory_exact (row : Row model domain original reference) (index : Index model reference) :
    (row.get index).inventory = Authority.Trace.Lawful.inventory
      (evaluation model original row.world.val row.table ((programmes model reference)[index.val])).native := by
  rw [get_exact];rfl
theorem value_exact (row : Row model domain original reference) (index : Index model reference)
    (axis : EconomicAxis model.source.code) (inside : axis ∈ economicAxes row.world.val.source row.world.val.cut) :
    lookup (row.get index).values axis =
      (evaluation model original row.world.val row.table ((programmes model reference)[index.val])).value axis := by
  rw [get_exact]
  exact lookup_map _ _ axis inside
end Row

/-- Quiet equality shares one row; otherwise every original adaptive table remains. -/
def rows : List (Row model domain original reference) :=
  if PublicDomain.quiet (code := model.source.code) then
    (Replanning.points model domain).map fun world => Row.generate world none
  else
    (Replanning.points model domain).flatMap fun world =>
      (Cut.tables world.val.source world.val.entry world.val.cut).map fun table => Row.generate world (some table)

structure Snapshot where
  rows : List (Row model domain original reference)
  original : rows = Tensor.rows model domain original reference

def snapshot : Snapshot model domain original reference := ⟨rows model domain original reference,rfl⟩

variable (saved : Snapshot model domain original reference)
theorem every_source_row_iff (test : Row model domain original reference → Prop) :
    (∀ row ∈ saved.rows,test row) ↔
      if PublicDomain.quiet (code := model.source.code) then
        ∀ world ∈ Replanning.points model domain,test (Row.generate world none)
      else ∀ world ∈ Replanning.points model domain,
        ∀ table ∈ Cut.tables world.val.source world.val.entry world.val.cut,test (Row.generate world (some table)) := by
  rw [saved.original]
  unfold rows
  by_cases quiet : PublicDomain.quiet (code := model.source.code) = true
  · simp only [if_pos quiet]
    constructor
    · intro all world inside
      exact all _ (List.mem_map.mpr ⟨world,inside,rfl⟩)
    · intro all row inside
      obtain ⟨world,worldIncluded,rfl⟩ := List.mem_map.mp inside
      exact all world worldIncluded
  · simp only [if_neg quiet]
    constructor
    · intro all world inside table included
      exact all _ (List.mem_flatMap.mpr ⟨world,inside,List.mem_map.mpr ⟨table,included,rfl⟩⟩)
    · intro all row inside
      obtain ⟨world,worldIncluded,rowIncluded⟩ := List.mem_flatMap.mp inside
      obtain ⟨table,included,rfl⟩ := List.mem_map.mp rowIncluded
      exact all world worldIncluded table included

private def zero : Index model reference := ⟨0,by simp only [programmes,List.length_cons];omega⟩

def holds (row : Row model domain original reference) (index : Index model reference) : Prop :=
  let current := row.get index
  let prior := row.get (zero model reference)
  current.full.legal = true ∧ current.full.complete = true ∧ current.full.profile = prior.full.profile ∧
    current.inventory.NoWorse prior.inventory ∧
      ∀ axis ∈ economicAxes row.world.val.source row.world.val.cut,lookup current.values axis ≤ lookup prior.values axis
instance (row : Row model domain original reference) (index : Index model reference) :
    Decidable (holds model domain original reference row index) := by unfold holds;infer_instance

theorem holds_exact (row : Row model domain original reference) (index : Index model reference) :
    holds model domain original reference row index ↔
      Synthesis.accepts model.source.code (economicAxes row.world.val.source row.world.val.cut)
        (evaluation model original row.world.val row.table ((programmes model reference)[index.val]))
        (evaluation model original row.world.val row.table reference) := by
  have prior : (programmes model reference)[(zero model reference).val] = reference := rfl
  simp only [holds,Synthesis.accepts,Row.full_exact,Row.inventory_exact,prior,Authority.Trace.Lawful.NoWorse]
  constructor
  · rintro ⟨a,b,c,d,values⟩
    refine ⟨a,b,c,d,fun axis inside => ?_⟩
    have checked := values axis inside
    rw [Row.value_exact row index axis inside,Row.value_exact row (zero model reference) axis inside,prior] at checked
    exact checked
  · rintro ⟨a,b,c,d,values⟩
    refine ⟨a,b,c,d,fun axis inside => ?_⟩
    rw [Row.value_exact row index axis inside,Row.value_exact row (zero model reference) axis inside,prior]
    exact values axis inside

def accepted (index : Index model reference) : Prop := ∀ row ∈ saved.rows,holds model domain original reference row index
instance (index : Index model reference) : Decidable (accepted model domain original reference saved index) := by
  unfold accepted;infer_instance

theorem accepted_exact (index : Index model reference) :
    accepted model domain original reference saved index ↔
      Selection.acceptable model domain original reference ((programmes model reference)[index.val]) := by
  unfold accepted
  rw [every_source_row_iff]
  simp only [holds_exact]
  rw [←Selection.compactPacked_iff]
  unfold Selection.compactPacked Selection.packed
  split <;> rfl

/-- Dominance reads cached values and provenance keys, never the evaluator closure. -/
def below (row : Row model domain original reference) (current prior : Index model reference) : Prop :=
  (row.get current).inventory.due.Subperm (row.get prior).inventory.due ∧
    ∀ axis ∈ economicAxes row.world.val.source row.world.val.cut,
      lookup (row.get current).values axis ≤ lookup (row.get prior).values axis
instance (row : Row model domain original reference) (current prior : Index model reference) :
    Decidable (below model domain original reference row current prior) := by unfold below;infer_instance

theorem below_exact (row : Row model domain original reference) (current prior : Index model reference) :
    below model domain original reference row current prior ↔
      (Authority.Trace.Lawful.inventory (evaluation model original row.world.val row.table ((programmes model reference)[current.val])).native).due.Subperm
        (Authority.Trace.Lawful.inventory (evaluation model original row.world.val row.table ((programmes model reference)[prior.val])).native).due ∧
      ∀ axis ∈ economicAxes row.world.val.source row.world.val.cut,
        (evaluation model original row.world.val row.table ((programmes model reference)[current.val])).value axis ≤
          (evaluation model original row.world.val row.table ((programmes model reference)[prior.val])).value axis := by
  simp only [below,Row.inventory_exact]
  constructor
  · rintro ⟨native,values⟩
    refine ⟨native,fun axis inside => ?_⟩
    simpa only [Row.value_exact row current axis inside,Row.value_exact row prior axis inside] using values axis inside
  · rintro ⟨native,values⟩
    refine ⟨native,fun axis inside => ?_⟩
    simpa only [Row.value_exact row current axis inside,Row.value_exact row prior axis inside] using values axis inside

def noWorse (current prior : Index model reference) : Prop :=
  ∀ row ∈ saved.rows,below model domain original reference row current prior
instance (current prior : Index model reference) : Decidable (noWorse model domain original reference saved current prior) := by
  unfold noWorse;infer_instance

theorem noWorse_exact (current prior : Index model reference) :
    noWorse model domain original reference saved current prior ↔
      Distributed.NoWorse (Selection.axes (fuel := fuel) model domain) (Selection.benefit model domain original)
        ((programmes model reference)[current.val]) ((programmes model reference)[prior.val]) := by
  unfold noWorse
  rw [every_source_row_iff]
  simp only [below_exact]
  rw [←Review.noWorse_iff]
  unfold Review.noWorse Review.packedNoWorse
  split <;> rfl

def improves (prior current : Index model reference) : Prop :=
  noWorse model domain original reference saved current prior ∧ ¬ noWorse model domain original reference saved prior current
instance (prior current : Index model reference) : Decidable (improves model domain original reference saved prior current) := by
  unfold improves;infer_instance

theorem improves_exact (prior current : Index model reference) :
    improves model domain original reference saved prior current ↔
      Distributed.Improves (Selection.axes (fuel := fuel) model domain) (Selection.benefit model domain original)
        ((programmes model reference)[prior.val]) ((programmes model reference)[current.val]) := by
  simp only [improves,Distributed.Improves,noWorse_exact]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Review.Tensor
