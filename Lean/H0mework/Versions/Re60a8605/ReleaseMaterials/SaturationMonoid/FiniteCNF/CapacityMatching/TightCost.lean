import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CapacityMatching.Tight
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CapacityMatching.SourceCost

/-!
The ledger follows the original matching guard and each actual column probe.
It includes full matrix/output-copy and discarded-payload allowances. Computing
these counters and implementing addresses/allocation at bit level remain separate.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.TightCost

structure Execution (α : Type) extends SourceCost.Counted α where
  generations : Nat

def withoutRow {m r : Nat} (graph : Graph m r) (removed : Fin r) (i : Fin m) : SourceCost.Counted (Vector Bool r) :=
  ⟨Vector.ofFn (fun j => edge graph i j && decide (j ≠ removed)),6*r+1⟩

def without {m r : Nat} (graph : Graph m r) (removed : Fin r) : SourceCost.Counted (Graph m r) :=
  let rows := Vector.ofFn (withoutRow graph removed)
  ⟨rows.map SourceCost.Counted.value,(rows.toList.map SourceCost.Counted.cells).sum+2*m*r+2*m+2⟩

theorem without_value {m r : Nat} (graph : Graph m r) (removed : Fin r) :
    (without graph removed).value = Tight.without graph removed := by
  simp [without,withoutRow,Tight.without,Function.comp_def]

theorem without_cells {m r : Nat} (graph : Graph m r) (removed : Fin r) :
    (without graph removed).cells = 8*m*r+3*m+2 := by
  simp [without,withoutRow,Vector.toList_ofFn,List.map_ofFn,Function.comp_def]
  ring

def demandScan {m r : Nat} (graph : Graph m r) (j : Fin r) : List (Fin m) → SourceCost.Counted Bool
  | [] => ⟨false,1⟩
  | i::rest =>
      if edge graph i j then ⟨true,4⟩
      else let next := demandScan graph j rest; ⟨next.value,next.cells+4⟩

theorem demandScan_value {m r : Nat} (graph : Graph m r) (j : Fin r) (demands : List (Fin m)) :
    (demandScan graph j demands).value = demands.any (fun i => edge graph i j) := by
  induction demands with
  | nil => rfl
  | cons i rest ih => simp only [demandScan,List.any_cons]; split <;> simp_all

theorem demandScan_cells {m r : Nat} (graph : Graph m r) (j : Fin r) (demands : List (Fin m)) :
    (demandScan graph j demands).cells ≤ 4*demands.length+1 := by
  induction demands with
  | nil => rfl
  | cons i rest ih => simp only [demandScan,List.length_cons]; split <;> simp only <;> omega

def links {m r : Nat} (graph : Graph m r) (demands : List (Fin m)) :
    List (Fin r) → SourceCost.Counted (List (Fin r))
  | [] => ⟨[],1⟩
  | j::rest =>
      let found := demandScan graph j demands
      let tail := links graph demands rest
      ⟨if found.value then j::tail.value else tail.value,found.cells+tail.cells+4⟩

theorem links_value {m r : Nat} (graph : Graph m r) (demands : List (Fin m)) (groups : List (Fin r)) :
    (links graph demands groups).value = groups.filter (fun j => demands.any (fun i => edge graph i j)) := by
  induction groups with
  | nil => rfl
  | cons j rest ih => simp only [links,List.filter_cons,demandScan_value,ih]

theorem links_cells {m r : Nat} (graph : Graph m r) (demands : List (Fin m)) (groups : List (Fin r)) :
    (links graph demands groups).cells ≤ groups.length*(4*demands.length+5)+1 := by
  induction groups with
  | nil => simp [links]
  | cons j rest ih =>
      have head := demandScan_cells graph j demands
      simp only [links,List.length_cons]
      nlinarith

def neighborhood {m r : Nat} (graph : Graph m r) (demands : List (Fin m)) : SourceCost.Counted (List (Fin r)) :=
  let result := links graph demands (List.finRange r)
  ⟨result.value,result.cells+r+1⟩

theorem neighborhood_value {m r : Nat} (graph : Graph m r) (demands : List (Fin m)) :
    (neighborhood graph demands).value = neighbors graph demands := links_value graph demands _

theorem neighborhood_cells {m r : Nat} (graph : Graph m r) (demands : List (Fin m)) :
    (neighborhood graph demands).cells ≤ r*(4*demands.length+6)+2 := by
  have bound := links_cells graph demands (List.finRange r)
  simp only [List.length_finRange] at bound
  simp only [neighborhood]
  nlinarith

theorem neighborhood_length {m r : Nat} (graph : Graph m r) (demands : List (Fin m)) :
    (neighborhood graph demands).value.length ≤ r := by
  rw [neighborhood_value]
  exact (List.length_filter_le _ (List.finRange r)).trans_eq List.length_finRange

def restore {m r : Nat} (graph : Graph m r) (value : Cut m r) : SourceCost.Counted (Cut m r) :=
  let original := neighborhood graph value.demands
  ⟨⟨value.demands,original.value⟩,
    original.cells+2*value.demands.length+2*original.value.length+value.groups.length+3⟩

theorem restore_value {m r : Nat} (graph : Graph m r) (value : Cut m r) :
    (restore graph value).value = Tight.restore graph value := by
  simp only [restore,neighborhood_value,Tight.restore]

theorem restore_cells {m r : Nat} (graph : Graph m r) (value : Cut m r) :
    (restore graph value).cells ≤ r*(4*value.demands.length+8)+2*value.demands.length+value.groups.length+5 := by
  have scan := neighborhood_cells graph value.demands
  have size := neighborhood_length graph value.demands
  simp only [restore]
  nlinarith

def generateBudget (m r : Nat) : Nat := (m+1)*solveUnits m r+r+1

def probeBudget (m r : Nat) : Nat :=
  (8*m*r+3*m+2)+generateBudget m r+(m*r+m+2)+
    (r*(4*m+8)+2*m+r+5)+2*r+3

def probe {m r : Nat} (graph : Graph m r) (removed : Fin r) : Execution (Option (Cut m r)) :=
  let deleted := without graph removed
  let attempt := generate deleted.value
  let used := deleted.cells+attempt.visits+m*r+m+2
  match attempt.answer with
  | .matched _ => { value := none, cells := used+2*r+3, generations := 1 }
  | .deficient value =>
      let original := restore graph value
      { value := some original.value, cells := used+original.cells+3, generations := 1 }

theorem probe_value {m r : Nat} (graph : Graph m r) (removed : Fin r) :
    (probe graph removed).value = Tight.probe graph removed := by
  simp only [probe,without_value,Tight.probe]
  cases (generate (Tight.without graph removed)).answer <;> simp [restore_value]

theorem probe_generations {m r : Nat} (graph : Graph m r) (removed : Fin r) :
    (probe graph removed).generations = 1 := by
  cases produced : (generate (without graph removed).value).answer <;> simp [probe,produced]

def cutCells {m r : Nat} (value : Cut m r) : Nat := value.demands.length+value.groups.length+2

theorem deficient_sizes {m r : Nat} (graph : Graph m r) (value : Cut m r)
    (produced : (generate graph).answer = .deficient value) : value.demands.length ≤ m ∧ value.groups.length ≤ r := by
  have correct := generate_correct graph
  rw [produced] at correct
  constructor
  · simpa only [Fintype.card_fin] using correct.1.length_le_card
  · rw [correct.2.1]
    exact (List.length_filter_le _ (List.finRange r)).trans_eq List.length_finRange

theorem probe_cells {m r : Nat} (graph : Graph m r) (removed : Fin r) :
    (probe graph removed).cells ≤ probeBudget m r := by
  have iteration := generate_visits (without graph removed).value
  cases produced : (generate (without graph removed).value).answer with
  | matched table =>
      simp only [probe,produced,without_cells]
      unfold probeBudget generateBudget
      omega
  | deficient value =>
      obtain ⟨demands,groups⟩ := deficient_sizes (without graph removed).value value produced
      have restoring := restore_cells graph value
      have smaller : (restore graph value).cells ≤ r*(4*m+8)+2*m+r+5 := by
        apply restoring.trans
        gcongr
      simp only [probe,produced,without_cells]
      unfold probeBudget generateBudget
      omega

theorem probe_size {m r : Nat} (graph : Graph m r) (removed : Fin r) (value : Cut m r)
    (found : (probe graph removed).value = some value) : cutCells value ≤ m+r+2 := by
  cases produced : (generate (without graph removed).value).answer with
  | matched table => simp [probe,produced] at found
  | deficient previous =>
      have same : (restore graph previous).value = value := by simpa only [probe,produced,Option.some.injEq] using found
      subst value
      have demands := (deficient_sizes (without graph removed).value previous produced).1
      have groups := neighborhood_length graph previous.demands
      simp only [restore,cutCells]
      omega

def listCells {m r : Nat} (values : List (Cut m r)) : Nat := (values.map cutCells).sum

@[simp] theorem listCells_nil (m r : Nat) : listCells ([] : List (Cut m r)) = 0 := rfl
@[simp] theorem listCells_cons {m r : Nat} (value : Cut m r) (values : List (Cut m r)) :
    listCells (value::values) = cutCells value+listCells values := rfl

def probes {m r : Nat} (graph : Graph m r) : List (Fin r) → Execution (List (Cut m r))
  | [] => { value := [], cells := 1, generations := 0 }
  | removed::rest =>
      let first := probe graph removed
      let tail := probes graph rest
      let used := first.cells+tail.cells+2*listCells tail.value+4
      match first.value with
      | none => { value := tail.value, cells := used, generations := first.generations+tail.generations }
      | some value =>
          { value := value::tail.value, cells := used+2*cutCells value+2,
            generations := first.generations+tail.generations }

theorem probes_value {m r : Nat} (graph : Graph m r) (indices : List (Fin r)) :
    (probes graph indices).value = indices.filterMap (Tight.probe graph) := by
  induction indices with
  | nil => rfl
  | cons removed rest ih =>
      rw [List.filterMap_cons,← probe_value]
      cases found : (probe graph removed).value <;> simp [probes,found,ih]

theorem probes_generations {m r : Nat} (graph : Graph m r) (indices : List (Fin r)) :
    (probes graph indices).generations = indices.length := by
  induction indices with
  | nil => rfl
  | cons removed rest ih =>
      cases found : (probe graph removed).value <;> simp [probes,found,probe_generations,ih,Nat.add_comm]

theorem probes_storage {m r : Nat} (graph : Graph m r) (indices : List (Fin r)) :
    listCells (probes graph indices).value ≤ indices.length*(m+r+2) := by
  induction indices with
  | nil => simp [probes]
  | cons removed rest ih =>
      cases found : (probe graph removed).value with
      | none => simp only [probes,found,List.length_cons]; nlinarith
      | some value =>
          have head := probe_size graph removed value found
          simp only [probes,found,listCells_cons,List.length_cons]
          nlinarith

theorem probes_length {m r : Nat} (graph : Graph m r) (indices : List (Fin r)) :
    (probes graph indices).value.length ≤ indices.length := by
  rw [probes_value]
  exact List.length_filterMap_le _ _

theorem probes_cells {m r : Nat} (graph : Graph m r) (indices : List (Fin r)) :
    (probes graph indices).cells ≤ indices.length*(probeBudget m r+2*(indices.length+1)*(m+r+2)+6)+1 := by
  induction indices with
  | nil => simp [probes]
  | cons removed rest ih =>
      have first := probe_cells graph removed
      have stored := probes_storage graph rest
      cases found : (probe graph removed).value with
      | none =>
          simp only [probes,found,List.length_cons]
          nlinarith [Nat.zero_le (rest.length*(m+r+2))]
      | some value =>
          have head := probe_size graph removed value found
          simp only [probes,found,List.length_cons]
          nlinarith [Nat.zero_le (rest.length*(m+r+2))]

def run {m r : Nat} (graph : Graph m r) : Execution (List (Cut m r)) :=
  let original := generate graph
  match original.answer with
  | .deficient value => { value := [], cells := original.visits+2*cutCells value+3, generations := 1 }
  | .matched _ =>
      let all := probes graph (List.finRange r)
      { value := all.value, cells := original.visits+all.cells+3*r+3, generations := 1+all.generations }

theorem run_value {m r : Nat} (graph : Graph m r) : (run graph).value = Tight.run graph := by
  cases produced : (generate graph).answer <;> simp [run,Tight.run,produced,probes_value]

theorem run_generations {m r : Nat} (graph : Graph m r) : (run graph).generations ≤ r+1 := by
  cases produced : (generate graph).answer <;> simp [run,produced,probes_generations,Nat.add_comm]

theorem run_storage {m r : Nat} (graph : Graph m r) : listCells (run graph).value ≤ r*(m+r+2) := by
  have bound := probes_storage graph (List.finRange r)
  cases produced : (generate graph).answer <;> simp_all [run]

theorem run_length {m r : Nat} (graph : Graph m r) : (run graph).value.length ≤ r := by
  rw [run_value]
  exact Tight.run_length graph

def runBudget (m r : Nat) : Nat :=
  generateBudget m r+r*(probeBudget m r+2*(r+1)*(m+r+2)+6)+2*m+4*r+8

theorem run_cells {m r : Nat} (graph : Graph m r) : (run graph).cells ≤ runBudget m r := by
  have first := generate_visits graph
  have all := probes_cells graph (List.finRange r)
  simp only [List.length_finRange] at all
  cases produced : (generate graph).answer with
  | matched table =>
      simp only [run,produced]
      unfold runBudget generateBudget
      omega
  | deficient value =>
      obtain ⟨demands,groups⟩ := deficient_sizes graph value produced
      simp only [run,produced,cutCells]
      unfold runBudget generateBudget
      omega

theorem run_correct {m r : Nat} (graph : Graph m r) (value : Cut m r) (member : value ∈ (run graph).value) :
    Tight.Correct graph value := by
  rw [run_value] at member
  exact Tight.run_correct graph value member

end SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.TightCost
