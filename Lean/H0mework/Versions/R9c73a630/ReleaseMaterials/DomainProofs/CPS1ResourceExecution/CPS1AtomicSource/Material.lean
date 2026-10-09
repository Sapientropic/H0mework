import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Graph
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.PrimaryFacts

set_option autoImplicit false
set_option maxHeartbeats 0

namespace CPS1AtomicSource.Material
open CPS1ResourceExecution CPS1LocalChemicalExecution.PeptideMaterial
open Primary

def keepTerminal (incoming outgoing : Bool) (atom : Primary.Atom) : Bool :=
  match atom.terminalLeave with
  | .none => true
  | .amino => !incoming
  | .carboxyl => !outgoing

theorem terminal_count_partition (atoms : List Primary.Atom) (element : Element)
    (incoming outgoing : Bool) :
    Primary.atomCount (atoms.filter (keepTerminal incoming outgoing)) element +
      (if incoming then Primary.atomCount (atoms.filter (fun atom => atom.terminalLeave == .amino)) element else 0) +
      (if outgoing then Primary.atomCount (atoms.filter (fun atom => atom.terminalLeave == .carboxyl)) element else 0) =
    Primary.atomCount atoms element := by
  induction atoms with
  | nil => simp [Primary.atomCount]
  | cons atom rest ih =>
    cases leave : atom.terminalLeave <;> cases incoming <;> cases outgoing <;>
      by_cases same : atom.element = element <;>
      simp [Primary.atomCount,keepTerminal,leave,same] at ih ⊢ <;> omega

theorem residue_count (aa : AA) (element : Element) (incoming outgoing : Bool) :
    Primary.atomCount ((Primary.template aa).atoms.filter (keepTerminal incoming outgoing)) element +
      (if incoming && element == .H then 1 else 0) +
      (if outgoing && (element == .H || element == .O) then 1 else 0) =
    freeAtoms aa element + (if element = .H then Primary.additionalProtons aa else 0) := by
  have partition := terminal_count_partition (Primary.template aa).atoms element incoming outgoing
  have amino : Primary.atomCount ((Primary.template aa).atoms.filter (fun atom => atom.terminalLeave == .amino)) element =
      (if element = .H then 1 else 0) := (Primary.original_ends aa element).1
  have carboxyl : Primary.atomCount ((Primary.template aa).atoms.filter (fun atom => atom.terminalLeave == .carboxyl)) element =
      (if element = .H ∨ element = .O then 1 else 0) := (Primary.original_ends aa element).2
  rw [amino,carboxyl,Primary.original_formula] at partition
  cases incoming <;> cases outgoing <;> cases element <;> exact partition

def charge (atoms : List Primary.Atom) : Int := (atoms.map Primary.Atom.charge).sum

theorem terminal_charge_partition (atoms : List Primary.Atom) (incoming outgoing : Bool) :
    charge (atoms.filter (keepTerminal incoming outgoing)) +
      (if incoming then charge (atoms.filter (fun atom => atom.terminalLeave == .amino)) else 0) +
      (if outgoing then charge (atoms.filter (fun atom => atom.terminalLeave == .carboxyl)) else 0) =
    charge atoms := by
  induction atoms with
  | nil => simp [charge]
  | cons atom rest ih =>
    cases leave : atom.terminalLeave <;> cases incoming <;> cases outgoing <;>
      simp [charge,keepTerminal,leave] at ih ⊢ <;> omega

theorem residue_charge (aa : AA) (incoming outgoing : Bool) :
    charge ((Primary.template aa).atoms.filter (keepTerminal incoming outgoing)) =
      (Primary.additionalProtons aa : Int) := by
  have partition := terminal_charge_partition (Primary.template aa).atoms incoming outgoing
  have amino : charge ((Primary.template aa).atoms.filter (fun atom => atom.terminalLeave == .amino)) = 0 :=
    (Primary.original_end_charge aa).1
  have carboxyl : charge ((Primary.template aa).atoms.filter (fun atom => atom.terminalLeave == .carboxyl)) = 0 :=
    (Primary.original_end_charge aa).2
  rw [amino,carboxyl] at partition
  simp only [ite_self,Int.add_zero] at partition
  exact partition.trans (Primary.original_charge aa)

def incoming (edges : List Nat) (row : AA × Nat) : Bool := 0 < row.2 && row.2-1 ∈ edges
def outgoing (edges : List Nat) (row : AA × Nat) : Bool := row.2 ∈ edges

theorem source_survives (edges : List Nat) (row : AA × Nat) (atom : Primary.Atom) :
    Graph.survives edges row.2 atom = keepTerminal (incoming edges row) (outgoing edges row) atom := by
  cases leave : atom.terminalLeave <;> rfl

def rowAtoms (edges : List Nat) (rows : List (AA × Nat)) (element : Element) : Nat :=
  ((rows.flatMap (Graph.residueAtoms Primary.template edges)).map
    (fun atom => if atom.source.element = element then 1 else 0)).sum

def rowIncoming (edges : List Nat) (rows : List (AA × Nat)) (element : Element) : Nat :=
  (rows.map (fun row => if incoming edges row && element == .H then 1 else 0)).sum

def rowOutgoing (edges : List Nat) (rows : List (AA × Nat)) (element : Element) : Nat :=
  (rows.map (fun row => if outgoing edges row && (element == .H || element == .O) then 1 else 0)).sum

def rowFull (rows : List (AA × Nat)) (element : Element) : Nat :=
  (rows.map (fun row => freeAtoms row.1 element + if element = .H then Primary.additionalProtons row.1 else 0)).sum

theorem actual_row_atoms (edges : List Nat) (row : AA × Nat) (element : Element) :
    rowAtoms edges [row] element = Primary.atomCount
      ((Primary.template row.1).atoms.filter (keepTerminal (incoming edges row) (outgoing edges row))) element := by
  simp only [rowAtoms,List.flatMap_cons,List.flatMap_nil,List.append_nil,Graph.residueAtoms,List.map_map]
  have keep : Graph.survives edges row.2 = keepTerminal (incoming edges row) (outgoing edges row) :=
    funext (source_survives edges row)
  rw [keep]
  rfl

theorem rows_count_balance (edges : List Nat) (rows : List (AA × Nat)) (element : Element) :
    rowAtoms edges rows element + rowIncoming edges rows element + rowOutgoing edges rows element = rowFull rows element := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have rowBalance := residue_count row.1 element (incoming edges row) (outgoing edges row)
    rw [← actual_row_atoms] at rowBalance
    simp only [rowAtoms,List.flatMap_cons,List.flatMap_nil,List.map_nil,List.sum_nil,List.map_append,List.sum_append,rowIncoming,rowOutgoing,rowFull,
      List.map_cons,List.sum_cons] at ih rowBalance ⊢
    omega

theorem build_count_balance (word : List AA) (remaining : List Nat) (element : Element) :
    let edges := remaining.filter (fun edge => edge+1 < word.length)
    Graph.atoms (Graph.build Primary.template word remaining) element +
      rowIncoming edges word.zipIdx element + rowOutgoing edges word.zipIdx element = rowFull word.zipIdx element :=
  rows_count_balance _ _ _

theorem actual_residue_charge (edges : List Nat) (row : AA × Nat) :
    ((Graph.residueAtoms Primary.template edges row).map (fun atom => atom.source.charge)).sum =
      (Primary.additionalProtons row.1 : Int) := by
  simp only [Graph.residueAtoms,List.map_map]
  have keep : Graph.survives edges row.2 = keepTerminal (incoming edges row) (outgoing edges row) :=
    funext (source_survives edges row)
  rw [keep]
  exact residue_charge _ _ _

theorem rows_charge (edges : List Nat) (rows : List (AA × Nat)) :
    ((rows.flatMap (Graph.residueAtoms Primary.template edges)).map (fun atom => atom.source.charge)).sum =
      ((rows.map (fun row => Primary.additionalProtons row.1)).sum : Int) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
      Nat.cast_add,actual_residue_charge,ih]

theorem build_charge (word : List AA) (remaining : List Nat) :
    Graph.charge (Graph.build Primary.template word remaining) = (Graph.requiredProtons word : Int) := by
  have paid := rows_charge (remaining.filter (fun edge => edge+1 < word.length)) word.zipIdx
  have same : word.zipIdx.map (fun row => Primary.additionalProtons row.1) = word.map Primary.additionalProtons := by
    simpa only [List.map_map,Function.comp_def] using
      congrArg (List.map Primary.additionalProtons) (List.zipIdx_map_fst 0 word)
  simpa only [Graph.charge,Graph.build,same,Graph.requiredProtons] using paid

end CPS1AtomicSource.Material
