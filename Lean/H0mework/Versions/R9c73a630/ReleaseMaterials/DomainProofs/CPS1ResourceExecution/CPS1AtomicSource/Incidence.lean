import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Material

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CPS1AtomicSource.Incidence
open CPS1ResourceExecution CPS1LocalChemicalExecution.PeptideMaterial

theorem indicator_sum {α : Type} (rows : List α) (p : α → Bool) :
    (rows.map (fun row => if p row then 1 else 0)).sum = rows.countP p := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons,List.sum_cons,List.countP_cons,ih,Nat.add_comm]

theorem range_membership_count (size : Nat) (edges : List Nat) (unique : edges.Nodup)
    (bounded : ∀ edge ∈ edges, edge < size) :
    (List.range size).countP (fun edge => edge ∈ edges) = edges.length := by
  rw [List.countP_eq_length_filter]
  have perm : ((List.range size).filter (fun edge => edge ∈ edges)).Perm edges := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_range (n := size)).filter _) unique).mpr
    intro edge
    simp only [List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨And.right,fun member => ⟨bounded edge member,member⟩⟩
  exact perm.length_eq

theorem outgoing_count (word : List AA) (edges : List Nat) (unique : edges.Nodup)
    (bounded : ∀ edge ∈ edges, edge < word.length) :
    Material.rowOutgoing edges word.zipIdx .H = edges.length ∧
    Material.rowOutgoing edges word.zipIdx .O = edges.length := by
  have mapping : word.zipIdx.map (fun row => if (row.2 ∈ edges : Bool) then 1 else 0) =
      (List.range word.length).map (fun edge => if (edge ∈ edges : Bool) then 1 else 0) := by
    simpa only [List.map_map,Function.comp_def,← List.range_eq_range'] using
      congrArg (List.map (fun edge => if (edge ∈ edges : Bool) then 1 else 0)) (List.zipIdx_map_snd 0 word)
  have count := range_membership_count word.length edges unique bounded
  constructor <;> simpa only [Material.rowOutgoing,Material.outgoing,mapping,
    Bool.or_true,Bool.true_or,Bool.and_true,beq_self_eq_true,indicator_sum] using count

theorem incoming_membership (edges : List Nat) (address : Nat) :
    (0 < address ∧ address-1 ∈ edges) ↔ address ∈ edges.map Nat.succ := by
  cases address with
  | zero => simp
  | succ address => simp

theorem incoming_count (word : List AA) (edges : List Nat) (unique : edges.Nodup)
    (bounded : ∀ edge ∈ edges, edge+1 < word.length) :
    Material.rowIncoming edges word.zipIdx .H = edges.length := by
  have successorUnique : (edges.map Nat.succ).Nodup := unique.map (fun _ _ same => Nat.succ.inj same)
  have successorBounded : ∀ address ∈ edges.map Nat.succ, address < word.length := by
    intro address inSuccessors
    rcases List.mem_map.mp inSuccessors with ⟨edge,member,equality⟩
    rw [← equality]
    exact bounded edge member
  have predicates : (fun row : AA × Nat => Material.incoming edges row) =
      (fun row : AA × Nat => decide (row.2 ∈ edges.map Nat.succ)) := by
    funext row
    apply Bool.eq_iff_iff.mpr
    simp only [Material.incoming,Bool.and_eq_true,decide_eq_true_eq,incoming_membership]
  have mapping : word.zipIdx.map (fun row => if (row.2 ∈ edges.map Nat.succ : Bool) then 1 else 0) =
      (List.range word.length).map (fun address => if (address ∈ edges.map Nat.succ : Bool) then 1 else 0) := by
    simpa only [List.map_map,Function.comp_def,← List.range_eq_range'] using
      congrArg (List.map (fun address => if (address ∈ edges.map Nat.succ : Bool) then 1 else 0)) (List.zipIdx_map_snd 0 word)
  have count := range_membership_count word.length (edges.map Nat.succ) successorUnique successorBounded
  simp only [Material.rowIncoming,beq_self_eq_true,Bool.and_true,predicates]
  rw [mapping,indicator_sum]
  simpa only [List.length_map] using count

theorem row_full (word : List AA) (element : Element) :
    Material.rowFull word.zipIdx element =
      (word.map (fun aa => freeAtoms aa element)).sum +
        (if element = .H then Graph.requiredProtons word else 0) := by
  have sum (rows : List (AA × Nat)) : Material.rowFull rows element =
      (rows.map (fun row => freeAtoms row.1 element)).sum +
        (if element = .H then (rows.map (fun row => Primary.additionalProtons row.1)).sum else 0) := by
    induction rows with
    | nil => simp [Material.rowFull]
    | cons row rest ih =>
      by_cases hydrogen : element = .H <;>
        simp only [Material.rowFull,List.map_cons,List.sum_cons,hydrogen,if_true,if_false] at ih ⊢ <;> omega
  have rawFree : word.zipIdx.map (fun row => freeAtoms row.1 element) = word.map (fun aa => freeAtoms aa element) := by
    simpa only [List.map_map,Function.comp_def] using
      congrArg (List.map (fun aa => freeAtoms aa element)) (List.zipIdx_map_fst 0 word)
  have rawQ : word.zipIdx.map (fun row => Primary.additionalProtons row.1) = word.map Primary.additionalProtons := by
    simpa only [List.map_map,Function.comp_def] using
      congrArg (List.map Primary.additionalProtons) (List.zipIdx_map_fst 0 word)
  simpa only [rawFree,rawQ,Graph.requiredProtons] using sum word.zipIdx

theorem incoming_element (edges : List Nat) (rows : List (AA × Nat)) (element : Element) :
    Material.rowIncoming edges rows element = if element = .H then Material.rowIncoming edges rows .H else 0 := by
  cases element <;> simp [Material.rowIncoming]

theorem outgoing_element (edges : List Nat) (rows : List (AA × Nat)) (element : Element) :
    Material.rowOutgoing edges rows element =
      if element = .H ∨ element = .O then Material.rowOutgoing edges rows .H else 0 := by
  cases element <;> simp [Material.rowOutgoing]

theorem whole_material (word : List AA) (remaining : List Nat) (unique : remaining.Nodup)
    (element : Element) :
    let edges := remaining.filter (fun edge => edge+1 < word.length)
    (Graph.atoms (Graph.build Primary.template word remaining) element : Int) +
      (edges.length : Int) * (waterAtoms element : Int) =
      freeWordAtoms word element + (if element = .H then (Graph.requiredProtons word : Int) else 0) := by
  let edges := remaining.filter (fun edge => edge+1 < word.length)
  have edgeUnique := unique.filter (fun edge => edge+1 < word.length)
  have bounded : ∀ edge ∈ edges, edge+1 < word.length := by
    intro edge member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  have incoming := incoming_count word edges edgeUnique bounded
  have outgoing := (outgoing_count word edges edgeUnique (fun edge member => Nat.lt_of_succ_lt (bounded edge member))).1
  have balance := Material.build_count_balance word remaining element
  dsimp only at balance
  rw [incoming_element,outgoing_element,incoming,outgoing,row_full] at balance
  dsimp only
  have integer := congrArg (fun n : Nat => (n : Int)) balance
  simp only [Nat.cast_add,freeWordAtoms] at integer ⊢
  cases element <;> simp [waterAtoms,edges] at integer ⊢ <;> omega

theorem processed_material (word : List AA) (remaining : List Nat) (cuts : Nat)
    (unique : remaining.Nodup) (bounded : ∀ edge ∈ remaining, edge+1 < word.length)
    (partition : remaining.length + cuts = bondCount word) (element : Element) :
    (Graph.atoms (Graph.build Primary.template word remaining) element : Int) =
      wordAtoms word cuts element + (if element = .H then (Graph.requiredProtons word : Int) else 0) := by
  have allEdges : remaining.filter (fun edge => edge+1 < word.length) = remaining := by
    apply List.filter_eq_self.mpr
    intro edge member
    exact decide_eq_true (bounded edge member)
  have paid := whole_material word remaining unique element
  dsimp only at paid
  rw [allEdges] at paid
  have integerPartition := congrArg (fun n : Nat => (n : Int)) partition
  simp only [Nat.cast_add] at integerPartition
  cases element <;> simp [wordAtoms,waterAtoms,bondCount] at paid integerPartition ⊢ <;> omega

end CPS1AtomicSource.Incidence
