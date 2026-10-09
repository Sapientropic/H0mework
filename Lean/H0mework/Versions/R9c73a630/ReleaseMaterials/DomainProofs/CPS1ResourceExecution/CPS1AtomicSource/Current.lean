import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Graph
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Incidence
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EditingChemicalJoin.Contract

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1AtomicSource.Current
open CPS1ResourceExecution
open CPS1LocalChemicalExecution

def ChainValid (frame : CPS1Recycling.Frame) (chain : Chain frame) : Prop :=
  chain.bonds.Nodup ∧
  (∀ edge ∈ chain.bonds, edge < (Actual.cps1 frame).2.length) ∧
  chain.bonds.length + chain.hydrolysed.length = (Actual.cps1 frame).2.length

theorem initial_valid (frame : CPS1Recycling.Frame) : ChainValid frame (Chain.initial frame) := by
  exact ⟨List.nodup_range,fun _ member => List.mem_range.mp member,by simp [Chain.initial]⟩

theorem cleave_valid (frame : CPS1Recycling.Frame) (chain : Chain frame) (valid : ChainValid frame chain)
    (edge : Nat) (present : edge ∈ chain.bonds) : ChainValid frame (chain.cleave frame edge) := by
  refine ⟨valid.1.erase _,?_,?_⟩
  · intro other member
    exact valid.2.1 other (List.mem_of_mem_erase member)
  · have length := List.length_erase_of_mem present
    have positive : 0 < chain.bonds.length := List.length_pos_of_mem present
    have partition := valid.2.2
    simp only [Chain.cleave,List.length_cons]
    omega

theorem report_valid (frame : CPS1Recycling.Frame) (chain : Chain frame) (valid : ChainValid frame chain)
    (address : Nat) (r p : Vec) : ChainValid frame (chain.report frame address r p) := valid

theorem inertia_valid (frame : CPS1Recycling.Frame) (chain : Chain frame) (valid : ChainValid frame chain)
    (address : Nat) (mass : ℚ) : ChainValid frame (chain.recordInertia frame address mass) := valid

/-- The atomic carrier keeps the same peptide/bond source. Its graph is the fixed
CCD restriction computed below, rather than a caller-supplied graph or pose. -/
inductive Species (frame : CPS1Recycling.Frame)
  | retained (old : CPS1LocalChemicalExecution.Species frame)
  | atomic (source : Chain frame)
  | missingChain
  deriving DecidableEq

abbrev Stock (frame : CPS1Recycling.Frame) := List (Species frame)

def graph (frame : CPS1Recycling.Frame) (chain : Chain frame) : Graph.Molecule := Graph.fromChain frame chain

def proton (frame : CPS1Recycling.Frame) : Species frame := .retained (molecule frame .proton)

def protonDebt (frame : CPS1Recycling.Frame) : Nat :=
  Graph.requiredProtons (Actual.cps1 frame).word

inductive Reaction (frame : CPS1Recycling.Frame)
  | atomize (source : Chain frame)
  | requireChain
  deriving DecidableEq

def Reaction.reactants (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .atomize source => .retained (.chain source) :: List.replicate (protonDebt frame) (proton frame)
  | .requireChain => [.missingChain]

def Reaction.products (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .atomize source => [.atomic source]
  | .requireChain => []

abbrev Execution (frame : CPS1Recycling.Frame) := Inventory.Execution (Species frame) (Reaction frame)

def execute (frame : CPS1Recycling.Frame) (program : List (Reaction frame)) (stock : Stock frame) : Execution frame :=
  Inventory.execute (Reaction.reactants frame) (Reaction.products frame) program stock

structure Occurrence (frame : CPS1Recycling.Frame) where
  previous : CPS1EditingChemicalJoin.Source.Occurrence frame
  source : Option (Chain frame)
  current : Execution frame

def fromActual (frame : CPS1Recycling.Frame) (previous : CPS1EditingChemicalJoin.Source.Occurrence frame) :
    Occurrence frame :=
  let source := CPS1LocalChemicalExecution.Source.heldChain frame previous.current.stock
  let stock := previous.current.stock.map Species.retained
  let program := match source with | none => [.requireChain] | some chain => [.atomize chain]
  ⟨previous,source,execute frame program stock⟩

def sourceExecution
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction) (feed : List CPS1EditingChemicalJoin.Source.RawMaterial) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← CPS1EditingChemicalJoin.Source.execution edits water additional path
    recycleFeed scanFeed bodyFeed depth actions feed
  pure ⟨previous.1,fromActual previous.1 previous.2⟩

def execution
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) :=
  sourceExecution edits water additional path recycleFeed scanFeed bodyFeed depth [] CPS1EditingChemicalJoin.Source.rawFuel

theorem reserve_repeated (frame : CPS1Recycling.Frame) (amount : Nat) (stock : Stock frame)
    (enough : amount ≤ stock.count (proton frame)) :
    ∃ surplus, stock.Perm (List.replicate amount (proton frame) ++ surplus) := by
  induction amount generalizing stock with
  | zero => exact ⟨stock,List.Perm.refl stock⟩
  | succ amount ih =>
    have positive : 0 < stock.count (proton frame) := by omega
    have present := List.count_pos_iff.mp positive
    have remaining : amount ≤ (stock.erase (proton frame)).count (proton frame) := by
      rw [List.count_erase_self]
      omega
    rcases ih _ remaining with ⟨surplus,paid⟩
    refine ⟨surplus,?_⟩
    simpa only [List.replicate_succ,List.cons_append] using (List.perm_cons_erase present).trans (paid.cons _)

theorem held_chain_member (frame : CPS1Recycling.Frame) (stock : CPS1LocalChemicalExecution.Stock frame)
    (chain : Chain frame) (held : CPS1LocalChemicalExecution.Source.heldChain frame stock = some chain) :
    CPS1LocalChemicalExecution.Species.chain chain ∈ stock := by
  induction stock with
  | nil => cases held
  | cons species rest ih =>
    cases species <;> first
    | exact List.mem_cons_of_mem _ (ih held)
    | exact List.mem_cons_self
    | simp only [CPS1LocalChemicalExecution.Source.heldChain,Option.some.injEq] at held
      cases held
      exact List.mem_cons_self


def advance (frame : CPS1Recycling.Frame) (current : Occurrence frame) : Occurrence frame :=
  {current with current := execute frame current.current.remaining current.current.stock}

theorem atomize_paid (frame : CPS1Recycling.Frame) (source : Chain frame) (surplus stock : Stock frame)
    (inventory : stock.Perm ((Reaction.atomize source).reactants frame ++ surplus)) :
    let result := execute frame [.atomize source] stock
    result.fired = [.atomize source] ∧ result.remaining = [] ∧ result.missing = none ∧
    result.stock.Perm (.atomic source :: surplus) := by
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame) (.atomize source)
    surplus stock inventory with ⟨next,paid,generated⟩
  dsimp only
  simp only [execute,Inventory.execute,paid]
  exact ⟨True.intro,True.intro,True.intro,generated⟩

theorem advance_retains_source (frame : CPS1Recycling.Frame) (current : Occurrence frame) :
    (advance frame current).previous = current.previous ∧ (advance frame current).source = current.source := ⟨rfl,rfl⟩

theorem atomize_from_current (frame : CPS1Recycling.Frame)
    (previous : CPS1EditingChemicalJoin.Source.Occurrence frame) (source : Chain frame)
    (held : CPS1LocalChemicalExecution.Source.heldChain frame previous.current.stock = some source)
    (surplus : Stock frame)
    (inventory : (previous.current.stock.map Species.retained).Perm
      ((Reaction.atomize source).reactants frame ++ surplus)) :
    (fromActual frame previous).source = some source ∧
    (fromActual frame previous).current.fired = [.atomize source] ∧
    (fromActual frame previous).current.remaining = [] ∧ (fromActual frame previous).current.missing = none ∧
    (fromActual frame previous).current.stock.Perm (.atomic source :: surplus) := by
  have paid := atomize_paid frame source surplus _ inventory
  simp only [fromActual,held]
  exact ⟨True.intro,paid⟩

theorem source_proton_payment (frame : CPS1Recycling.Frame)
    (previous : CPS1EditingChemicalJoin.Source.Occurrence frame) (chain : Chain frame)
    (held : CPS1LocalChemicalExecution.Source.heldChain frame previous.current.stock = some chain)
    (enough : protonDebt frame ≤ (previous.current.stock.map Species.retained).count (proton frame)) :
    ∃ surplus, (fromActual frame previous).current.fired = [.atomize chain] ∧
      (fromActual frame previous).current.remaining = [] ∧
      (fromActual frame previous).current.missing = none ∧
      (fromActual frame previous).current.stock.Perm (.atomic chain :: surplus) ∧
      (previous.current.stock.map Species.retained).Perm
        (.retained (.chain chain) :: List.replicate (protonDebt frame) (proton frame) ++ surplus) := by
  have member := held_chain_member frame _ chain held
  have mapped : Species.retained (.chain chain) ∈ previous.current.stock.map Species.retained :=
    List.mem_map.mpr ⟨_,member,rfl⟩
  have distinct : Species.retained (.chain chain) ≠ proton frame := by simp [proton,molecule]
  have remaining : protonDebt frame ≤
      ((previous.current.stock.map Species.retained).erase (.retained (.chain chain))).count (proton frame) := by
    simpa only [List.count_erase_of_ne distinct.symm] using enough
  rcases reserve_repeated frame (protonDebt frame) _ remaining with ⟨surplus,paid⟩
  have inventory := (List.perm_cons_erase mapped).trans (paid.cons _)
  have result := atomize_from_current frame previous chain held surplus inventory
  exact ⟨surplus,result.2.1,result.2.2.1,result.2.2.2.1,result.2.2.2.2,inventory⟩

theorem atomic_inventory_balance (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (species : Species frame) :
    let result := execute frame program stock
    stock.count species + (Inventory.credit (Reaction.products frame) result.fired).count species =
      result.stock.count species + (Inventory.debit (Reaction.reactants frame) result.fired).count species :=
  Inventory.execution_balance (Reaction.reactants frame) (Reaction.products frame) program stock species

theorem atomic_cut (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (missing : Species frame)
    (cut : (execute frame program stock).missing = some missing) :
    ∃ reaction rest, (execute frame program stock).remaining = reaction :: rest ∧
      (execute frame program stock).stock.count missing < (reaction.reactants frame).count missing :=
  Inventory.execution_cut (Reaction.reactants frame) (Reaction.products frame) program stock missing cut

theorem chain_material (frame : CPS1Recycling.Frame) (chain : Chain frame) (valid : ChainValid frame chain)
    (element : PeptideMaterial.Element) :
    (Graph.atoms (graph frame chain) element : Int) = chain.atoms frame element +
      (if element = .H then (protonDebt frame : Int) else 0) := by
  apply Incidence.processed_material (Actual.cps1 frame).word chain.bonds chain.hydrolysed.length valid.1
  · intro edge member
    have bound := valid.2.1 edge member
    simpa only [Peptide.word,List.length_cons] using Nat.succ_lt_succ bound
  · simpa only [PeptideMaterial.bondCount,Peptide.word,List.length_cons,Nat.add_sub_cancel] using valid.2.2

theorem chain_charge (frame : CPS1Recycling.Frame) (chain : Chain frame) :
    Graph.charge (graph frame chain) = (protonDebt frame : Int) := Material.build_charge _ _

theorem chain_no_dangling (frame : CPS1Recycling.Frame) (chain : Chain frame) :
    Graph.dangling (graph frame chain) = [] := Graph.no_dangling _ _

end CPS1AtomicSource.Current
