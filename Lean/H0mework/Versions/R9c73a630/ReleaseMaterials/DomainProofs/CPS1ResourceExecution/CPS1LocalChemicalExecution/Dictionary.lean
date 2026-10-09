import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Actual
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Chemistry
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.PeptideMaterial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1LocalChemicalExecution
open CPS1ResourceExecution

structure Vec where
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq

def Vec.add (a b : Vec) : Vec := ⟨a.x+b.x,a.y+b.y,a.z+b.z⟩
def Vec.scale (t : ℚ) (a : Vec) : Vec := ⟨t*a.x,t*a.y,t*a.z⟩
def Vec.sub (a b : Vec) : Vec := ⟨a.x-b.x,a.y-b.y,a.z-b.z⟩
def Vec.dot (a b : Vec) : ℚ := a.x*b.x+a.y*b.y+a.z*b.z
def Vec.kinetic (mass : ℚ) (momentum : Vec) : ℚ := momentum.dot momentum/(2*mass)

inductive EndGroup | aminoHydrogen | carboxylHydroxyl deriving DecidableEq

/-- Cα source rows are a first positional restriction. Every unreported row remains
missing; the carrier does not assert an all-atom native fold or activation. -/
structure Chain (frame : CPS1Recycling.Frame) where
  bonds : List Nat
  hydrolysed : List Nat
  endGroups : List (Nat × EndGroup)
  positions : List (Nat × Vec)
  momenta : List (Nat × Vec)
  inertias : List (Nat × ℚ)
  deriving DecidableEq

def Chain.initial (frame : CPS1Recycling.Frame) : Chain frame :=
  ⟨List.range (Actual.cps1 frame).2.length,[],
    [(0,.aminoHydrogen),((Actual.cps1 frame).2.length,.carboxylHydroxyl)],[],[],[]⟩

/-- Edge i joins source residues i and i+1. Components are calculated from the
remaining edges, retaining the original residue addresses and sequence. -/
def attachResidue (bonds : List Nat) (residue : Nat × AA) :
    List (List (Nat × AA)) → List (List (Nat × AA))
    | [] => [[residue]]
    | first :: remaining =>
      if residue.1 ∈ bonds then (residue :: first) :: remaining
      else [residue] :: first :: remaining

def components (bonds : List Nat) (word : List (Nat × AA)) : List (List (Nat × AA)) :=
  List.rec [] (fun residue _ fragments => attachResidue bonds residue fragments) word

theorem components_cons (bonds : List Nat) (residue : Nat × AA) (rest : List (Nat × AA)) :
    components bonds (residue :: rest) = attachResidue bonds residue (components bonds rest) := rfl

def Chain.fragments (frame : CPS1Recycling.Frame) (chain : Chain frame) : List (List (Nat × AA)) :=
  components chain.bonds ((Actual.cps1 frame).word.zipIdx.map (fun row => (row.2,row.1)))

def Chain.atoms (frame : CPS1Recycling.Frame) (chain : Chain frame) : PeptideMaterial.Element → Int :=
  PeptideMaterial.wordAtoms (Actual.cps1 frame).word chain.hydrolysed.length

def Chain.cleave (frame : CPS1Recycling.Frame) (chain : Chain frame) (address : Nat) : Chain frame :=
  {chain with
    bonds := chain.bonds.erase address
    hydrolysed := address :: chain.hydrolysed
    endGroups := (address,.carboxylHydroxyl) :: (address+1,.aminoHydrogen) :: chain.endGroups}

def EndGroup.atoms : EndGroup → Chemistry.Atom → Nat
  | .aminoHydrogen => Chemistry.formula 0 1 0 0 0 0 0
  | .carboxylHydroxyl => Chemistry.formula 0 1 0 1 0 0 0

theorem cleavage_water (atom : Chemistry.Atom) :
    EndGroup.aminoHydrogen.atoms atom + EndGroup.carboxylHydroxyl.atoms atom =
      Chemistry.Molecule.water.atoms atom := by
  cases atom <;> rfl

theorem components_all_material (bonds : List Nat) (word : List (Nat × AA)) :
    (components bonds word).flatten = word := by
  have attach (residue : Nat × AA) (fragments : List (List (Nat × AA))) :
      (attachResidue bonds residue fragments).flatten = residue :: fragments.flatten := by
    cases fragments with
    | nil => rfl
    | cons first remaining =>
      by_cases connected : residue.1 ∈ bonds <;>
        simp [attachResidue,connected]
  induction word with
  | nil => rfl
  | cons residue rest ih =>
    rw [components_cons,attach,ih]

def Chain.position (frame : CPS1Recycling.Frame) (chain : Chain frame) (address : Nat) : Option Vec :=
  (chain.positions.find? (fun row => row.1 = address)).map Prod.snd

def Chain.momentum (frame : CPS1Recycling.Frame) (chain : Chain frame) (address : Nat) : Option Vec :=
  (chain.momenta.find? (fun row => row.1 = address)).map Prod.snd

def Chain.inertia (frame : CPS1Recycling.Frame) (chain : Chain frame) (address : Nat) : Option ℚ :=
  (chain.inertias.find? (fun row => row.1 = address)).map Prod.snd

def Chain.inertiaConsistent (frame : CPS1Recycling.Frame) (chain : Chain frame)
    (address : Nat) (mass : ℚ) : Bool :=
  (chain.inertia frame address).isNone || chain.inertia frame address == some mass

def Chain.recordInertia (frame : CPS1Recycling.Frame) (chain : Chain frame)
    (address : Nat) (mass : ℚ) : Chain frame :=
  {chain with inertias := (address,mass) :: (chain.inertias.filter (fun row => row.1 ≠ address))}

def Chain.report (frame : CPS1Recycling.Frame) (chain : Chain frame) (address : Nat) (r p : Vec) : Chain frame :=
  {chain with
    positions := (address,r) :: (chain.positions.filter (fun row => row.1 ≠ address))
    momenta := (address,p) :: (chain.momenta.filter (fun row => row.1 ≠ address))}

def Chain.reportConsistent (frame : CPS1Recycling.Frame) (chain : Chain frame)
    (address : Nat) (r p : Vec) : Bool :=
  ((chain.position frame address).isNone || chain.position frame address == some r) &&
    ((chain.momentum frame address).isNone || chain.momentum frame address == some p)

def Chain.drive? (frame : CPS1Recycling.Frame) (chain : Chain frame) (address : Nat)
    (force : Vec) (dt mass : ℚ) : Option (Chain frame × ℚ) := do
  if mass ≤ 0 ∨ dt < 0 then none else do
  if !(chain.inertiaConsistent frame address mass) then none else do
  let r ← chain.position frame address
  let p ← chain.momentum frame address
  let nextP := p.add (force.scale dt)
  let nextR := (r.add (p.scale (dt/mass))).add (force.scale (dt*dt/(2*mass)))
  pure ((chain.report frame address nextR nextP).recordInertia frame address mass,
    Vec.kinetic mass nextP - Vec.kinetic mass p)

inductive Species (frame : CPS1Recycling.Frame)
  | retained (old : CPS1Reinitiation.Species frame)
  | chain (state : Chain frame)
  | molecule (molecule : Chemistry.Molecule)
  | processor
  | localRow (address : Nat) (r p : Vec)
  | impulse (address : Nat) (force : Vec) (dt mass : ℚ)
  | spentImpulse (address : Nat) (force : Vec) (dt mass work : ℚ)
  | missingPosition (address : Nat)
  | missingPeptideBond (address : Nat)
  | missingResidue (address : Nat)
  | conflictingRow (address : Nat)
  deriving DecidableEq

abbrev Stock (frame : CPS1Recycling.Frame) := List (Species frame)

def molecule (frame : CPS1Recycling.Frame) : Chemistry.Molecule → Species frame
  | .atp => .retained (CPS1StockRecursion.Dictionary.old frame .atp)
  | .adp => .retained (.retained .adp)
  | .phosphate => .retained (CPS1StockRecursion.Dictionary.old frame .phosphate)
  | .water => .retained (CPS1StockRecursion.Dictionary.old frame .water)
  | .proton => .retained (CPS1StockRecursion.Dictionary.old frame .proton)
  | .ammonia => .retained (CPS1StockRecursion.Dictionary.old frame .ammonia)
  | other => .molecule other

inductive Reaction (frame : CPS1Recycling.Frame)
  | capture
  | report (state : Chain frame) (address : Nat) (r p : Vec)
  | drive (state : Chain frame) (address : Nat) (force : Vec) (dt mass : ℚ)
  | hydrolyseBond (state : Chain frame) (address : Nat)
  | chemical (step : Chemistry.Step)
  deriving DecidableEq

def Reaction.reactants (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .capture => [.retained (Actual.species frame)]
  | .report state address r p => [.chain state,.localRow address r p] ++
      (if address < (Actual.cps1 frame).word.length then [] else [.missingResidue address]) ++
      (if state.reportConsistent frame address r p then [] else [.conflictingRow address])
  | .drive state address force dt mass => [.chain state,.impulse address force dt mass] ++
      if (state.drive? frame address force dt mass).isSome then [] else [.missingPosition address]
  | .hydrolyseBond state address => [.chain state,.processor,molecule frame .water] ++
      if address ∈ state.bonds then [] else [.missingPeptideBond address]
  | .chemical step => step.reactants.map (molecule frame)

def Reaction.products (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .capture => [.chain (Chain.initial frame)]
  | .report state address r p => [.chain (state.report frame address r p)]
  | .drive state address force dt mass =>
      let next := (state.drive? frame address force dt mass).getD (state,0)
      [.chain next.1,.spentImpulse address force dt mass next.2]
  | .hydrolyseBond state address =>
      [.chain (state.cleave frame address),.processor]
  | .chemical step => step.products.map (molecule frame)

abbrev Execution (frame : CPS1Recycling.Frame) := Inventory.Execution (Species frame) (Reaction frame)
def execute (frame : CPS1Recycling.Frame) (program : List (Reaction frame)) (stock : Stock frame) : Execution frame :=
  Inventory.execute (Reaction.reactants frame) (Reaction.products frame) program stock

/-- Actual reservation removes only the original genomic CPS1 chain from the current
common inventory. All RNA, other proteins, nucleotide layers and history survive. -/
theorem capture_from_actual (frame : CPS1Recycling.Frame) (actual : CPS1Reinitiation.Stock frame)
    (present : Actual.species frame ∈ actual) :
    let result := execute frame [.capture] (actual.map Species.retained)
    result.fired = [.capture] ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (.chain (Chain.initial frame) ::
        (actual.erase (Actual.species frame)).map Species.retained) := by
  have stock := (List.perm_cons_erase present).map (Species.retained (frame := frame))
  have aligned : (actual.map Species.retained).Perm
      ((Reaction.capture).reactants frame ++ (actual.erase (Actual.species frame)).map Species.retained) := by
    simpa only [Reaction.reactants,List.map_cons,List.singleton_append] using stock
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame) .capture
    ((actual.erase (Actual.species frame)).map Species.retained) (actual.map Species.retained) aligned with
      ⟨next,paid,generated⟩
  dsimp only
  simp only [execute,Inventory.execute,paid]
  exact ⟨True.intro,True.intro,True.intro,generated⟩

theorem hydrolyse_source_bond (frame : CPS1Recycling.Frame) (state : Chain frame) (address : Nat)
    (present : address ∈ state.bonds) (surplus stock : Stock frame)
    (inventory : stock.Perm ([.chain state,.processor,molecule frame .water] ++ surplus)) :
    let result := execute frame [.hydrolyseBond state address] stock
    result.fired = [.hydrolyseBond state address] ∧ result.remaining = [] ∧ result.missing = none ∧
    result.stock.Perm ([.chain (state.cleave frame address),.processor] ++ surplus) ∧
    (∀ element, (state.cleave frame address).atoms frame element = state.atoms frame element +
      (PeptideMaterial.waterAtoms element : Int)) ∧
    ((state.cleave frame address).fragments frame).flatten =
      (Actual.cps1 frame).word.zipIdx.map (fun row => (row.2,row.1)) := by
  have aligned : stock.Perm ((Reaction.hydrolyseBond state address).reactants frame ++ surplus) := by
    simpa only [Reaction.reactants,if_pos present,List.append_nil] using inventory
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.hydrolyseBond state address) surplus stock aligned with ⟨next,paid,generated⟩
  dsimp only
  simp only [execute,Inventory.execute,paid]
  refine ⟨True.intro,True.intro,True.intro,generated,?_,?_⟩
  · intro element
    exact (PeptideMaterial.hydrolysis_atoms (Actual.cps1 frame).word state.hydrolysed.length element).symm
  · exact components_all_material _ _

end CPS1LocalChemicalExecution
