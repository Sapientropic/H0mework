import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Recycling.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Reinitiation
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive RecruitmentFactor | eIF4A | eIF4B | eIF4E | eIF4G
  deriving DecidableEq, Repr

/-- The original recycled stock and the separately registered RNA remain on one carrier. -/
inductive Species (frame : CPS1Recycling.Frame)
  | retained (old : CPS1Recycling.Species frame)
  | rna (word : RegisteredRna)
  | factor (factor : RecruitmentFactor)
  | adp
  | scanning (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (address : Nat)
  | recognized (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (address : Nat)
  | committed (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (address : Nat)
  | unavailableCodon (rna : RegisteredRna) (address : Nat)
  deriving DecidableEq

abbrev Stock (frame : CPS1Recycling.Frame) := List (Species frame)

def startCodonAt (rna : RegisteredRna) (address : Nat) : Bool :=
  ((Rna.template rna).drop address).take 3 == [.adenine,.thymine,.guanine]

/-- A fixed reaction dictionary. Addresses in a program are computed from raw RNA. -/
inductive Primitive
  | recruit (sites : CPS1Recycling.Sites) (rna : RegisteredRna)
  | advance (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (address : Nat)
  | recognize (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (address : Nat)
  | commit (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (address : Nat)
  deriving DecidableEq

namespace Primitive
def reactants (frame : CPS1Recycling.Frame) : Primitive → Stock frame
  | .recruit sites rna =>
    [.retained (.next43 sites),.rna rna,.factor .eIF4A,.factor .eIF4B,.factor .eIF4E,.factor .eIF4G]
  | .advance sites rna address =>
    [.scanning sites rna address,.retained (.old .atp),.retained (.old .water)]
  | .recognize sites rna address =>
    [.scanning sites rna address,.retained (.old (.actor .eIF5))] ++
      if startCodonAt rna address then [] else [.unavailableCodon rna address]
  | .commit sites rna address =>
    [.recognized sites rna address,.retained (.old .water)]

def products (frame : CPS1Recycling.Frame) : Primitive → Stock frame
  | .recruit sites rna => [.scanning sites rna 0,.retained .eIF3j]
  | .advance sites rna address =>
    [.scanning sites rna (address+1),.adp,.retained (.old .phosphate),.retained (.old .proton)]
  | .recognize sites rna address =>
    [.recognized sites rna address,.retained (.old (.actor .eIF1))]
  | .commit sites rna address =>
    [.committed sites rna address,.retained (.old .phosphate),.retained (.old .proton)]
end Primitive

abbrev Execution (frame : CPS1Recycling.Frame) := Inventory.Execution (Species frame) Primitive

/-- The shared inventory kernel specialized to this common carrier. -/
def execute (frame : CPS1Recycling.Frame) (program : List Primitive) (stock : Stock frame) : Execution frame :=
  Inventory.execute (Primitive.reactants frame) (Primitive.products frame) program stock

theorem execute_cons (frame : CPS1Recycling.Frame) (reaction : Primitive) (rest : List Primitive)
    (stock : Stock frame) : execute frame (reaction :: rest) stock =
    match Inventory.fire (Primitive.reactants frame) (Primitive.products frame) reaction stock with
    | .error missing => ⟨[],reaction :: rest,stock,some missing⟩
    | .ok next =>
      let after := execute frame rest next
      ⟨reaction :: after.fired,after.remaining,after.stock,after.missing⟩ := by
  unfold execute
  rw [Inventory.execute_cons]
  cases Inventory.fire (Primitive.reactants frame) (Primitive.products frame) reaction stock <;> rfl

def scanProgram (sites : CPS1Recycling.Sites) (rna : RegisteredRna) : List Primitive :=
  match Coding.firstStart (Rna.template rna) with
  | some address => [.recruit sites rna] ++
      (List.range address).map (Primitive.advance sites rna) ++
      [.recognize sites rna address,.commit sites rna address]
  | none => [.recruit sites rna] ++
      (List.range (Rna.template rna).length).map (Primitive.advance sites rna) ++
      [.recognize sites rna (Rna.template rna).length]

/-- Only raw factors and currencies may enter; a caller cannot provide a scanned complex. -/
inductive RawMaterial
  | factor (factor : RecruitmentFactor) | atp | water | gtp
  deriving DecidableEq, Repr

def RawMaterial.species (frame : CPS1Recycling.Frame) : RawMaterial → Species frame
  | .factor f => .factor f
  | .atp => .retained (.old .atp)
  | .water => .retained (.old .water)
  | .gtp => .retained (.old .gtp)

def initialStock (frame : CPS1Recycling.Frame) (old : CPS1Recycling.ExecutionAt frame)
    (rna : RegisteredRna) (feed : List RawMaterial) : Stock frame :=
  old.stock.map Species.retained ++ [.rna rna] ++ feed.map (RawMaterial.species frame)

def run (frame : CPS1Recycling.Frame) (old : CPS1Recycling.ExecutionAt frame)
    (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (feed : List RawMaterial) : Execution frame :=
  execute frame (scanProgram sites rna) (initialStock frame old rna feed)

def rawFuel (address : Nat) : List RawMaterial :=
  [.factor .eIF4A,.factor .eIF4B,.factor .eIF4E,.factor .eIF4G] ++
    (List.replicate address .atp ++ List.replicate (address+1) .water)

def workProducts (frame : CPS1Recycling.Frame) (address : Nat) : Stock frame :=
  List.replicate address .adp ++ List.replicate address (.retained (.old .phosphate)) ++
    List.replicate address (.retained (.old .proton))

theorem run_decomposes (frame : CPS1Recycling.Frame) (old : CPS1Recycling.ExecutionAt frame)
    (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (feed : List RawMaterial) :
    (run frame old sites rna feed).fired ++ (run frame old sites rna feed).remaining = scanProgram sites rna :=
  Inventory.execution_decomposes _ _ _ _

theorem run_balance (frame : CPS1Recycling.Frame) (old : CPS1Recycling.ExecutionAt frame)
    (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (feed : List RawMaterial) (species : Species frame) :
    (initialStock frame old rna feed).count species +
      (Inventory.credit (Primitive.products frame) (run frame old sites rna feed).fired).count species =
    (run frame old sites rna feed).stock.count species +
      (Inventory.debit (Primitive.reactants frame) (run frame old sites rna feed).fired).count species :=
  Inventory.execution_balance _ _ _ _ _

theorem run_potential (frame : CPS1Recycling.Frame) (old : CPS1Recycling.ExecutionAt frame)
    (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (feed : List RawMaterial) (μ : Species frame → ℚ) :
    Inventory.value μ (initialStock frame old rna feed) =
      Inventory.value μ (run frame old sites rna feed).stock +
      Inventory.affinity μ (Primitive.reactants frame) (Primitive.products frame)
        (run frame old sites rna feed).fired :=
  Inventory.execution_potential _ _ _ _ _

theorem run_cut (frame : CPS1Recycling.Frame) (old : CPS1Recycling.ExecutionAt frame)
    (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (feed : List RawMaterial)
    (missing : Species frame) (cut : (run frame old sites rna feed).missing = some missing) :
    ∃ reaction rest, (run frame old sites rna feed).remaining = reaction :: rest ∧
      (run frame old sites rna feed).stock.count missing < (reaction.reactants frame).count missing :=
  Inventory.execution_cut _ _ _ _ _ cut

namespace Source
/-- The new RNA is the registered editor molecule, not the old endogenous message coordinate. -/
def execution (edits : Target.Edits) (water additional : Nat) (site : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (feed : List RawMaterial) :
    Option (Σ frame : CPS1Recycling.Frame, Execution frame) :=
  (CPS1Recycling.Source.execution edits water additional
    (CPS1Recycling.productiveEvents site) recycleFeed).map fun prior =>
      ⟨prior.1,run prior.1 prior.2 site.after Molecules.mrna feed⟩

theorem original_start_and_context :
    Coding.firstStart (Rna.template Molecules.mrna) = some 151 ∧
    startCodonAt Molecules.mrna 151 = true := by
  exact ⟨Molecules.original_first_frame_generated.1,by decide +kernel⟩

end Source
end CPS1Reinitiation
