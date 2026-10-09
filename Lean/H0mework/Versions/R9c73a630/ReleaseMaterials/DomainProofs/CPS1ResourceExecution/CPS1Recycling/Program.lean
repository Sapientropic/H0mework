import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Recycling.Chemistry

set_option autoImplicit false

namespace CPS1Recycling
open CPS1ResourceExecution

abbrev StockAt (frame : Frame) := List (Species frame)
abbrev ExecutionAt (frame : Frame) := Inventory.Execution (Species frame) Primitive

/-- The inlet cannot contain a recycled subunit, loaded initiator or future PIC. -/
inductive RawMaterial
  | abce1 (sites : Sites) | eIF3j | atp | gtp | water | methionine
  deriving DecidableEq, Repr

def RawMaterial.species (frame : Frame) : RawMaterial → Species frame
  | .abce1 sites => .abce1 sites
  | .eIF3j => .eIF3j
  | .atp => .old .atp
  | .gtp => .old .gtp
  | .water => .old .water
  | .methionine => .old (.freeAA .M)

inductive SplitSite | first | second deriving DecidableEq, Repr

def SplitSite.after : SplitSite → Sites
  | .first => humanHybrid
  | .second => ⟨.atp,.adp⟩

/-- Events select ATPase sites, never products or a successful recycling certificate. -/
inductive RawEvent
  | engageControl | engageWork | split (site : SplitSite)
  | hydrolyzeFirst (second : Nucleotide)
  | returnTrna (sites : Sites) | dischargeMessage (sites : Sites)
  | chargeInitiator | captureNext (sites : Sites)
  deriving DecidableEq, Repr

def RawEvent.primitive (frame : Frame) : RawEvent → Primitive
  | .engageControl => .engageControl (sourceTrna frame)
  | .engageWork => .engageWork (sourceTrna frame)
  | .split .first => .splitHydrolyzingFirst (sourceTrna frame)
  | .split .second => .splitHydrolyzingSecond (sourceTrna frame)
  | .hydrolyzeFirst second => .hydrolyzeFirst (sourceTrna frame) second
  | .returnTrna sites => .removeTrna (sourceTrna frame) sites
  | .dischargeMessage sites => .removeMessage sites
  | .chargeInitiator => .chargeNextInitiator
  | .captureNext sites => .captureNext sites

def compile (frame : Frame) (events : List RawEvent) : List Primitive :=
  events.map (RawEvent.primitive frame)

def currentStock (frame : Frame) (feed : List RawMaterial) : StockAt frame :=
  frame.native.stock.map Species.old ++ feed.map (RawMaterial.species frame)

/-- This is a specialization of the original inventory kernel. -/
def run (frame : Frame) (events : List RawEvent) (feed : List RawMaterial) : ExecutionAt frame :=
  Inventory.execute (Primitive.reactants frame) (Primitive.products frame)
    (compile frame events) (currentStock frame feed)

def debitAt (frame : Frame) (trace : List Primitive) : StockAt frame :=
  Inventory.debit (Primitive.reactants frame) trace

def creditAt (frame : Frame) (trace : List Primitive) : StockAt frame :=
  Inventory.credit (Primitive.products frame) trace

def affinityAt (frame : Frame) (μ : Species frame → ℚ) (trace : List Primitive) : ℚ :=
  Inventory.affinity μ (Primitive.reactants frame) (Primitive.products frame) trace

def productiveEvents (site : SplitSite) : List RawEvent :=
  [.engageControl,.engageWork,.split site,.returnTrna site.after,
    .dischargeMessage site.after,.chargeInitiator,.captureNext site.after]

def freshFuel : List RawMaterial :=
  [.abce1 emptySites,.atp,.atp,.water,.eIF3j,.methionine,.atp,.gtp]

theorem run_disposition (frame : Frame) (events : List RawEvent) (feed : List RawMaterial) :
    (run frame events feed).fired ++ (run frame events feed).remaining = compile frame events :=
  Inventory.execution_decomposes _ _ _ _

theorem run_inventory_balance (frame : Frame) (events : List RawEvent) (feed : List RawMaterial)
    (species : Species frame) :
    (currentStock frame feed).count species + (creditAt frame (run frame events feed).fired).count species =
      (run frame events feed).stock.count species + (debitAt frame (run frame events feed).fired).count species :=
  Inventory.execution_balance _ _ _ _ species

theorem run_potential (frame : Frame) (events : List RawEvent) (feed : List RawMaterial)
    (μ : Species frame → ℚ) :
    Inventory.value μ (currentStock frame feed) =
      Inventory.value μ (run frame events feed).stock + affinityAt frame μ (run frame events feed).fired :=
  Inventory.execution_potential _ _ _ _ μ

theorem run_cut (frame : Frame) (events : List RawEvent) (feed : List RawMaterial)
    (missing : Species frame) (cut : (run frame events feed).missing = some missing) :
    ∃ reaction rest, (run frame events feed).remaining = reaction :: rest ∧
      (run frame events feed).stock.count missing < (reaction.reactants frame).count missing :=
  Inventory.execution_cut _ _ _ _ missing cut

theorem run_currency_balance (frame : Frame) (events : List RawEvent) (feed : List RawMaterial) :
    moiety frame (adenylate frame) (currentStock frame feed) =
      moiety frame (adenylate frame) (run frame events feed).stock ∧
    moiety frame (guanylate frame) (currentStock frame feed) =
      moiety frame (guanylate frame) (run frame events feed).stock ∧
    moiety frame (phosphate frame) (currentStock frame feed) =
      moiety frame (phosphate frame) (run frame events feed).stock := by
  refine ⟨?_,?_,?_⟩
  · exact Inventory.execution_measure_preserved _ _ _ _ _
      (fun primitive _ => (primitive_currency_balance frame primitive).1)
  · exact Inventory.execution_measure_preserved _ _ _ _ _
      (fun primitive _ => (primitive_currency_balance frame primitive).2.1)
  · exact Inventory.execution_measure_preserved _ _ _ _ _
      (fun primitive _ => (primitive_currency_balance frame primitive).2.2)

theorem run_carrier_balance (frame : Frame) (events : List RawEvent) (feed : List RawMaterial) :
    moiety frame (abce1Count frame) (currentStock frame feed) =
      moiety frame (abce1Count frame) (run frame events feed).stock ∧
    moiety frame (trnaCount frame) (currentStock frame feed) =
      moiety frame (trnaCount frame) (run frame events feed).stock ∧
    moiety frame (smallCount frame) (currentStock frame feed) =
      moiety frame (smallCount frame) (run frame events feed).stock ∧
    moiety frame (largeCount frame) (currentStock frame feed) =
      moiety frame (largeCount frame) (run frame events feed).stock := by
  refine ⟨?_,?_,?_,?_⟩
  · exact Inventory.execution_measure_preserved _ _ _ _ _
      (fun primitive _ => (primitive_carrier_balance frame primitive).1)
  · exact Inventory.execution_measure_preserved _ _ _ _ _
      (fun primitive _ => (primitive_carrier_balance frame primitive).2.1)
  · exact Inventory.execution_measure_preserved _ _ _ _ _
      (fun primitive _ => (primitive_carrier_balance frame primitive).2.2.1)
  · exact Inventory.execution_measure_preserved _ _ _ _ _
      (fun primitive _ => (primitive_carrier_balance frame primitive).2.2.2)

theorem run_actor_balance (frame : Frame) (events : List RawEvent) (feed : List RawMaterial)
    (factor : Factor) :
    moiety frame (actorCount frame factor) (currentStock frame feed) =
      moiety frame (actorCount frame factor) (run frame events feed).stock :=
  Inventory.execution_measure_preserved _ _ _ _ _
    (fun primitive _ => primitive_actor_balance frame primitive factor)

theorem run_residue_message_balance (frame : Frame) (events : List RawEvent)
    (feed : List RawMaterial) (aa : AA) :
    moiety frame (residueCount frame aa) (currentStock frame feed) =
      moiety frame (residueCount frame aa) (run frame events feed).stock ∧
    moiety frame (messageCount frame) (currentStock frame feed) =
      moiety frame (messageCount frame) (run frame events feed).stock ∧
    moiety frame (initiatorCount frame) (currentStock frame feed) =
      moiety frame (initiatorCount frame) (run frame events feed).stock := by
  refine ⟨?_,?_,?_⟩
  · exact Inventory.execution_measure_preserved _ _ _ _ _
      (fun primitive _ => (primitive_residue_message_balance frame primitive aa).1)
  · exact Inventory.execution_measure_preserved _ _ _ _ _
      (fun primitive _ => (primitive_residue_message_balance frame primitive aa).2.1)
  · exact Inventory.execution_measure_preserved _ _ _ _ _
      (fun primitive _ => (primitive_residue_message_balance frame primitive aa).2.2)

end CPS1Recycling
