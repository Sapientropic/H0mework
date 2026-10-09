import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Body
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Contract

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1AtomicDynamics
noncomputable section
open CPS1ResourceExecution CPS1LocalChemicalExecution

inductive Species (frame : CPS1Recycling.Frame)
  | retained (old : CPS1AtomicSource.Current.Species frame)
  | body (state : Body.State frame)
  | rawRow (address : Charged.Address) (row : Body.Row)
  | rawEnergy (amount : ℝ)
  | rawTime (dt : ℝ)
  | spentPulse (pulse : Body.Pulse)
  | missingAtomic
  | guard (failure : Body.Failure)
  deriving DecidableEq

abbrev Stock (frame : CPS1Recycling.Frame) := List (Species frame)

inductive Reaction (frame : CPS1Recycling.Frame)
  | capture (chain : Chain frame)
  | requireAtomic
  | report (state : Body.State frame) (address : Charged.Address) (row : Body.Row)
  | deposit (state : Body.State frame) (amount : ℝ)
  | pulse (state : Body.State frame) (dt : ℝ)
  deriving DecidableEq

def guards {A : Type} (frame : CPS1Recycling.Frame) : Except Body.Failure A → Stock frame
  | .error failure => [.guard failure]
  | .ok _ => []

def Reaction.reactants (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .capture chain => [.retained (.atomic chain)]
  | .requireAtomic => [.missingAtomic]
  | .report state address row => [.body state,.rawRow address row] ++ guards frame (Body.report? frame state address row)
  | .deposit state amount => [.body state,.rawEnergy amount] ++ guards frame (Body.deposit? frame state amount)
  | .pulse state dt => [.body state,.rawTime dt] ++ guards frame (Body.pulse? frame state dt)

def Reaction.products (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .capture chain => [.body ⟨chain,[],0⟩]
  | .requireAtomic => []
  | .report state address row =>
    match Body.report? frame state address row with | .ok next => [.body next] | .error _ => []
  | .deposit state amount =>
    match Body.deposit? frame state amount with | .ok next => [.body next] | .error _ => []
  | .pulse state dt =>
    match Body.pulse? frame state dt with
    | .ok next => [.body next.1,.spentPulse next.2]
    | .error _ => []

abbrev Execution (frame : CPS1Recycling.Frame) := Inventory.Execution (Species frame) (Reaction frame)

def execute (frame : CPS1Recycling.Frame) (program : List (Reaction frame)) (stock : Stock frame) : Execution frame :=
  Inventory.execute (Reaction.reactants frame) (Reaction.products frame) program stock

theorem capture_current (frame : CPS1Recycling.Frame) (chain : Chain frame) (surplus stock : Stock frame)
    (inventory : stock.Perm (.retained (.atomic chain) :: surplus)) :
    let result := execute frame [.capture chain] stock
    result.fired = [.capture chain] ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (.body ⟨chain,[],0⟩ :: surplus) := by
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame) (.capture chain)
    surplus stock inventory with ⟨next,paid,generated⟩
  dsimp only
  simp only [execute,Inventory.execute,paid]
  exact ⟨True.intro,True.intro,True.intro,generated⟩

theorem actual_report (frame : CPS1Recycling.Frame) (state next : Body.State frame)
    (address : Charged.Address) (row : Body.Row)
    (reported : Body.report? frame state address row = .ok next)
    (surplus stock : Stock frame)
    (inventory : stock.Perm ([.body state,.rawRow address row] ++ surplus)) :
    let result := execute frame [.report state address row] stock
    result.fired = [.report state address row] ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (.body next :: surplus) := by
  have aligned : stock.Perm ((Reaction.report state address row).reactants frame ++ surplus) := by
    simpa only [Reaction.reactants,reported,guards,List.append_nil] using inventory
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.report state address row) surplus stock aligned with ⟨after,paid,generated⟩
  dsimp only
  simp only [execute,Inventory.execute,paid]
  simpa only [Reaction.products,reported,List.singleton_append] using
    (show True ∧ True ∧ True ∧ after.Perm ((Reaction.report state address row).products frame ++ surplus) from
      ⟨True.intro,True.intro,True.intro,generated⟩)

theorem actual_pulse (frame : CPS1Recycling.Frame) (state next : Body.State frame)
    (pulse : Body.Pulse) (dt : ℝ) (computed : Body.pulse? frame state dt = .ok (next,pulse))
    (surplus stock : Stock frame)
    (inventory : stock.Perm ([.body state,.rawTime dt] ++ surplus)) :
    let result := execute frame [.pulse state dt] stock
    result.fired = [.pulse state dt] ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ([.body next,.spentPulse pulse] ++ surplus) := by
  have aligned : stock.Perm ((Reaction.pulse state dt).reactants frame ++ surplus) := by
    simpa only [Reaction.reactants,computed,guards,List.append_nil] using inventory
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.pulse state dt) surplus stock aligned with ⟨after,paid,generated⟩
  dsimp only
  simp only [execute,Inventory.execute,paid]
  simpa only [Reaction.products,computed] using
    (show True ∧ True ∧ True ∧ after.Perm ((Reaction.pulse state dt).products frame ++ surplus) from
      ⟨True.intro,True.intro,True.intro,generated⟩)

theorem full_inventory (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (species : Species frame) :
    let result := execute frame program stock
    stock.count species + (Inventory.credit (Reaction.products frame) result.fired).count species =
      result.stock.count species + (Inventory.debit (Reaction.reactants frame) result.fired).count species :=
  Inventory.execution_balance (Reaction.reactants frame) (Reaction.products frame) program stock species

theorem source_cut (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (missing : Species frame)
    (cut : (execute frame program stock).missing = some missing) :
    ∃ reaction rest, (execute frame program stock).remaining = reaction :: rest ∧
      (execute frame program stock).stock.count missing < (reaction.reactants frame).count missing :=
  Inventory.execution_cut (Reaction.reactants frame) (Reaction.products frame) program stock missing cut

end
end CPS1AtomicDynamics
