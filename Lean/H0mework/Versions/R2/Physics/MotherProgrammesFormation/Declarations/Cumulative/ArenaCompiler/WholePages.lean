import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaCompiler.WholeFactory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
open MotherArenaNetwork MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} (coordinates : LedgerCoordinates (rank := rank) N)

theorem rowKey_lt {s t : N.Support} {a : OpenResponsibilityAt N s} {b : OpenResponsibilityAt N t}
    (row : LedgerEntryEvolutionAt N a b) : (rowKey coordinates row).1 < 3 := by
  cases row <;> simp only [rowKey, Nat.reduceLT]

theorem destinationKey_lt {s t : N.Support} {a : OpenResponsibilityAt N s} (output : Destination s t a) :
    (destinationKey coordinates output).1 < 3 := rowKey_lt coordinates output.2

theorem originKey_lt {s t : N.Support} {b : OpenResponsibilityAt N t} (output : Origin s t b) :
    (originKey coordinates output).1 < 3 := rowKey_lt coordinates output.2

def writePage {s t : N.Support} (data : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩)
    (tag : Nat) (input output : B) : Prop :=
  if tag < 3 then
    ∃ entry, coordinates.entry s entry = input ∧ destinationKey coordinates (data.destination entry) = (tag, output)
  else
    ∃ entry, coordinates.entry t entry = input ∧ originKey coordinates (data.origin entry) = (tag - 3, output)

def terminalPage {s : N.Support} (data : LedgerTerminalEvolutionAt N ⟨s⟩)
    (tag : Nat) (input output : B) : Prop :=
  tag = 6 ∧ ∃ entry, coordinates.entry s entry = input ∧ coordinates.settlement s (data.discharge entry).receipt = output

section Write
variable {s t : N.Support} (data : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩) {material : MotherArenaHigher.Material rank} {context : MotherArenaHigher.Base rank}
    (graph : ∀ tag input output, r3 material tag context input output ↔ writePage coordinates data tag input output)
include graph

theorem destination_graph_at (entry : OpenResponsibilityAt N s) (output : Destination s t entry) :
    destinationGraph coordinates material context entry output ↔ output = data.destination entry := by
  rw [destinationGraph, graph]
  simp only [writePage, if_pos (destinationKey_lt coordinates output)]
  change (∃ other, coordinates.entry s other = coordinates.entry s entry ∧
    destinationKey coordinates (data.destination other) = destinationKey coordinates output) ↔ _
  constructor
  · rintro ⟨other, same, keyEq⟩
    have same := (coordinates.entry s).injective same
    cases same
    exact (destinationKey_injective coordinates keyEq).symm
  · intro same
    cases same
    exact ⟨entry, rfl, rfl⟩

theorem origin_graph_at (entry : OpenResponsibilityAt N t) (output : Origin s t entry) :
    originGraph coordinates material context entry output ↔ output = data.origin entry := by
  rw [originGraph, graph]
  simp only [writePage, show ¬ (3 + (originKey coordinates output).1 < 3) by omega,
    if_false, Nat.add_sub_cancel_left]
  change (∃ other, coordinates.entry t other = coordinates.entry t entry ∧
    originKey coordinates (data.origin other) = originKey coordinates output) ↔ _
  constructor
  · rintro ⟨other, same, keyEq⟩
    have same := (coordinates.entry t).injective same
    cases same
    exact (originKey_injective coordinates keyEq).symm
  · intro same
    cases same
    exact ⟨entry, rfl, rfl⟩

theorem writeCheckOfPage : WriteCheck coordinates material context s t where
  destination := fun entry => ⟨data.destination entry, (destination_graph_at coordinates data graph entry _).mpr rfl,
    fun output selected => (destination_graph_at coordinates data graph entry output).mp selected⟩
  origin := fun entry => ⟨data.origin entry, (origin_graph_at coordinates data graph entry _).mpr rfl,
    fun output selected => (origin_graph_at coordinates data graph entry output).mp selected⟩

theorem write_eq_of_page : write coordinates material context s t (writeCheckOfPage coordinates data graph) = data := by
  apply congrArg₂ (fun destination origin => ({ destination, origin } : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩))
  · funext entry
    exact (destination_graph_at coordinates data graph entry _).mp
      (Classical.choose_spec ((writeCheckOfPage coordinates data graph).destination entry)).1
  · funext entry
    exact (origin_graph_at coordinates data graph entry _).mp
      (Classical.choose_spec ((writeCheckOfPage coordinates data graph).origin entry)).1

end Write

section Terminal
variable {s : N.Support} (data : LedgerTerminalEvolutionAt N ⟨s⟩) {material : MotherArenaHigher.Material rank} {context : MotherArenaHigher.Base rank}
    (graph : ∀ tag input output, r3 material tag context input output ↔ terminalPage coordinates data tag input output)
include graph

theorem terminal_graph_at (entry : OpenResponsibilityAt N s) (receipt : N.DispositionAt s .supportSettlement) :
    r3 material 6 context (coordinates.entry s entry) (coordinates.settlement s receipt) ↔
      receipt = (data.discharge entry).receipt := by
  rw [graph]
  simp only [terminalPage, true_and]
  constructor
  · rintro ⟨other, same, receiptEq⟩
    have same := (coordinates.entry s).injective same
    cases same
    exact ((coordinates.settlement s).injective receiptEq).symm
  · intro same
    cases same
    exact ⟨entry, rfl, rfl⟩

theorem terminalCheckOfPage : TerminalCheck coordinates material context s := fun entry =>
  ⟨(data.discharge entry).receipt, (terminal_graph_at coordinates data graph entry _).mpr rfl,
    fun receipt selected => (terminal_graph_at coordinates data graph entry receipt).mp selected⟩

theorem terminal_eq_of_page : terminal coordinates material context s (terminalCheckOfPage coordinates data graph) = data := by
  apply congrArg (fun discharge => ({ discharge } : LedgerTerminalEvolutionAt N ⟨s⟩))
  funext entry
  apply congrArg LedgerEntryTerminalAt.mk
  exact (terminal_graph_at coordinates data graph entry _).mp
    (Classical.choose_spec (terminalCheckOfPage coordinates data graph entry)).1

end Terminal
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
