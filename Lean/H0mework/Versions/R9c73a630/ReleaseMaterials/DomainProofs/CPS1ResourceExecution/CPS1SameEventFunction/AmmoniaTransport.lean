import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.AmmoniaPhysical
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.SourceGenome

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1EnzymeBath.BathAccounting
variable {frame : CPS1Recycling.Frame}

theorem electronic_nh3_inputs (reaction : CPS1ElectronicSource.Reaction frame) :
    (reaction.reactants frame).count (electronicNH3 frame) = 0 := by
  cases reaction
  case jointAttach joint kind =>
    cases kind <;> simp [CPS1ElectronicSource.Reaction.reactants,CPS1EnzymeBath.componentSpecies,
      CPS1EnzymeBath.Primary.TemplateKind.molecule,electronicNH3,bathNH3,atomicNH3,
      atomizedNH3,localNH3,CPS1LocalChemicalExecution.molecule,CPS1StockRecursion.Dictionary.old]
  all_goals simp only [CPS1ElectronicSource.Reaction.reactants,CPS1ElectronicSource.guards]
  all_goals repeat first
    | (solve | simp [electronicNH3,bathNH3])
    | split

theorem electronic_nh3_outputs (reaction : CPS1ElectronicSource.Reaction frame) :
    (reaction.products frame).count (electronicNH3 frame) = 0 := by
  cases reaction <;> simp only [CPS1ElectronicSource.Reaction.products]
  all_goals repeat first
    | (solve | simp [electronicNH3,bathNH3])
    | split

theorem nuclear_nh3_inputs (reaction : CPS1QuantumNuclear.Reaction frame) :
    (reaction.reactants frame).count (nuclearNH3 frame) = 0 := by
  cases reaction
  case retained old =>
    exact (List.count_map_of_injective _ _ (fun _ _ same => CPS1QuantumNuclear.Species.retained.inj same) _).trans
      (electronic_nh3_inputs old)
  all_goals simp only [CPS1QuantumNuclear.Reaction.reactants,CPS1QuantumNuclear.guards]
  all_goals dsimp only [deformedNH3,molecularNH3,followingNH3,nuclearNH3,electronicNH3,bathNH3,atomicNH3,atomizedNH3,localNH3]
  all_goals repeat first
    | (solve | simp)
    | split

theorem nuclear_nh3_outputs (reaction : CPS1QuantumNuclear.Reaction frame) :
    (reaction.products frame).count (nuclearNH3 frame) = 0 := by
  cases reaction
  case retained old =>
    exact (List.count_map_of_injective _ _ (fun _ _ same => CPS1QuantumNuclear.Species.retained.inj same) _).trans
      (electronic_nh3_outputs old)
  all_goals simp only [CPS1QuantumNuclear.Reaction.products]
  all_goals dsimp only [deformedNH3,molecularNH3,followingNH3,nuclearNH3,electronicNH3,bathNH3,atomicNH3,atomizedNH3,localNH3]
  all_goals repeat first
    | (solve | simp)
    | split

theorem following_nh3_inputs (reaction : CPS1Following.Reaction frame) :
    (reaction.reactants frame).count (followingNH3 frame) = 0 := by
  cases reaction
  case retained old =>
    exact (List.count_map_of_injective _ _ (fun _ _ same => CPS1Following.Species.retained.inj same) _).trans
      (nuclear_nh3_inputs old)
  all_goals simp only [CPS1Following.Reaction.reactants,CPS1Following.guards]
  all_goals dsimp only [deformedNH3,molecularNH3,followingNH3,nuclearNH3,electronicNH3,bathNH3,atomicNH3,atomizedNH3,localNH3]
  all_goals repeat first
    | (solve | simp)
    | split

theorem following_nh3_outputs (reaction : CPS1Following.Reaction frame) :
    (reaction.products frame).count (followingNH3 frame) = 0 := by
  cases reaction
  case retained old =>
    exact (List.count_map_of_injective _ _ (fun _ _ same => CPS1Following.Species.retained.inj same) _).trans
      (nuclear_nh3_outputs old)
  all_goals simp only [CPS1Following.Reaction.products]
  all_goals dsimp only [deformedNH3,molecularNH3,followingNH3,nuclearNH3,electronicNH3,bathNH3,atomicNH3,atomizedNH3,localNH3]
  all_goals repeat first
    | (solve | simp)
    | split

theorem molecular_nh3_inputs (reaction : CPS1MolecularFrame.Reaction frame) :
    (reaction.reactants frame).count (molecularNH3 frame) = 0 := by
  cases reaction
  case retained old =>
    exact (List.count_map_of_injective _ _ (fun _ _ same => CPS1MolecularFrame.Species.retained.inj same) _).trans
      (following_nh3_inputs old)
  all_goals simp only [CPS1MolecularFrame.Reaction.reactants,CPS1MolecularFrame.guards]
  all_goals dsimp only [deformedNH3,molecularNH3,followingNH3,nuclearNH3,electronicNH3,bathNH3,atomicNH3,atomizedNH3,localNH3]
  all_goals repeat first
    | (solve | simp)
    | split

theorem molecular_nh3_outputs (reaction : CPS1MolecularFrame.Reaction frame) :
    (reaction.products frame).count (molecularNH3 frame) = 0 := by
  cases reaction
  case retained old =>
    exact (List.count_map_of_injective _ _ (fun _ _ same => CPS1MolecularFrame.Species.retained.inj same) _).trans
      (following_nh3_outputs old)
  all_goals simp only [CPS1MolecularFrame.Reaction.products]
  all_goals dsimp only [deformedNH3,molecularNH3,followingNH3,nuclearNH3,electronicNH3,bathNH3,atomicNH3,atomizedNH3,localNH3]
  all_goals repeat first
    | (solve | simp)
    | split

theorem deformed_nh3_inputs (reaction : CPS1Deformation.Reaction frame) :
    (reaction.reactants frame).count (deformedNH3 frame) = 0 := by
  cases reaction
  case retained old =>
    exact (List.count_map_of_injective _ _ (fun _ _ same => CPS1Deformation.Species.retained.inj same) _).trans
      (molecular_nh3_inputs old)
  all_goals simp only [CPS1Deformation.Reaction.reactants,CPS1Deformation.guards]
  all_goals dsimp only [deformedNH3,molecularNH3,followingNH3,nuclearNH3,electronicNH3,bathNH3,atomicNH3,atomizedNH3,localNH3]
  all_goals repeat first
    | (solve | simp)
    | split

theorem deformed_nh3_outputs (reaction : CPS1Deformation.Reaction frame) :
    (reaction.products frame).count (deformedNH3 frame) = 0 := by
  cases reaction
  case retained old =>
    exact (List.count_map_of_injective _ _ (fun _ _ same => CPS1Deformation.Species.retained.inj same) _).trans
      (molecular_nh3_outputs old)
  all_goals simp only [CPS1Deformation.Reaction.products]
  all_goals dsimp only [deformedNH3,molecularNH3,followingNH3,nuclearNH3,electronicNH3,bathNH3,atomicNH3,atomizedNH3,localNH3]
  all_goals repeat first
    | (solve | simp)
    | split

theorem electronic_ammonia_preserved (program : List (CPS1ElectronicSource.Reaction frame)) (stock : CPS1ElectronicSource.Stock frame) :
    (CPS1ElectronicSource.execute frame program stock).stock.count (electronicNH3 frame) = stock.count (electronicNH3 frame) :=
  execute_count_preserved (CPS1ElectronicSource.Reaction.reactants frame) (CPS1ElectronicSource.Reaction.products frame)
    (electronicNH3 frame) electronic_nh3_inputs electronic_nh3_outputs program stock

theorem nuclear_ammonia_preserved (program : List (CPS1QuantumNuclear.Reaction frame)) (stock : CPS1QuantumNuclear.Stock frame) :
    (CPS1QuantumNuclear.execute frame program stock).stock.count (nuclearNH3 frame) = stock.count (nuclearNH3 frame) :=
  execute_count_preserved (CPS1QuantumNuclear.Reaction.reactants frame) (CPS1QuantumNuclear.Reaction.products frame)
    (nuclearNH3 frame) nuclear_nh3_inputs nuclear_nh3_outputs program stock

theorem following_ammonia_preserved (program : List (CPS1Following.Reaction frame)) (stock : CPS1Following.Stock frame) :
    (CPS1Following.execute frame program stock).stock.count (followingNH3 frame) = stock.count (followingNH3 frame) :=
  execute_count_preserved (CPS1Following.Reaction.reactants frame) (CPS1Following.Reaction.products frame)
    (followingNH3 frame) following_nh3_inputs following_nh3_outputs program stock

theorem molecular_ammonia_preserved (program : List (CPS1MolecularFrame.Reaction frame)) (stock : CPS1MolecularFrame.Stock frame) :
    (CPS1MolecularFrame.execute frame program stock).stock.count (molecularNH3 frame) = stock.count (molecularNH3 frame) :=
  execute_count_preserved (CPS1MolecularFrame.Reaction.reactants frame) (CPS1MolecularFrame.Reaction.products frame)
    (molecularNH3 frame) molecular_nh3_inputs molecular_nh3_outputs program stock

theorem deformed_ammonia_preserved (program : List (CPS1Deformation.Reaction frame)) (stock : CPS1Deformation.Stock frame) :
    (CPS1Deformation.execute frame program stock).stock.count (deformedNH3 frame) = stock.count (deformedNH3 frame) :=
  execute_count_preserved (CPS1Deformation.Reaction.reactants frame) (CPS1Deformation.Reaction.products frame)
    (deformedNH3 frame) deformed_nh3_inputs deformed_nh3_outputs program stock

end
end CPS1SameEventFunction
