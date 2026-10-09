import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.AmmoniaNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1EnzymeBath.BathAccounting
variable {frame : CPS1Recycling.Frame}

def localNH3 (f : CPS1Recycling.Frame) := CPS1LocalChemicalExecution.molecule f .ammonia
def atomizedNH3 (f : CPS1Recycling.Frame) : CPS1AtomicSource.Current.Species f := .retained (localNH3 f)
def atomicNH3 (f : CPS1Recycling.Frame) : CPS1AtomicDynamics.Species f := .retained (atomizedNH3 f)
def bathNH3 (f : CPS1Recycling.Frame) : CPS1EnzymeBath.Species f := .retained (atomicNH3 f)
def electronicNH3 (f : CPS1Recycling.Frame) : CPS1ElectronicSource.Species f := .retained (bathNH3 f)
def nuclearNH3 (f : CPS1Recycling.Frame) : CPS1QuantumNuclear.Species f := .retained (electronicNH3 f)
def followingNH3 (f : CPS1Recycling.Frame) : CPS1Following.Species f := .retained (nuclearNH3 f)
def molecularNH3 (f : CPS1Recycling.Frame) : CPS1MolecularFrame.Species f := .retained (followingNH3 f)
def deformedNH3 (f : CPS1Recycling.Frame) : CPS1Deformation.Species f := .retained (molecularNH3 f)

theorem atomized_nh3_inputs (reaction : CPS1AtomicSource.Current.Reaction frame) :
    (reaction.reactants frame).count (atomizedNH3 frame) = 0 := by
  cases reaction <;> simp [CPS1AtomicSource.Current.Reaction.reactants,atomizedNH3,localNH3,
    CPS1AtomicSource.Current.proton,CPS1LocalChemicalExecution.molecule,
    CPS1StockRecursion.Dictionary.old,List.count_replicate]

theorem atomized_nh3_outputs (reaction : CPS1AtomicSource.Current.Reaction frame) :
    (reaction.products frame).count (atomizedNH3 frame) = 0 := by
  cases reaction <;> simp [CPS1AtomicSource.Current.Reaction.products,atomizedNH3]

theorem atomization_ammonia_count (previous : CPS1EditingChemicalJoin.Source.Occurrence frame) :
    (CPS1AtomicSource.Current.fromActual frame previous).current.stock.count (atomizedNH3 frame) =
      previous.current.stock.count (localNH3 frame) := by
  have preserved := execute_count_preserved
    (CPS1AtomicSource.Current.Reaction.reactants frame) (CPS1AtomicSource.Current.Reaction.products frame)
    (atomizedNH3 frame) atomized_nh3_inputs atomized_nh3_outputs
    (match CPS1LocalChemicalExecution.Source.heldChain frame previous.current.stock with
      | none => [.requireChain] | some chain => [.atomize chain])
    (previous.current.stock.map CPS1AtomicSource.Current.Species.retained)
  change (CPS1AtomicSource.Current.fromActual frame previous).current.stock.count (atomizedNH3 frame) = _ at preserved
  rw [preserved]
  exact List.count_map_of_injective _ _ (fun _ _ same => CPS1AtomicSource.Current.Species.retained.inj same) _

@[simp] theorem bath_guards_no_ammonia {A : Type} (result : Except CPS1AtomicDynamics.Body.Failure A) :
    (CPS1EnzymeBath.guards frame result).count (bathNH3 frame) = 0 := by
  cases result <;> rfl

@[simp] theorem bath_component_no_ammonia (kind : CPS1EnzymeBath.Primary.TemplateKind) :
    CPS1EnzymeBath.componentSpecies frame kind ≠ bathNH3 frame := by
  cases kind <;> simp [CPS1EnzymeBath.componentSpecies,CPS1EnzymeBath.Primary.TemplateKind.molecule,
    bathNH3,atomicNH3,atomizedNH3,localNH3,CPS1LocalChemicalExecution.molecule,
    CPS1StockRecursion.Dictionary.old]

theorem bath_nh3_inputs (reaction : CPS1EnzymeBath.Reaction frame) :
    (reaction.reactants frame).count (bathNH3 frame) = 0 := by
  cases reaction <;> simp only [CPS1EnzymeBath.Reaction.reactants,List.count_append,
    bath_guards_no_ammonia,Nat.add_zero]
  all_goals try simp [bathNH3,atomicNH3,atomizedNH3]
  rename_i state kind
  change ([CPS1EnzymeBath.componentSpecies frame kind]).count (bathNH3 frame) = 0
  simp [bath_component_no_ammonia]

theorem bath_nh3_outputs (reaction : CPS1EnzymeBath.Reaction frame) :
    (reaction.products frame).count (bathNH3 frame) = 0 := by
  cases reaction <;> simp only [CPS1EnzymeBath.Reaction.products]
  all_goals first
    | rfl
    | (split <;> simp [bathNH3,atomicNH3,atomizedNH3])

theorem bath_ammonia_preserved (program : List (CPS1EnzymeBath.Reaction frame)) (stock : CPS1EnzymeBath.Stock frame) :
    (CPS1EnzymeBath.execute frame program stock).stock.count (bathNH3 frame) = stock.count (bathNH3 frame) :=
  execute_count_preserved (CPS1EnzymeBath.Reaction.reactants frame) (CPS1EnzymeBath.Reaction.products frame)
    (bathNH3 frame) bath_nh3_inputs bath_nh3_outputs program stock

end
end CPS1SameEventFunction
