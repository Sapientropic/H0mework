import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.OwnedDeformed
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativePaidReturn

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativePaidPositive
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1SameEventFunction
open NativePaidEvent
variable {frame : CPS1Recycling.Frame}

def sourceJoint (frame : CPS1Recycling.Frame) : CPS1EnzymeBath.Joint.State frame :=
  CPS1EnzymeBath.Joint.fromBody frame ⟨CPS1LocalChemicalExecution.Chain.initial frame,[],0⟩

theorem physical_deformed_source {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (event : PhysicalEvent before water raw path [] [] noPhysicalSupply)
    (complete : event.seed.translation.native.missing = none) :
    ∃ tail, event.deformation.current.stock = wrappedJoint (sourceJoint event.seed.translation.generatedFrame) :: tail ∧
      event.deformation.current.pending = deformedAttach :: [.old (.old (.old (.old .prepare))),.old .adopt,.adopt] ∧
      event.deformation.current.cut = some (deformedCP event.seed.translation.generatedFrame) ∧
      deformedCP event.seed.translation.generatedFrame ∉ event.deformation.current.stock := by
  obtain ⟨bathTail,bathHead,bathPending,bathAbsent,_⟩ := physical_bath_head event complete
  let joint := sourceJoint event.seed.translation.generatedFrame
  have electronicSource := event.electronicSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at electronicSource
  have electronicFacts := electronic_source_stalls event.bath joint bathTail [] bathHead bathPending bathAbsent
  have electronicStock : event.electronic.current.stock = event.bath.current.stock.map
      (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame) := by
    rw [electronicSource]
    exact electronicFacts.1
  have electronicHead : event.electronic.current.stock = .retained (.joint joint) ::
      bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame) := by
    rw [electronicStock,bathHead,List.map_cons]
    rfl
  have electronicPending : event.electronic.current.pending = electronicAttach :: [.prepare] := by
    rw [electronicSource,electronicFacts.2.1,bathPending]
    rfl
  have electronicAbsent : electronicCP event.seed.translation.generatedFrame ∉ event.electronic.current.stock := by
    rw [electronicStock]
    exact electronic_lift_cp_absent _ bathAbsent
  have nuclearSource := event.nuclearSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at nuclearSource
  have nuclearFacts := nuclear_source_stalls event.electronic joint (bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)) ([.prepare])
    electronicHead electronicPending electronicAbsent
  have nuclearStock : event.nuclear.current.stock = event.electronic.current.stock.map CPS1QuantumNuclear.Species.retained := by
    rw [nuclearSource]
    exact nuclearFacts.1
  have nuclearHead : event.nuclear.current.stock = (.retained (.retained (.joint joint)) : CPS1QuantumNuclear.Species event.seed.translation.generatedFrame) ::
      (bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained := by
    rw [nuclearStock,electronicHead,List.map_cons]
  have nuclearPending : event.nuclear.current.pending = nuclearAttach :: [.old .prepare] := by
    rw [nuclearSource,nuclearFacts.2.1,electronicPending]
    rfl
  have nuclearAbsent : nuclearCP event.seed.translation.generatedFrame ∉ event.nuclear.current.stock := by
    rw [nuclearStock]
    exact mapped_absent CPS1QuantumNuclear.Species.retained (fun _ _ same => CPS1QuantumNuclear.Species.retained.inj same) _ _ electronicAbsent
  have followingSource := event.followingSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at followingSource
  have followingFacts := following_source_stalls event.nuclear joint ((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained) ([.old .prepare])
    nuclearHead nuclearPending nuclearAbsent
  have followingStock : event.following.current.stock = event.nuclear.current.stock.map CPS1Following.Species.retained := by
    rw [followingSource]
    exact followingFacts.1
  have followingHead : event.following.current.stock = (.retained (.retained (.retained (.joint joint))) : CPS1Following.Species event.seed.translation.generatedFrame) ::
      ((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained).map CPS1Following.Species.retained := by
    rw [followingStock,nuclearHead,List.map_cons]
  have followingPending : event.following.current.pending = followingAttach :: [.old (.old .prepare)] := by
    rw [followingSource,followingFacts.2.1,nuclearPending]
    rfl
  have followingAbsent : followingCP event.seed.translation.generatedFrame ∉ event.following.current.stock := by
    rw [followingStock]
    exact mapped_absent CPS1Following.Species.retained (fun _ _ same => CPS1Following.Species.retained.inj same) _ _ nuclearAbsent
  have molecularSource := event.molecularSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at molecularSource
  have molecularFacts := molecular_source_stalls event.following joint (((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained).map CPS1Following.Species.retained) ([.old (.old .prepare)])
    followingHead followingPending followingAbsent
  have molecularStock : event.molecular.current.stock = event.following.current.stock.map CPS1MolecularFrame.Species.retained := by
    rw [molecularSource]
    exact molecularFacts.1
  have molecularHead : event.molecular.current.stock = (.retained (.retained (.retained (.retained (.joint joint)))) : CPS1MolecularFrame.Species event.seed.translation.generatedFrame) ::
      (((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained).map CPS1Following.Species.retained).map CPS1MolecularFrame.Species.retained := by
    rw [molecularStock,followingHead,List.map_cons]
  have molecularPending : event.molecular.current.pending = molecularAttach :: [.old (.old (.old .prepare)),.adopt] := by
    rw [molecularSource,molecularFacts.2.1,followingPending]
    rfl
  have molecularAbsent : molecularCP event.seed.translation.generatedFrame ∉ event.molecular.current.stock := by
    rw [molecularStock]
    exact mapped_absent CPS1MolecularFrame.Species.retained (fun _ _ same => CPS1MolecularFrame.Species.retained.inj same) _ _ followingAbsent
  have deformedSource := event.deformationSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at deformedSource
  have deformedFacts := deformed_source_stalls event.molecular joint ((((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained).map CPS1Following.Species.retained).map CPS1MolecularFrame.Species.retained) ([.old (.old (.old .prepare)),.adopt])
    molecularHead molecularPending molecularAbsent
  have deformedStock : event.deformation.current.stock = event.molecular.current.stock.map CPS1Deformation.Species.retained := by
    rw [deformedSource]
    exact deformedFacts.1
  have deformedHead : event.deformation.current.stock = (.retained (.retained (.retained (.retained (.retained (.joint joint))))) : CPS1Deformation.Species event.seed.translation.generatedFrame) ::
      ((((bathTail.map (CPS1ElectronicSource.Source.liftMaterial event.seed.translation.generatedFrame)).map CPS1QuantumNuclear.Species.retained).map CPS1Following.Species.retained).map CPS1MolecularFrame.Species.retained).map CPS1Deformation.Species.retained := by
    rw [deformedStock,molecularHead,List.map_cons]
  have deformedPending : event.deformation.current.pending = deformedAttach :: [.old (.old (.old (.old .prepare))),.old .adopt,.adopt] := by
    rw [deformedSource,deformedFacts.2.1,molecularPending]
    rfl
  have deformedAbsent : deformedCP event.seed.translation.generatedFrame ∉ event.deformation.current.stock := by
    rw [deformedStock]
    exact mapped_absent CPS1Deformation.Species.retained (fun _ _ same => CPS1Deformation.Species.retained.inj same) _ _ molecularAbsent
  refine ⟨_,deformedHead,deformedPending,?_,deformedAbsent⟩
  rw [deformedSource]
  exact deformedFacts.2.2

end
end CPS1MaterialIncidence.NativePaidPositive
