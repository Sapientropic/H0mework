import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Prefix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution CPS1BiologicalUpdate CPS1LiveEditing CPS1ReactiveSourceEntry

private theorem empty_programme_beginning {frame : CPS1Recycling.Frame}
    (old : CPS1Deformation.Source.Occurrence frame) :
    (programmeFromOld old [] [] [] 0 (([],[]),[]) 0).beginning.native.current =
      CPS1ReactiveField.next (CPS1ReactiveField.start old) [] [] [] := by
  have actual := initial_entry_current old [] [] []
  unfold programmeFromOld
  generalize selected : enterFromOld old [] [] [] = entered
  rw [selected] at actual
  cases entered with
  | residual cursor failure =>
    change cursor.native.current = _
    simpa only [entryCursor] using actual
  | admitted before =>
    change (match reenter (renewEntered before 0).after (([],[]),[]) with
      | .residual chemical failure => Programme.chemicalResidual before (renewEntered before 0) chemical failure
      | .admitted chemical => Programme.cycled before (renewEntered before 0) chemical (renewEntered chemical 0)).beginning.native.current = _
    cases reenter (renewEntered before 0).after (([],[]),[]) <;>
      simpa only [entryCursor,Programme.beginning] using actual

theorem empty_programme_old {frame : CPS1Recycling.Frame}
    (old : CPS1Deformation.Source.Occurrence frame) :
    (programmeFromOld old [] [] [] 0 (([],[]),[]) 0).current.native.current.old = old := by
  let programme := programmeFromOld old [] [] [] 0 (([],[]),[]) 0
  have law := programme_whole programme (([],[]),[])
    (programme_from_old_chemical old [] [] [] 0 (([],[]),[]) 0)
  exact law.1.trans (congrArg CPS1ReactiveField.Occurrence.old (empty_programme_beginning old))

private theorem empty_twice_stock {frame : CPS1Recycling.Frame}
    (old : CPS1Deformation.Source.Occurrence frame) :
    (CPS1AddressedHydrolysis.Atomic.next
      (CPS1ReactiveField.next (CPS1ReactiveField.start old) [] [] []).ingress.atomic [] []).source.stock =
      (CPS1ReactiveField.enzymeView old).map CPS1AddressedChemicalReaction.Material.inherited := by
  change (CPS1AddressedChemicalReaction.Source.next
    (CPS1AddressedChemicalReaction.Source.next
      (CPS1AddressedChemicalReaction.Source.start (CPS1ReactiveField.freshIngress old)) [] []) [] []).stock = _
  simp only [CPS1AddressedChemicalReaction.Source.next,CPS1AddressedChemicalReaction.Source.execution,
    CPS1AddressedChemicalReaction.Source.requestedProgram,CPS1AddressedChemicalReaction.Source.available,
    CPS1AddressedChemicalReaction.Source.packet,CPS1AddressedChemicalReaction.Source.start,
    CPS1ReactiveField.freshIngress,CPS1LocalChemicalExecution.Source.localProgram,
    List.map_nil,List.flatMap_nil,List.nil_append,List.append_nil,List.drop_nil,
    CPS1AddressedChemicalReaction.rawPacket,List.zipIdx_nil,CPS1AddressedChemicalReaction.run_nil]

private theorem old_dna_reader {frame : CPS1Recycling.Frame} (item : CPS1Deformation.Species frame) :
    (liveResource? (.old item)).bind nativeDNA? = deformedDNA? item := by
  cases item
  repeat first
    | rfl
    | (rename_i inherited; cases inherited)

theorem empty_programme_genome {frame : CPS1Recycling.Frame}
    (old : CPS1Deformation.Source.Occurrence frame) :
    CPS1Deamination.ExecutionReadout.readDNA
      (liveResources (programmeFromOld old [] [] [] 0 (([],[]),[]) 0).current.native.current) =
      (old.current.stock.filterMap deformedDNA?).head? := by
  let programme := programmeFromOld old [] [] [] 0 (([],[]),[]) 0
  have law := programme_whole programme (([],[]),[])
    (programme_from_old_chemical old [] [] [] 0 (([],[]),[]) 0)
  have stock := congrArg (fun value : CPS1AddressedHydrolysis.Atomic.Occurrence frame => value.source.stock) law.2.1
  rw [empty_programme_beginning old] at stock
  rw [empty_twice_stock old] at stock
  have residual := old_residual_genome programme.current.native.current
  rw [empty_programme_old old] at residual
  change ((CPS1ReactiveField.liveStock programme.current.native.current).filterMap liveResource? |>.filterMap nativeDNA?).head? = _
  rw [List.filterMap_filterMap]
  unfold CPS1ReactiveField.liveStock
  simp only [List.filterMap_append,List.filterMap_map,Function.comp_def,old_dna_reader]
  rw [residual,stock]
  have fresh : ((CPS1ReactiveField.enzymeView old).map CPS1AddressedChemicalReaction.Material.inherited).filterMap
      (fun item => (liveResource? (.reactive item)).bind nativeDNA?) = [] := by
    unfold CPS1ReactiveField.enzymeView
    split <;> rfl
  rw [fresh,List.append_nil]

theorem registered_before_old : registeredBefore.native.current.old = registeredOld := by
  simpa only [registeredBefore,registeredProgrammeData] using empty_programme_old registeredOld

theorem registered_before_genome :
    CPS1Deamination.ExecutionReadout.readDNA (liveResources registeredBefore.native.current) =
      (registeredOld.current.stock.filterMap deformedDNA?).head? := by
  simpa only [registeredBefore,registeredProgrammeData] using empty_programme_genome registeredOld

theorem registered_before_editing :
    (CPS1ReactiveField.editingSource registeredBefore.native.current.old).editing =
      CPS1Deamination.Continuation.sourceContinuation registeredEdits registeredWater registeredAdditional := by
  exact (congrArg (fun old => (CPS1ReactiveField.editingSource old).editing) registered_before_old).trans registered_editing_actual

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
