import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.StalledPhysical

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing
variable {frame : CPS1Recycling.Frame}

theorem mapped_absent {S T : Type} (lift : S → T) (injective : Function.Injective lift)
    (stock : List S) (item : S) (absent : item ∉ stock) : lift item ∉ stock.map lift := by
  intro present
  obtain ⟨old,held,same⟩ := List.mem_map.mp present
  exact absent ((injective same) ▸ held)

theorem electronic_lift_cp_absent (stock : CPS1EnzymeBath.Stock frame) (absent : bathCP frame ∉ stock) :
    electronicCP frame ∉ stock.map (CPS1ElectronicSource.Source.liftMaterial frame) := by
  apply List.count_eq_zero.mp
  have same := count_map_only (CPS1ElectronicSource.Source.liftMaterial frame) (bathCP frame) (electronicCP frame)
    (by intro item
        dsimp only [electronicCP,bathCP,CPS1EnzymeBath.componentSpecies]
        cases item <;> simp [CPS1ElectronicSource.Source.liftMaterial]) stock
  exact same.trans (List.count_eq_zero.mpr absent)

theorem electronic_source_stalls (previous : CPS1EnzymeBath.Source.Occurrence frame)
    (joint : CPS1EnzymeBath.Joint.State frame) (tail : CPS1EnzymeBath.Stock frame)
    (rest : List CPS1EnzymeBath.Source.RawAction)
    (head : previous.current.stock = .joint joint :: tail)
    (pending : previous.current.pending = .attach .carbamoylPhosphate :: rest)
    (absent : bathCP frame ∉ previous.current.stock) :
    (CPS1ElectronicSource.Source.resume frame (CPS1ElectronicSource.Source.fromActual frame previous) [] []).current.stock =
      previous.current.stock.map (CPS1ElectronicSource.Source.liftMaterial frame) ∧
    (CPS1ElectronicSource.Source.resume frame (CPS1ElectronicSource.Source.fromActual frame previous) [] []).current.pending =
      previous.current.pending.map CPS1ElectronicSource.Source.RawAction.old ++ [.prepare] ∧
    (CPS1ElectronicSource.Source.resume frame (CPS1ElectronicSource.Source.fromActual frame previous) [] []).current.cut = some (electronicCP frame) := by
  let stock := previous.current.stock.map (CPS1ElectronicSource.Source.liftMaterial frame)
  have rawHead : stock = .retained (.joint joint) :: tail.map (CPS1ElectronicSource.Source.liftMaterial frame) := by
    dsimp only [stock]
    rw [head,List.map_cons]
    rfl
  have rawAbsent := electronic_lift_cp_absent previous.current.stock absent
  have held : CPS1ElectronicSource.Source.heldCarrier frame stock = some (.joint joint) := by rw [rawHead]; rfl
  have present : CPS1ElectronicSource.Species.retained (.joint joint) ∈ stock := by rw [rawHead]; exact List.mem_cons_self
  have cut := electronic_program_cp_cut stock joint
    (rest.map CPS1ElectronicSource.Source.RawAction.old ++ [.prepare]) held present rawAbsent
  dsimp only [stock,electronicAttach] at cut
  have firstStock : (CPS1ElectronicSource.Source.start frame previous).stock = stock := by
    unfold CPS1ElectronicSource.Source.start
    rw [pending]
    simp only [List.map_cons,List.cons_append]
    rw [cut]
  have firstPending : (CPS1ElectronicSource.Source.start frame previous).pending =
      electronicAttach :: (rest.map CPS1ElectronicSource.Source.RawAction.old ++ [.prepare]) := by
    unfold CPS1ElectronicSource.Source.start
    rw [pending]
    simp only [List.map_cons,List.cons_append]
    rw [cut]
    rfl
  have firstHead : (CPS1ElectronicSource.Source.start frame previous).stock =
      .retained (.joint joint) :: tail.map (CPS1ElectronicSource.Source.liftMaterial frame) := firstStock.trans rawHead
  have next := electronic_advance_cp_cut (CPS1ElectronicSource.Source.start frame previous) joint _ _ firstHead firstPending
    (by rw [firstStock]; exact rawAbsent)
  refine ⟨next.1.trans firstStock,?_,next.2.2⟩
  change (CPS1ElectronicSource.Source.advance frame (CPS1ElectronicSource.Source.start frame previous) [] []).pending = _
  rw [next.2.1,firstPending,pending,List.map_cons,List.cons_append]
  rfl


theorem nuclear_source_stalls (previous : CPS1ElectronicSource.Source.Occurrence frame)
    (joint : CPS1EnzymeBath.Joint.State frame) (tail : CPS1ElectronicSource.Stock frame) (rest : List CPS1ElectronicSource.Source.RawAction)
    (head : previous.current.stock = (.retained (.joint joint) : CPS1ElectronicSource.Species frame) :: tail)
    (pending : previous.current.pending = electronicAttach :: rest) (absent : electronicCP frame ∉ previous.current.stock) :
    (CPS1QuantumNuclear.Source.resume frame (CPS1QuantumNuclear.Source.fromActual frame previous) [] []).current.stock =
      previous.current.stock.map CPS1QuantumNuclear.Species.retained ∧
    (CPS1QuantumNuclear.Source.resume frame (CPS1QuantumNuclear.Source.fromActual frame previous) [] []).current.pending =
      previous.current.pending.map CPS1QuantumNuclear.Source.RawAction.old ∧
    (CPS1QuantumNuclear.Source.resume frame (CPS1QuantumNuclear.Source.fromActual frame previous) [] []).current.cut = some (nuclearCP frame) := by
  have rawHead : (CPS1QuantumNuclear.Source.fromActual frame previous).current.stock =
      (.retained (.retained (.joint joint)) : CPS1QuantumNuclear.Species frame) :: tail.map CPS1QuantumNuclear.Species.retained := by
    change previous.current.stock.map CPS1QuantumNuclear.Species.retained = _
    rw [head,List.map_cons]
  have rawPending : (CPS1QuantumNuclear.Source.fromActual frame previous).current.pending =
      nuclearAttach :: (rest.map CPS1QuantumNuclear.Source.RawAction.old) := by
    change previous.current.pending.map CPS1QuantumNuclear.Source.RawAction.old = _
    rw [pending,List.map_cons]
    rfl
  have rawAbsent : nuclearCP frame ∉ (CPS1QuantumNuclear.Source.fromActual frame previous).current.stock :=
    mapped_absent CPS1QuantumNuclear.Species.retained (fun _ _ same => CPS1QuantumNuclear.Species.retained.inj same) _ _ absent
  have next := nuclear_advance_cp_cut (CPS1QuantumNuclear.Source.fromActual frame previous).current joint _ _ rawHead rawPending rawAbsent
  exact ⟨next.1,next.2.1,next.2.2⟩

theorem following_source_stalls (previous : CPS1QuantumNuclear.Source.Occurrence frame)
    (joint : CPS1EnzymeBath.Joint.State frame) (tail : CPS1QuantumNuclear.Stock frame) (rest : List CPS1QuantumNuclear.Source.RawAction)
    (head : previous.current.stock = (.retained (.retained (.joint joint)) : CPS1QuantumNuclear.Species frame) :: tail)
    (pending : previous.current.pending = nuclearAttach :: rest) (absent : nuclearCP frame ∉ previous.current.stock) :
    (CPS1Following.Source.resume frame (CPS1Following.Source.fromActual frame previous) [] []).current.stock =
      previous.current.stock.map CPS1Following.Species.retained ∧
    (CPS1Following.Source.resume frame (CPS1Following.Source.fromActual frame previous) [] []).current.pending =
      previous.current.pending.map CPS1Following.Source.RawAction.old ∧
    (CPS1Following.Source.resume frame (CPS1Following.Source.fromActual frame previous) [] []).current.cut = some (followingCP frame) := by
  have rawHead : (CPS1Following.Source.fromActual frame previous).current.stock =
      (.retained (.retained (.retained (.joint joint))) : CPS1Following.Species frame) :: tail.map CPS1Following.Species.retained := by
    change previous.current.stock.map CPS1Following.Species.retained = _
    rw [head,List.map_cons]
  have rawPending : (CPS1Following.Source.fromActual frame previous).current.pending =
      followingAttach :: (rest.map CPS1Following.Source.RawAction.old) := by
    change previous.current.pending.map CPS1Following.Source.RawAction.old = _
    rw [pending,List.map_cons]
    rfl
  have rawAbsent : followingCP frame ∉ (CPS1Following.Source.fromActual frame previous).current.stock :=
    mapped_absent CPS1Following.Species.retained (fun _ _ same => CPS1Following.Species.retained.inj same) _ _ absent
  have next := following_advance_cp_cut (CPS1Following.Source.fromActual frame previous).current joint _ _ rawHead rawPending rawAbsent
  exact ⟨next.1,next.2.1,next.2.2⟩

theorem molecular_source_stalls (previous : CPS1Following.Source.Occurrence frame)
    (joint : CPS1EnzymeBath.Joint.State frame) (tail : CPS1Following.Stock frame) (rest : List CPS1Following.Source.RawAction)
    (head : previous.current.stock = (.retained (.retained (.retained (.joint joint))) : CPS1Following.Species frame) :: tail)
    (pending : previous.current.pending = followingAttach :: rest) (absent : followingCP frame ∉ previous.current.stock) :
    (CPS1MolecularFrame.Source.resume frame (CPS1MolecularFrame.Source.fromActual frame previous) [] []).current.stock =
      previous.current.stock.map CPS1MolecularFrame.Species.retained ∧
    (CPS1MolecularFrame.Source.resume frame (CPS1MolecularFrame.Source.fromActual frame previous) [] []).current.pending =
      previous.current.pending.map CPS1MolecularFrame.Source.RawAction.old ++ [.adopt] ∧
    (CPS1MolecularFrame.Source.resume frame (CPS1MolecularFrame.Source.fromActual frame previous) [] []).current.cut = some (molecularCP frame) := by
  have rawHead : (CPS1MolecularFrame.Source.fromActual frame previous).current.stock =
      (.retained (.retained (.retained (.retained (.joint joint)))) : CPS1MolecularFrame.Species frame) :: tail.map CPS1MolecularFrame.Species.retained := by
    change previous.current.stock.map CPS1MolecularFrame.Species.retained = _
    rw [head,List.map_cons]
  have rawPending : (CPS1MolecularFrame.Source.fromActual frame previous).current.pending =
      molecularAttach :: (rest.map CPS1MolecularFrame.Source.RawAction.old ++ [.adopt]) := by
    change previous.current.pending.map CPS1MolecularFrame.Source.RawAction.old ++ [.adopt] = _
    rw [pending,List.map_cons]
    rfl
  have rawAbsent : molecularCP frame ∉ (CPS1MolecularFrame.Source.fromActual frame previous).current.stock :=
    mapped_absent CPS1MolecularFrame.Species.retained (fun _ _ same => CPS1MolecularFrame.Species.retained.inj same) _ _ absent
  have next := molecular_advance_cp_cut (CPS1MolecularFrame.Source.fromActual frame previous).current joint _ _ rawHead rawPending rawAbsent
  exact ⟨next.1,next.2.1,next.2.2⟩

theorem deformed_source_stalls (previous : CPS1MolecularFrame.Source.Occurrence frame)
    (joint : CPS1EnzymeBath.Joint.State frame) (tail : CPS1MolecularFrame.Stock frame) (rest : List CPS1MolecularFrame.Source.RawAction)
    (head : previous.current.stock = (.retained (.retained (.retained (.retained (.joint joint)))) : CPS1MolecularFrame.Species frame) :: tail)
    (pending : previous.current.pending = molecularAttach :: rest) (absent : molecularCP frame ∉ previous.current.stock) :
    (CPS1Deformation.Source.resume frame (CPS1Deformation.Source.fromActual frame previous) [] []).current.stock =
      previous.current.stock.map CPS1Deformation.Species.retained ∧
    (CPS1Deformation.Source.resume frame (CPS1Deformation.Source.fromActual frame previous) [] []).current.pending =
      previous.current.pending.map CPS1Deformation.Source.RawAction.old ++ [.adopt] ∧
    (CPS1Deformation.Source.resume frame (CPS1Deformation.Source.fromActual frame previous) [] []).current.cut = some (deformedCP frame) := by
  have rawHead : (CPS1Deformation.Source.fromActual frame previous).current.stock =
      (.retained (.retained (.retained (.retained (.retained (.joint joint))))) : CPS1Deformation.Species frame) :: tail.map CPS1Deformation.Species.retained := by
    change previous.current.stock.map CPS1Deformation.Species.retained = _
    rw [head,List.map_cons]
  have rawPending : (CPS1Deformation.Source.fromActual frame previous).current.pending =
      deformedAttach :: (rest.map CPS1Deformation.Source.RawAction.old ++ [.adopt]) := by
    change previous.current.pending.map CPS1Deformation.Source.RawAction.old ++ [.adopt] = _
    rw [pending,List.map_cons]
    rfl
  have rawAbsent : deformedCP frame ∉ (CPS1Deformation.Source.fromActual frame previous).current.stock :=
    mapped_absent CPS1Deformation.Species.retained (fun _ _ same => CPS1Deformation.Species.retained.inj same) _ _ absent
  have next := deformed_advance_cp_cut (CPS1Deformation.Source.fromActual frame previous).current joint _ _ rawHead rawPending rawAbsent
  exact ⟨next.1,next.2.1,next.2.2⟩

end
end CPS1SameEventFunction
