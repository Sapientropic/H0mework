import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.OwnedBirth

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1SameEventFunction.Classical
variable {frame : CPS1Recycling.Frame}

def initialOwner (f : CPS1Recycling.Frame) : OwnedChain f := ⟨CPS1LocalChemicalExecution.Chain.initial f,[]⟩

theorem seed_body_owned {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] [])
    (complete : seed.translation.native.missing = none) :
    ((CPS1AtomicDynamics.Source.resume seed.translation.generatedFrame
      (CPS1AtomicDynamics.Source.fromActual seed.translation.generatedFrame seed.atomic) []).current.stock).filterMap ownedBody? =
        [initialOwner seed.translation.generatedFrame] := by
  obtain ⟨surplus,head,retained⟩ := seed_atomic_head seed complete
  have held : CPS1AtomicDynamics.Source.heldAtomic seed.translation.generatedFrame seed.atomic.current.stock =
      some (CPS1LocalChemicalExecution.Chain.initial seed.translation.generatedFrame) := by rw [head]; rfl
  have captured := CPS1AtomicDynamics.Source.start_current seed.translation.generatedFrame seed.atomic _ held
  have unchanged := atomic_advance_empty (CPS1AtomicDynamics.Source.start seed.translation.generatedFrame seed.atomic) captured.2.1 rfl
  change ((CPS1AtomicDynamics.Source.advance seed.translation.generatedFrame
    (CPS1AtomicDynamics.Source.start seed.translation.generatedFrame seed.atomic) []).stock).filterMap ownedBody? = _
  rw [unchanged.1]
  have stockHead : (CPS1AtomicDynamics.Source.start seed.translation.generatedFrame seed.atomic).stock =
      .body ⟨CPS1LocalChemicalExecution.Chain.initial seed.translation.generatedFrame,[],0⟩ :: surplus.map CPS1AtomicDynamics.Species.retained := by
    unfold CPS1AtomicDynamics.Source.start
    rw [held,head]
    simp [CPS1AtomicDynamics.execute,Inventory.execute,Inventory.fire,CPS1AtomicDynamics.Reaction.reactants,
      CPS1AtomicDynamics.Reaction.products,Inventory.consume]
  have empty : (surplus.map CPS1AtomicDynamics.Species.retained).filterMap ownedBody? = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro item present
    obtain ⟨atomized,held,rfl⟩ := List.mem_map.mp present
    obtain ⟨localMaterial,rfl⟩ := retained atomized held
    rfl
  rw [stockHead,List.filterMap_cons]
  change initialOwner seed.translation.generatedFrame :: _ = _
  rw [empty]

theorem bath_lift_owned (item : CPS1AtomicDynamics.Species frame) :
    ownedBath? (CPS1EnzymeBath.Source.liftMaterial frame item) = ownedBody? item := by cases item <;> rfl

theorem electronic_lift_owned (item : CPS1EnzymeBath.Species frame) :
    ownedElectronic? (CPS1ElectronicSource.Source.liftMaterial frame item) = ownedBath? item := by cases item <;> rfl

theorem physical_bath_owned {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (event : PhysicalEvent before water raw path [] [] CPS1BiologicalUpdate.noPhysicalSupply)
    (complete : event.seed.translation.native.missing = none) :
    event.bath.current.stock.filterMap ownedBath? = [initialOwner event.seed.translation.generatedFrame] := by
  have atomic := event.atomicSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at atomic
  obtain ⟨bodyTail,bodyHead,_⟩ := seed_body_head event.seed complete
  have head : event.atomic.current.stock =
      .body ⟨CPS1LocalChemicalExecution.Chain.initial event.seed.translation.generatedFrame,[],0⟩ :: bodyTail := by
    rw [atomic]
    exact bodyHead
  have owned : event.atomic.current.stock.filterMap ownedBody? = [initialOwner event.seed.translation.generatedFrame] := by
    rw [atomic]
    exact seed_body_owned event.seed complete
  rw [head,List.filterMap_cons] at owned
  have tailEmpty : bodyTail.filterMap ownedBody? = [] := List.cons.inj owned |>.2
  have held : CPS1AtomicDynamics.Source.heldBody event.seed.translation.generatedFrame event.atomic.current.stock =
      some ⟨CPS1LocalChemicalExecution.Chain.initial event.seed.translation.generatedFrame,[],0⟩ := by rw [head]; rfl
  have captured := CPS1EnzymeBath.Actual.capture_live_body event.seed.translation.generatedFrame event.atomic _ held
  have filtered := captured.1.filterMap ownedBath?
  have previous : (event.atomic.current.stock.erase
      (.body ⟨CPS1LocalChemicalExecution.Chain.initial event.seed.translation.generatedFrame,[],0⟩)).filterMap ownedBody? = [] := by
    rw [head,List.erase_cons_head]
    exact tailEmpty
  simp only [List.filterMap_cons,List.filterMap_map,Function.comp_def,bath_lift_owned,previous] at filtered
  have captureOwned : (CPS1EnzymeBath.Source.start event.seed.translation.generatedFrame event.atomic).stock.filterMap ownedBath? =
      [initialOwner event.seed.translation.generatedFrame] := List.perm_singleton.mp filtered
  have startHead := CPS1EnzymeBath.Partner.capture_head event.seed.translation.generatedFrame event.atomic _ held
  obtain ⟨startTail,sourceHead,_⟩ := startHead
  have startAbsent := bath_capture_no_cp event.atomic _ held (by
    rw [atomic]
    exact seed_body_no_cp event.seed complete)
  have startPending : (CPS1EnzymeBath.Source.start event.seed.translation.generatedFrame event.atomic).pending = [] := by
    obtain ⟨_,_,pending⟩ := seed_body_head event.seed complete
    rw [captured.2.2.2,atomic,pending,List.map_nil]
  have cut := bath_partner_cut (CPS1EnzymeBath.Source.start event.seed.translation.generatedFrame event.atomic) _ startTail
    sourceHead captured.2.1 startPending startAbsent
  have bath := event.bathSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at bath
  simp only [List.append_nil] at bath
  rw [bath]
  change ((CPS1EnzymeBath.Source.advance event.seed.translation.generatedFrame
    (CPS1EnzymeBath.Source.start event.seed.translation.generatedFrame event.atomic)
    CPS1EnzymeBath.Source.generatedPartnerProgram []).stock).filterMap ownedBath? = _
  rw [cut.1]
  exact captureOwned

end
end CPS1SameEventFunction
