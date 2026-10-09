import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.OwnedCurrent

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1EnzymeBath.BathAccounting
variable {frame : CPS1Recycling.Frame}

theorem seed_body_no_cp {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] [])
    (complete : seed.translation.native.missing = none) :
    (CPS1AtomicDynamics.Source.resume seed.translation.generatedFrame
      (CPS1AtomicDynamics.Source.fromActual seed.translation.generatedFrame seed.atomic) []).current.stock.count
        (currentCp seed.translation.generatedFrame) = 0 := by
  change (CPS1AtomicDynamics.Source.advance seed.translation.generatedFrame
    (CPS1AtomicDynamics.Source.start seed.translation.generatedFrame seed.atomic) []).stock.count _ = 0
  rw [advance_cp_count,start_cp_count,seed_atomic_no_cp seed complete]

theorem bath_capture_no_cp (previous : CPS1AtomicDynamics.Source.Occurrence frame)
    (body : CPS1AtomicDynamics.Body.State frame)
    (held : CPS1AtomicDynamics.Source.heldBody frame previous.current.stock = some body)
    (absent : previous.current.stock.count (currentCp frame) = 0) :
    bathCP frame ∉ (CPS1EnzymeBath.Source.start frame previous).stock := by
  have counts := (CPS1EnzymeBath.Actual.capture_live_body frame previous body held).1.count_eq (bathCP frame)
  have raw := count_map_only (CPS1EnzymeBath.Source.liftMaterial frame) (currentCp frame) (bathCP frame)
    (by intro item
        dsimp only [bathCP,CPS1EnzymeBath.componentSpecies,currentCp,atomicCp,sourceCp,
          CPS1EnzymeBath.Primary.TemplateKind.molecule]
        cases item <;> simp [CPS1EnzymeBath.Source.liftMaterial]) (previous.current.stock.erase (.body body))
  have notBody : CPS1AtomicDynamics.Species.body body ≠ currentCp frame := by simp [currentCp]
  have oldZero : (previous.current.stock.erase (.body body)).count (currentCp frame) = 0 :=
    (List.count_erase_of_ne notBody.symm).trans absent
  rw [List.count_cons,raw,oldZero] at counts
  have headFalse : ((CPS1EnzymeBath.Species.joint (CPS1EnzymeBath.Joint.fromBody frame body)) == bathCP frame) = false := rfl
  rw [headFalse] at counts
  have zero : (CPS1EnzymeBath.Source.start frame previous).stock.count (bathCP frame) = 0 := by
    simpa only [Bool.false_eq_true,if_false,Nat.add_zero] using counts
  exact List.count_eq_zero.mp zero

theorem physical_bath_head {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (event : PhysicalEvent before water raw path [] [] CPS1BiologicalUpdate.noPhysicalSupply)
    (complete : event.seed.translation.native.missing = none) :
    ∃ tail, event.bath.current.stock =
      .joint (CPS1EnzymeBath.Joint.fromBody event.seed.translation.generatedFrame
        ⟨CPS1LocalChemicalExecution.Chain.initial event.seed.translation.generatedFrame,[],0⟩) :: tail ∧
      event.bath.current.pending = [.attach .carbamoylPhosphate] ∧
      bathCP event.seed.translation.generatedFrame ∉ event.bath.current.stock ∧
      event.bath.current.cut = some (bathCP event.seed.translation.generatedFrame) := by
  have atomic := event.atomicSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at atomic
  obtain ⟨rawTail,rawHead,rawPending⟩ := seed_body_head event.seed complete
  have head : event.atomic.current.stock =
      .body ⟨CPS1LocalChemicalExecution.Chain.initial event.seed.translation.generatedFrame,[],0⟩ :: rawTail := by
    rw [atomic]
    exact rawHead
  have pending : event.atomic.current.pending = [] := by rw [atomic]; exact rawPending
  have cp : event.atomic.current.stock.count (currentCp event.seed.translation.generatedFrame) = 0 := by
    rw [atomic]
    exact seed_body_no_cp event.seed complete
  have held : CPS1AtomicDynamics.Source.heldBody event.seed.translation.generatedFrame event.atomic.current.stock =
      some ⟨CPS1LocalChemicalExecution.Chain.initial event.seed.translation.generatedFrame,[],0⟩ := by rw [head]; rfl
  obtain ⟨tail,startHead,_⟩ := CPS1EnzymeBath.Partner.capture_head event.seed.translation.generatedFrame event.atomic _ held
  have captured := CPS1EnzymeBath.Actual.capture_live_body event.seed.translation.generatedFrame event.atomic _ held
  have startPending : (CPS1EnzymeBath.Source.start event.seed.translation.generatedFrame event.atomic).pending = [] := by
    rw [captured.2.2.2,pending,List.map_nil]
  have absent := bath_capture_no_cp event.atomic _ held cp
  have cut := bath_partner_cut (CPS1EnzymeBath.Source.start event.seed.translation.generatedFrame event.atomic) _ tail
    startHead captured.2.1 startPending absent
  have bath := event.bathSource
  dsimp only [CPS1BiologicalUpdate.noPhysicalSupply] at bath
  simp only [List.append_nil] at bath
  refine ⟨tail,?_,?_,?_,?_⟩
  · rw [bath]
    exact cut.1.trans startHead
  · rw [bath]
    exact cut.2.1
  · rw [bath]
    change bathCP event.seed.translation.generatedFrame ∉
      (CPS1EnzymeBath.Source.advance event.seed.translation.generatedFrame
        (CPS1EnzymeBath.Source.start event.seed.translation.generatedFrame event.atomic)
        CPS1EnzymeBath.Source.generatedPartnerProgram []).stock
    rw [cut.1]
    exact absent
  · rw [bath]
    exact cut.2.2

end
end CPS1SameEventFunction
