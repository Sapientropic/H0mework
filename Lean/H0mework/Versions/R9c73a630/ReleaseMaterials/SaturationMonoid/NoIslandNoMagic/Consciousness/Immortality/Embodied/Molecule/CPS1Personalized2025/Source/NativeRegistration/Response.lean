import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Renew
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalResponded
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.Whole
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Ingress

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1SameEventFunction

noncomputable def responseIndex {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (selected : Classical.sourceAt cursor = .ok source)
    (empty : source.owned.chainRows = []) : Nat := by
  classical
  exact Nat.find (Classical.measured_public_responded source selected empty)

noncomputable def indexedResponseRaw {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (selected : Classical.sourceAt cursor = .ok source)
    (empty : source.owned.chainRows = []) : Classical.Raw :=
  source.measurementRaw 1 ((1/2 : ℝ)^responseIndex source selected empty)

theorem indexed_response_actual {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (selected : Classical.sourceAt cursor = .ok source)
    (empty : source.owned.chainRows = []) :
    ∃ before : Classical.Current cursor (indexedResponseRaw source selected empty),
      ∃ step : Classical.NativeStep before (indexedResponseRaw source selected empty).time,
        Classical.fromCursor cursor (indexedResponseRaw source selected empty) = .responded before step ∧
        ∀ node ∈ step.next.nodes, node.row.inertia = 1 := by
  classical
  obtain ⟨step,actual⟩ := Nat.find_spec (Classical.measured_public_responded source selected empty)
  exact ⟨Classical.measurementCurrent source empty 1 ((1/2 : ℝ)^responseIndex source selected empty),
    step,actual,CPS1PhosphorylExchange.measured_post_unit_inertia source empty 1 _ step⟩

noncomputable def registeredQuantumRaw : Raw := ⟨[],0,0⟩

noncomputable def responseRawFromRepair {body : Body} (repair : LocalRepairDisposition body) : WholeRaw := by
  classical
  exact match repair with
    | .residual _ _ => ⟨registeredQuantumRaw,⟨[],0,0⟩⟩
    | .repaired receipt =>
      match selected : Classical.sourceAt receipt.nextBody.current.2 with
      | .error _ => ⟨registeredQuantumRaw,⟨[],0,0⟩⟩
      | .ok source =>
        if empty : source.owned.chainRows = [] then
          ⟨registeredQuantumRaw,indexedResponseRaw source selected empty⟩
        else ⟨registeredQuantumRaw,⟨[],0,0⟩⟩

private theorem response_raw_selected {body : Body} (receipt : LocalRepairReceipt body)
    (source : Classical.Source receipt.nextBody.current.2)
    (selected : Classical.sourceAt receipt.nextBody.current.2 = .ok source)
    (empty : source.owned.chainRows = []) :
    responseRawFromRepair (.repaired receipt) = ⟨registeredQuantumRaw,indexedResponseRaw source selected empty⟩ := by
  unfold responseRawFromRepair
  dsimp only
  split
  · rename_i failure actual
    have impossible := selected.symm.trans actual
    cases impossible
  · rename_i found actual
    have same : found = source := Except.ok.inj (actual.symm.trans selected)
    subst found
    split
    · rfl
    · rename_i rejected
      exact False.elim (rejected empty)

noncomputable def registeredResponse : WholeRaw :=
  responseRawFromRepair (repairWhole registeredWhole registeredSupply)

theorem registered_response_actual
    (receipt : LocalRepairReceipt (initialBody ⟨registeredFrame,registeredBefore⟩))
    (selected : repairWhole registeredWhole registeredSupply = .repaired receipt) :
    ∃ before : Classical.Current receipt.nextBody.current.2 registeredResponse.particles,
      ∃ step : Classical.NativeStep before registeredResponse.particles.time,
        (wholeResponse (.repaired receipt) registeredResponse).particles = .responded before step ∧
        ∀ node ∈ step.next.nodes, node.row.inertia = 1 := by
  obtain ⟨source,actual,empty⟩ := registered_repaired_source_ready receipt selected
  have raw : registeredResponse = ⟨registeredQuantumRaw,indexedResponseRaw source actual empty⟩ := by
    unfold registeredResponse
    rw [selected]
    exact response_raw_selected receipt source actual empty
  rw [raw]
  exact indexed_response_actual source actual empty

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
