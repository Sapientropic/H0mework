import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeGatherSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeCPProjection
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativeCarbamoyl NativeGatherConsumers

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}

def cpSourceOrder : Fin 10 → Fin 10 := ![5,9,4,6,3,7,0,8,1,2]

theorem cp_source_order_surjective : Function.Surjective cpSourceOrder := by decide +kernel

theorem cp_atoms_length (paid : SourceGeneratedPaidReturn source current) :
    (cpSourceAtoms paid.parent.products.serial).length = 10 := rfl

def cpAtom (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) : Atom cursor :=
  (cpSourceAtoms paid.parent.products.serial).get
    ⟨(cpSourceOrder ordinal).val,by rw [cp_atoms_length]; exact (cpSourceOrder ordinal).isLt⟩

def templateAtom (ordinal : Fin 10) : CPS1EnzymeBath.Primary.Atom :=
  CPS1EnzymeBath.Primary.carbamoylPhosphate.atoms.get ⟨ordinal.val,by exact ordinal.isLt⟩

def templateDescriptor (ordinal : Fin 10) : Graph.Atom :=
  (CPS1EnzymeBath.Joint.bathAtom ⟨0,.carbamoylPhosphate⟩ (templateAtom ordinal)).descriptor

theorem cp_index (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    cpIndex (cpAtom paid ordinal).origin = ordinal.val := by
  fin_cases ordinal <;> rfl

theorem cp_atom_held (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    cpAtom paid ordinal ∈ cpSourceAtoms paid.parent.products.serial := List.get_mem _ _

theorem cp_source_held (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    cpAtom paid ordinal ∈ source.atoms :=
  cp_source_atoms_held paid.parent.products.serial _ (cp_atom_held paid ordinal)

theorem cp_element (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    (cpAtom paid ordinal).descriptor.source.element = (templateAtom ordinal).element := by
  fin_cases ordinal <;> rfl

theorem cp_charge (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    (cpAtom paid ordinal).descriptor.source.charge = (templateAtom ordinal).charge := by
  fin_cases ordinal <;> rfl

theorem cp_product_charge (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    paid.parent.products.serial.after.graph.formalCharge (cpAtom paid ordinal).origin =
      (templateAtom ordinal).charge :=
  (cp_atom_charge paid.parent.products.serial _ (cp_atom_held paid ordinal)).trans (cp_charge paid ordinal)

theorem cp_electrons (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    Charged.electrons (cpAtom paid ordinal).descriptor.source =
      Charged.electrons (templateDescriptor ordinal).source := by
  fin_cases ordinal <;> rfl

theorem cp_origin_injective (paid : SourceGeneratedPaidReturn source current) :
    Function.Injective (fun ordinal => (cpAtom paid ordinal).origin) := by
  intro first second same
  apply Fin.ext
  exact (cp_index paid first).symm.trans ((congrArg cpIndex same).trans (cp_index paid second))

theorem cp_coverage (paid : SourceGeneratedPaidReturn source current)
    (atom : Atom cursor) (held : atom ∈ cpSourceAtoms paid.parent.products.serial) :
    ∃ ordinal : Fin 10, cpAtom paid ordinal = atom := by
  obtain ⟨slot,found⟩ := List.getElem?_of_mem held
  have bound := (List.getElem?_eq_some_iff.mp found).1
  let index : Fin 10 := ⟨slot,by rw [← cp_atoms_length paid]; exact bound⟩
  obtain ⟨ordinal,ordered⟩ := cp_source_order_surjective index
  refine ⟨ordinal,?_⟩
  unfold cpAtom
  simp only [ordered]
  exact (List.getElem?_eq_some_iff.mp found).2

private theorem cp_slot_exists (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    ∃ slot : Fin source.atoms.length, source.atoms.get slot = cpAtom paid ordinal := by
  obtain ⟨slot,found⟩ := List.getElem?_of_mem (cp_source_held paid ordinal)
  exact ⟨⟨slot,(List.getElem?_eq_some_iff.mp found).1⟩,(List.getElem?_eq_some_iff.mp found).2⟩

def cpSlot (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) : Fin source.atoms.length :=
  Classical.choose (cp_slot_exists paid ordinal)

theorem cp_slot_actual (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    source.atoms.get (cpSlot paid ordinal) = cpAtom paid ordinal :=
  Classical.choose_spec (cp_slot_exists paid ordinal)

theorem cp_slot_injective (paid : SourceGeneratedPaidReturn source current) : Function.Injective (cpSlot paid) := by
  intro first second same
  apply cp_origin_injective paid
  change (cpAtom paid first).origin = (cpAtom paid second).origin
  rw [← cp_slot_actual paid first,← cp_slot_actual paid second,same]

private theorem cp_indexed (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    (cpAtom paid ordinal,(cpSlot paid ordinal).val) ∈ source.atoms.zipIdx := by
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  simpa only [← cp_slot_actual paid ordinal,List.get_eq_getElem] using
    List.getElem?_eq_getElem (cpSlot paid ordinal).isLt

private theorem source_particle_table :
    commonParticles before.packet.source raw.fuel = source.atoms.zipIdx.flatMap
      (fun entry => Charged.atomParticles (entry.1.descriptor,entry.2)) := by
  rw [source.atomSource]
  rfl

def cpNucleusParticle (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) : Charged.Particle :=
  ⟨.nucleus (cpSlot paid ordinal).val,(cpAtom paid ordinal).descriptor,
    (Charged.atomicNumber (cpAtom paid ordinal).descriptor.source.element : ℤ)⟩

def cpElectronParticle (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10)
    (orbital : Fin (Charged.electrons (templateDescriptor ordinal).source)) : Charged.Particle :=
  ⟨.electron (cpSlot paid ordinal).val orbital.val,(cpAtom paid ordinal).descriptor,-1⟩

private theorem nucleus_particle_held (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    cpNucleusParticle paid ordinal ∈ commonParticles before.packet.source raw.fuel := by
  rw [source_particle_table (source := source)]
  exact List.mem_flatMap.mpr ⟨(cpAtom paid ordinal,(cpSlot paid ordinal).val),cp_indexed paid ordinal,
    List.mem_cons_self⟩

private theorem electron_particle_held (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10)
    (orbital : Fin (Charged.electrons (templateDescriptor ordinal).source)) :
    cpElectronParticle paid ordinal orbital ∈ commonParticles before.packet.source raw.fuel := by
  have bound : orbital.val < Charged.electrons (cpAtom paid ordinal).descriptor.source := by
    rw [cp_electrons]
    exact orbital.isLt
  rw [source_particle_table (source := source)]
  apply List.mem_flatMap.mpr
  refine ⟨(cpAtom paid ordinal,(cpSlot paid ordinal).val),cp_indexed paid ordinal,?_⟩
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨orbital.val,List.mem_range.mpr bound,rfl⟩)

private theorem physical_particle_found (paid : SourceGeneratedPaidReturn source current) (particle : Charged.Particle)
    (held : particle ∈ commonParticles before.packet.source raw.fuel) :
    ∃ node ∈ paid.physical.pose, node.particle = particle := by
  have whole := paid.physical.particles.trans (current_particles_source source current)
  rw [← whole] at held
  exact List.mem_map.mp held

def cpNucleus (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) : Body.Node :=
  Classical.choose (physical_particle_found paid _ (nucleus_particle_held paid ordinal))

theorem cp_nucleus_actual (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    cpNucleus paid ordinal ∈ paid.physical.pose ∧
      (cpNucleus paid ordinal).particle = cpNucleusParticle paid ordinal :=
  Classical.choose_spec (physical_particle_found paid _ (nucleus_particle_held paid ordinal))

def cpElectron (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10)
    (orbital : Fin (Charged.electrons (templateDescriptor ordinal).source)) : Body.Node :=
  Classical.choose (physical_particle_found paid _ (electron_particle_held paid ordinal orbital))

theorem cp_electron_actual (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10)
    (orbital : Fin (Charged.electrons (templateDescriptor ordinal).source)) :
    cpElectron paid ordinal orbital ∈ paid.physical.pose ∧
      (cpElectron paid ordinal orbital).particle = cpElectronParticle paid ordinal orbital :=
  Classical.choose_spec (physical_particle_found paid _ (electron_particle_held paid ordinal orbital))

theorem cp_nucleus_positive (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    0 < (cpNucleus paid ordinal).row.inertia :=
  paid.physical.inertia _ (cp_nucleus_actual paid ordinal).1

theorem cp_electron_mass (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10)
    (orbital : Fin (Charged.electrons (templateDescriptor ordinal).source)) :
    (cpElectron paid ordinal orbital).row.inertia = source.electronInertia := by
  have uniform := paid_uniform_electrons paid _ (cp_electron_actual paid ordinal orbital).1
  rw [(cp_electron_actual paid ordinal orbital).2] at uniform
  exact uniform

theorem cp_nucleus_source_mass (paid : SourceGeneratedPaidReturn source current) (ordinal : Fin 10) :
    ∃ original ∈ source.nodes, original.particle = (cpNucleus paid ordinal).particle ∧
      original.row.inertia = (cpNucleus paid ordinal).row.inertia := by
  have held : particleMass (cpNucleus paid ordinal) ∈ source.nodes.map particleMass :=
    paid_particle_mass paid ▸ List.mem_map_of_mem (cp_nucleus_actual paid ordinal).1
  obtain ⟨original,originalHeld,same⟩ := List.mem_map.mp held
  exact ⟨original,originalHeld,congrArg Prod.fst same,congrArg Prod.snd same⟩

end
end CPS1MaterialIncidence.NativeCPProjection
