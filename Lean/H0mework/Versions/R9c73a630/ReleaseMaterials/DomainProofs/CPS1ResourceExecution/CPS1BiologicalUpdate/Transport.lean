import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Preserve
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Reached

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing
attribute [local simp] List.forall_mem_cons List.forall_mem_append
variable {frame : CPS1Recycling.Frame}

abbrev DNA := List CPS1Deamination.Base

def recycledDNA? : CPS1Recycling.Species frame → Option DNA
  | .old item => nativeDNA? item
  | _ => none

def reinitiatedDNA? : CPS1Reinitiation.Species frame → Option DNA
  | .retained item => recycledDNA? item
  | _ => none

def localDNA? : CPS1LocalChemicalExecution.Species frame → Option DNA
  | .retained item => reinitiatedDNA? item
  | _ => none

def atomizedDNA? : CPS1AtomicSource.Current.Species frame → Option DNA
  | .retained item => localDNA? item
  | _ => none

def atomicDNA? : CPS1AtomicDynamics.Species frame → Option DNA
  | .retained item => atomizedDNA? item
  | _ => none

def bathDNA? : CPS1EnzymeBath.Species frame → Option DNA
  | .retained item => atomicDNA? item
  | _ => none

def electronicDNA? : CPS1ElectronicSource.Species frame → Option DNA
  | .retained item => bathDNA? item
  | _ => none

def nuclearDNA? : CPS1QuantumNuclear.Species frame → Option DNA
  | .retained item => electronicDNA? item
  | _ => none

def followingDNA? : CPS1Following.Species frame → Option DNA
  | .retained item => nuclearDNA? item
  | _ => none

def molecularDNA? : CPS1MolecularFrame.Species frame → Option DNA
  | .retained item => followingDNA? item
  | _ => none

def deformedDNA? : CPS1Deformation.Species frame → Option DNA
  | .retained item => molecularDNA? item
  | _ => none

section
open CPS1Recycling
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem recycledDNA_old (species : CPS1ResourceExecution.Species) :
    recycledDNA? (CPS1Recycling.Species.old species : CPS1Recycling.Species frame) = nativeDNA? species := rfl
@[simp] private theorem recycledDNA_abce1 (sites : Sites) :
    recycledDNA? (CPS1Recycling.Species.abce1 sites : CPS1Recycling.Species frame) = none := rfl
@[simp] private theorem recycledDNA_eIF3j  :
    recycledDNA? (CPS1Recycling.Species.eIF3j  : CPS1Recycling.Species frame) = none := rfl
@[simp] private theorem recycledDNA_adp  :
    recycledDNA? (CPS1Recycling.Species.adp  : CPS1Recycling.Species frame) = none := rfl
@[simp] private theorem recycledDNA_preSplit (trna : Trna) (sites : Sites) :
    recycledDNA? (CPS1Recycling.Species.preSplit trna sites : CPS1Recycling.Species frame) = none := rfl
@[simp] private theorem recycledDNA_boundSmall (trna : Trna) (sites : Sites) :
    recycledDNA? (CPS1Recycling.Species.boundSmall trna sites : CPS1Recycling.Species frame) = none := rfl
@[simp] private theorem recycledDNA_smallWithMessage (sites : Sites) :
    recycledDNA? (CPS1Recycling.Species.smallWithMessage sites : CPS1Recycling.Species frame) = none := rfl
@[simp] private theorem recycledDNA_primedSmall (sites : Sites) :
    recycledDNA? (CPS1Recycling.Species.primedSmall sites : CPS1Recycling.Species frame) = none := rfl
@[simp] private theorem recycledDNA_next43 (sites : Sites) :
    recycledDNA? (CPS1Recycling.Species.next43 sites : CPS1Recycling.Species frame) = none := rfl
@[simp] private theorem recycledDNA_messageCoordinate  :
    recycledDNA? (CPS1Recycling.Species.messageCoordinate  : CPS1Recycling.Species frame) = none := rfl
end

section
open CPS1Reinitiation
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem reinitiatedDNA_retained (old : CPS1Recycling.Species frame) :
    reinitiatedDNA? (CPS1Reinitiation.Species.retained old : CPS1Reinitiation.Species frame) = recycledDNA? old := rfl
@[simp] private theorem reinitiatedDNA_rna (word : RegisteredRna) :
    reinitiatedDNA? (CPS1Reinitiation.Species.rna word : CPS1Reinitiation.Species frame) = none := rfl
@[simp] private theorem reinitiatedDNA_factor (factor : RecruitmentFactor) :
    reinitiatedDNA? (CPS1Reinitiation.Species.factor factor : CPS1Reinitiation.Species frame) = none := rfl
@[simp] private theorem reinitiatedDNA_adp  :
    reinitiatedDNA? (CPS1Reinitiation.Species.adp  : CPS1Reinitiation.Species frame) = none := rfl
@[simp] private theorem reinitiatedDNA_scanning (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (address : Nat) :
    reinitiatedDNA? (CPS1Reinitiation.Species.scanning sites rna address : CPS1Reinitiation.Species frame) = none := rfl
@[simp] private theorem reinitiatedDNA_recognized (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (address : Nat) :
    reinitiatedDNA? (CPS1Reinitiation.Species.recognized sites rna address : CPS1Reinitiation.Species frame) = none := rfl
@[simp] private theorem reinitiatedDNA_committed (sites : CPS1Recycling.Sites) (rna : RegisteredRna) (address : Nat) :
    reinitiatedDNA? (CPS1Reinitiation.Species.committed sites rna address : CPS1Reinitiation.Species frame) = none := rfl
@[simp] private theorem reinitiatedDNA_unavailableCodon (rna : RegisteredRna) (address : Nat) :
    reinitiatedDNA? (CPS1Reinitiation.Species.unavailableCodon rna address : CPS1Reinitiation.Species frame) = none := rfl
end

section
open CPS1LocalChemicalExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem localDNA_retained (old : CPS1Reinitiation.Species frame) :
    localDNA? (CPS1LocalChemicalExecution.Species.retained old : CPS1LocalChemicalExecution.Species frame) = reinitiatedDNA? old := rfl
@[simp] private theorem localDNA_chain (state : Chain frame) :
    localDNA? (CPS1LocalChemicalExecution.Species.chain state : CPS1LocalChemicalExecution.Species frame) = none := rfl
@[simp] private theorem localDNA_molecule (molecule : Chemistry.Molecule) :
    localDNA? (CPS1LocalChemicalExecution.Species.molecule molecule : CPS1LocalChemicalExecution.Species frame) = none := rfl
@[simp] private theorem localDNA_processor  :
    localDNA? (CPS1LocalChemicalExecution.Species.processor  : CPS1LocalChemicalExecution.Species frame) = none := rfl
@[simp] private theorem localDNA_localRow (address : Nat) (r p : Vec) :
    localDNA? (CPS1LocalChemicalExecution.Species.localRow address r p : CPS1LocalChemicalExecution.Species frame) = none := rfl
@[simp] private theorem localDNA_impulse (address : Nat) (force : Vec) (dt mass : ℚ) :
    localDNA? (CPS1LocalChemicalExecution.Species.impulse address force dt mass : CPS1LocalChemicalExecution.Species frame) = none := rfl
@[simp] private theorem localDNA_spentImpulse (address : Nat) (force : Vec) (dt mass work : ℚ) :
    localDNA? (CPS1LocalChemicalExecution.Species.spentImpulse address force dt mass work : CPS1LocalChemicalExecution.Species frame) = none := rfl
@[simp] private theorem localDNA_missingPosition (address : Nat) :
    localDNA? (CPS1LocalChemicalExecution.Species.missingPosition address : CPS1LocalChemicalExecution.Species frame) = none := rfl
@[simp] private theorem localDNA_missingPeptideBond (address : Nat) :
    localDNA? (CPS1LocalChemicalExecution.Species.missingPeptideBond address : CPS1LocalChemicalExecution.Species frame) = none := rfl
@[simp] private theorem localDNA_missingResidue (address : Nat) :
    localDNA? (CPS1LocalChemicalExecution.Species.missingResidue address : CPS1LocalChemicalExecution.Species frame) = none := rfl
@[simp] private theorem localDNA_conflictingRow (address : Nat) :
    localDNA? (CPS1LocalChemicalExecution.Species.conflictingRow address : CPS1LocalChemicalExecution.Species frame) = none := rfl
end

section
open CPS1AtomicSource.Current CPS1LocalChemicalExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem atomizedDNA_retained (old : CPS1LocalChemicalExecution.Species frame) :
    atomizedDNA? (CPS1AtomicSource.Current.Species.retained old : CPS1AtomicSource.Current.Species frame) = localDNA? old := rfl
@[simp] private theorem atomizedDNA_atomic (source : Chain frame) :
    atomizedDNA? (CPS1AtomicSource.Current.Species.atomic source : CPS1AtomicSource.Current.Species frame) = none := rfl
@[simp] private theorem atomizedDNA_missingChain  :
    atomizedDNA? (CPS1AtomicSource.Current.Species.missingChain  : CPS1AtomicSource.Current.Species frame) = none := rfl
end

section
open CPS1AtomicDynamics
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem atomicDNA_retained (old : CPS1AtomicSource.Current.Species frame) :
    atomicDNA? (CPS1AtomicDynamics.Species.retained old : CPS1AtomicDynamics.Species frame) = atomizedDNA? old := rfl
@[simp] private theorem atomicDNA_body (state : Body.State frame) :
    atomicDNA? (CPS1AtomicDynamics.Species.body state : CPS1AtomicDynamics.Species frame) = none := rfl
@[simp] private theorem atomicDNA_rawRow (address : Charged.Address) (row : Body.Row) :
    atomicDNA? (CPS1AtomicDynamics.Species.rawRow address row : CPS1AtomicDynamics.Species frame) = none := rfl
@[simp] private theorem atomicDNA_rawEnergy (amount : ℝ) :
    atomicDNA? (CPS1AtomicDynamics.Species.rawEnergy amount : CPS1AtomicDynamics.Species frame) = none := rfl
@[simp] private theorem atomicDNA_rawTime (dt : ℝ) :
    atomicDNA? (CPS1AtomicDynamics.Species.rawTime dt : CPS1AtomicDynamics.Species frame) = none := rfl
@[simp] private theorem atomicDNA_spentPulse (pulse : Body.Pulse) :
    atomicDNA? (CPS1AtomicDynamics.Species.spentPulse pulse : CPS1AtomicDynamics.Species frame) = none := rfl
@[simp] private theorem atomicDNA_missingAtomic  :
    atomicDNA? (CPS1AtomicDynamics.Species.missingAtomic  : CPS1AtomicDynamics.Species frame) = none := rfl
@[simp] private theorem atomicDNA_guard (failure : Body.Failure) :
    atomicDNA? (CPS1AtomicDynamics.Species.guard failure : CPS1AtomicDynamics.Species frame) = none := rfl
end

section
open CPS1EnzymeBath
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem bathDNA_retained (old : CPS1AtomicDynamics.Species frame) :
    bathDNA? (CPS1EnzymeBath.Species.retained old : CPS1EnzymeBath.Species frame) = atomicDNA? old := rfl
@[simp] private theorem bathDNA_joint (state : Joint.State frame) :
    bathDNA? (CPS1EnzymeBath.Species.joint state : CPS1EnzymeBath.Species frame) = none := rfl
@[simp] private theorem bathDNA_rawRow (address : CPS1AtomicDynamics.Charged.Address) (row : CPS1AtomicDynamics.Body.Row) :
    bathDNA? (CPS1EnzymeBath.Species.rawRow address row : CPS1EnzymeBath.Species frame) = none := rfl
@[simp] private theorem bathDNA_rawEnergy (amount : ℝ) :
    bathDNA? (CPS1EnzymeBath.Species.rawEnergy amount : CPS1EnzymeBath.Species frame) = none := rfl
@[simp] private theorem bathDNA_rawTime (dt : ℝ) :
    bathDNA? (CPS1EnzymeBath.Species.rawTime dt : CPS1EnzymeBath.Species frame) = none := rfl
@[simp] private theorem bathDNA_spentPulse (pulse : CPS1AtomicDynamics.Body.Pulse) :
    bathDNA? (CPS1EnzymeBath.Species.spentPulse pulse : CPS1EnzymeBath.Species frame) = none := rfl
@[simp] private theorem bathDNA_guard (failure : CPS1AtomicDynamics.Body.Failure) :
    bathDNA? (CPS1EnzymeBath.Species.guard failure : CPS1EnzymeBath.Species frame) = none := rfl
@[simp] private theorem bathDNA_missingBody  :
    bathDNA? (CPS1EnzymeBath.Species.missingBody  : CPS1EnzymeBath.Species frame) = none := rfl
end

section
open CPS1ElectronicSource
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem electronicDNA_retained (old : CPS1EnzymeBath.Species frame) :
    electronicDNA? (CPS1ElectronicSource.Species.retained old : CPS1ElectronicSource.Species frame) = bathDNA? old := rfl
@[simp] private theorem electronicDNA_quantum (state : State frame) :
    electronicDNA? (CPS1ElectronicSource.Species.quantum state : CPS1ElectronicSource.Species frame) = none := rfl
@[simp] private theorem electronicDNA_rawRow (address : CPS1AtomicDynamics.Charged.Address) (row : CPS1AtomicDynamics.Body.Row) :
    electronicDNA? (CPS1ElectronicSource.Species.rawRow address row : CPS1ElectronicSource.Species frame) = none := rfl
@[simp] private theorem electronicDNA_rawEnergy (amount : ℝ) :
    electronicDNA? (CPS1ElectronicSource.Species.rawEnergy amount : CPS1ElectronicSource.Species frame) = none := rfl
@[simp] private theorem electronicDNA_rawTime (time : ℝ) :
    electronicDNA? (CPS1ElectronicSource.Species.rawTime time : CPS1ElectronicSource.Species frame) = none := rfl
@[simp] private theorem electronicDNA_spentQuantum (pulse : ElectronicPulse) :
    electronicDNA? (CPS1ElectronicSource.Species.spentQuantum pulse : CPS1ElectronicSource.Species frame) = none := rfl
@[simp] private theorem electronicDNA_guard (failure : Failure) :
    electronicDNA? (CPS1ElectronicSource.Species.guard failure : CPS1ElectronicSource.Species frame) = none := rfl
@[simp] private theorem electronicDNA_missingCarrier  :
    electronicDNA? (CPS1ElectronicSource.Species.missingCarrier  : CPS1ElectronicSource.Species frame) = none := rfl
end

section
open CPS1QuantumNuclear
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem nuclearDNA_retained (old : CPS1ElectronicSource.Species frame) :
    nuclearDNA? (CPS1QuantumNuclear.Species.retained old : CPS1QuantumNuclear.Species frame) = electronicDNA? old := rfl
@[simp] private theorem nuclearDNA_guard (failure : Failure) :
    nuclearDNA? (CPS1QuantumNuclear.Species.guard failure : CPS1QuantumNuclear.Species frame) = none := rfl
end

section
open CPS1Following
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem followingDNA_retained (old : CPS1QuantumNuclear.Species frame) :
    followingDNA? (CPS1Following.Species.retained old : CPS1Following.Species frame) = nuclearDNA? old := rfl
@[simp] private theorem followingDNA_following (state : CPS1ElectronicSource.State frame) :
    followingDNA? (CPS1Following.Species.following state : CPS1Following.Species frame) = none := rfl
@[simp] private theorem followingDNA_spentRelocation (receipt : RelocationReceipt) :
    followingDNA? (CPS1Following.Species.spentRelocation receipt : CPS1Following.Species frame) = none := rfl
@[simp] private theorem followingDNA_spentPulse (pulse : CPS1ElectronicSource.ElectronicPulse) :
    followingDNA? (CPS1Following.Species.spentPulse pulse : CPS1Following.Species frame) = none := rfl
@[simp] private theorem followingDNA_guard (failure : Failure) :
    followingDNA? (CPS1Following.Species.guard failure : CPS1Following.Species frame) = none := rfl
end

section
open CPS1MolecularFrame
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem molecularDNA_retained (old : CPS1Following.Species frame) :
    molecularDNA? (CPS1MolecularFrame.Species.retained old : CPS1MolecularFrame.Species frame) = followingDNA? old := rfl
@[simp] private theorem molecularDNA_molecular (state : Material frame) :
    molecularDNA? (CPS1MolecularFrame.Species.molecular state : CPS1MolecularFrame.Species frame) = none := rfl
@[simp] private theorem molecularDNA_spentAdopt (reference : CPS1ElectronicSource.State frame) :
    molecularDNA? (CPS1MolecularFrame.Species.spentAdopt reference : CPS1MolecularFrame.Species frame) = none := rfl
@[simp] private theorem molecularDNA_spentPulse (before : Material frame) (time : ℝ) :
    molecularDNA? (CPS1MolecularFrame.Species.spentPulse before time : CPS1MolecularFrame.Species frame) = none := rfl
@[simp] private theorem molecularDNA_guard (failure : Failure) :
    molecularDNA? (CPS1MolecularFrame.Species.guard failure : CPS1MolecularFrame.Species frame) = none := rfl
@[simp] private theorem molecularDNA_missingCarrier  :
    molecularDNA? (CPS1MolecularFrame.Species.missingCarrier  : CPS1MolecularFrame.Species frame) = none := rfl
end

section
open CPS1Deformation
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
@[simp] private theorem deformedDNA_retained (old : CPS1MolecularFrame.Species frame) :
    deformedDNA? (CPS1Deformation.Species.retained old : CPS1Deformation.Species frame) = molecularDNA? old := rfl
@[simp] private theorem deformedDNA_deformed (state : Material frame) :
    deformedDNA? (CPS1Deformation.Species.deformed state : CPS1Deformation.Species frame) = none := rfl
@[simp] private theorem deformedDNA_spentAdopt (reference : CPS1MolecularFrame.Material frame) :
    deformedDNA? (CPS1Deformation.Species.spentAdopt reference : CPS1Deformation.Species frame) = none := rfl
@[simp] private theorem deformedDNA_spentPulse (before : Material frame) (time : ℝ) :
    deformedDNA? (CPS1Deformation.Species.spentPulse before time : CPS1Deformation.Species frame) = none := rfl
@[simp] private theorem deformedDNA_guard (failure : Failure) :
    deformedDNA? (CPS1Deformation.Species.guard failure : CPS1Deformation.Species frame) = none := rfl
@[simp] private theorem deformedDNA_missingCarrier  :
    deformedDNA? (CPS1Deformation.Species.missingCarrier  : CPS1Deformation.Species frame) = none := rfl
end

private theorem ignored_map {S T : Type} (read : S → Option DNA)
    (lift : S → T) (readLift : T → Option DNA) (same : ∀ item, readLift (lift item) = read item)
    (required produced : List S)
    (ignored : (∀ item ∈ required, read item = none) ∧ produced.filterMap read = []) :
    (∀ item ∈ required.map lift, readLift item = none) ∧ (produced.map lift).filterMap readLift = [] := by
  constructor
  · intro item member
    rcases List.mem_map.mp member with ⟨original,held,rfl⟩
    exact (same original).trans (ignored.1 original held)
  · simpa only [List.filterMap_map,Function.comp_def,same] using ignored.2

@[simp] private theorem local_molecule_none (item : CPS1LocalChemicalExecution.Chemistry.Molecule) :
    localDNA? (CPS1LocalChemicalExecution.molecule frame item) = none := by
  cases item <;> rfl

@[simp] private theorem recycled_post_none (trna : CPS1Recycling.Trna) :
    nativeDNA? (CPS1Recycling.postSpecies trna) = none := by
  cases trna <;> rfl

@[simp] private theorem recycled_returned_none (trna : CPS1Recycling.Trna) :
    nativeDNA? (CPS1Recycling.returnedTrna trna) = none := by
  cases trna <;> rfl

@[simp] private theorem reinit_actual_none :
    reinitiatedDNA? (CPS1LocalChemicalExecution.Actual.species frame) = none := rfl

@[simp] private theorem capture_dna_none :
    localDNA? (.retained (CPS1LocalChemicalExecution.Actual.species frame)) = none := rfl

@[simp] private theorem bath_component_none (kind : CPS1EnzymeBath.Primary.TemplateKind) :
    bathDNA? (CPS1EnzymeBath.componentSpecies frame kind) = none :=
  local_molecule_none kind.molecule

private theorem recycled_reaction_ignored (reaction : CPS1Recycling.Primitive) :
    (∀ item ∈ reaction.reactants frame, recycledDNA? item = none) ∧
      (reaction.products frame).filterMap recycledDNA? = [] := by
  cases reaction <;>
    simp [CPS1Recycling.Primitive.reactants,CPS1Recycling.Primitive.products,
      Reaction.reactants,Reaction.products,nativeDNA?]
  case engageControl trna => cases trna <;> rfl
  case removeTrna trna sites => cases trna <;> rfl

private theorem local_reaction_ignored (reaction : CPS1LocalChemicalExecution.Reaction frame) :
    (∀ item ∈ reaction.reactants frame, localDNA? item = none) ∧
      (reaction.products frame).filterMap localDNA? = [] := by
  cases reaction <;>
    simp only [CPS1LocalChemicalExecution.Reaction.reactants,CPS1LocalChemicalExecution.Reaction.products]
  case chemical step =>
    exact ignored_map (fun _ => none) (CPS1LocalChemicalExecution.molecule frame) localDNA?
      local_molecule_none _ _ ⟨by intros; rfl,by simp⟩
  all_goals repeat first
    | (solve | simp)
    | split

private theorem atomized_reaction_ignored (reaction : CPS1AtomicSource.Current.Reaction frame) :
    (∀ item ∈ reaction.reactants frame, atomizedDNA? item = none) ∧
      (reaction.products frame).filterMap atomizedDNA? = [] := by
  cases reaction <;>
    simp [CPS1AtomicSource.Current.Reaction.reactants,CPS1AtomicSource.Current.Reaction.products,
      CPS1AtomicSource.Current.proton,atomizedDNA?,localDNA?,reinitiatedDNA?,recycledDNA?,nativeDNA?,
      CPS1LocalChemicalExecution.molecule,CPS1StockRecursion.Dictionary.old]

private theorem atomic_reaction_ignored (reaction : CPS1AtomicDynamics.Reaction frame) :
    (∀ item ∈ reaction.reactants frame, atomicDNA? item = none) ∧
      (reaction.products frame).filterMap atomicDNA? = [] := by
  cases reaction <;>
    simp only [CPS1AtomicDynamics.Reaction.reactants,CPS1AtomicDynamics.Reaction.products,CPS1AtomicDynamics.guards]
  all_goals repeat first
    | (solve | simp)
    | split

private theorem bath_reaction_ignored (reaction : CPS1EnzymeBath.Reaction frame) :
    (∀ item ∈ reaction.reactants frame, bathDNA? item = none) ∧
      (reaction.products frame).filterMap bathDNA? = [] := by
  cases reaction <;>
    simp only [CPS1EnzymeBath.Reaction.reactants,CPS1EnzymeBath.Reaction.products,CPS1EnzymeBath.guards]
  all_goals repeat first
    | (solve | simp)
    | split

private theorem electronic_reaction_ignored (reaction : CPS1ElectronicSource.Reaction frame) :
    (∀ item ∈ reaction.reactants frame, electronicDNA? item = none) ∧
      (reaction.products frame).filterMap electronicDNA? = [] := by
  cases reaction <;>
    simp only [CPS1ElectronicSource.Reaction.reactants,CPS1ElectronicSource.Reaction.products,CPS1ElectronicSource.guards]
  all_goals repeat first
    | (solve | simp)
    | split

private theorem nuclear_reaction_ignored (reaction : CPS1QuantumNuclear.Reaction frame) :
    (∀ item ∈ reaction.reactants frame, nuclearDNA? item = none) ∧
      (reaction.products frame).filterMap nuclearDNA? = [] := by
  cases reaction
  case retained original =>
    exact ignored_map electronicDNA? CPS1QuantumNuclear.Species.retained nuclearDNA? (fun _ => rfl)
      _ _ (electronic_reaction_ignored original)
  all_goals
    simp only [CPS1QuantumNuclear.Reaction.reactants,CPS1QuantumNuclear.Reaction.products,CPS1QuantumNuclear.guards]
    repeat first
      | (solve | simp)
      | split

private theorem following_reaction_ignored (reaction : CPS1Following.Reaction frame) :
    (∀ item ∈ reaction.reactants frame, followingDNA? item = none) ∧
      (reaction.products frame).filterMap followingDNA? = [] := by
  cases reaction
  case retained original =>
    exact ignored_map nuclearDNA? CPS1Following.Species.retained followingDNA? (fun _ => rfl)
      _ _ (nuclear_reaction_ignored original)
  all_goals
    simp only [CPS1Following.Reaction.reactants,CPS1Following.Reaction.products,CPS1Following.guards]
    repeat first
      | (solve | simp)
      | split

private theorem molecular_reaction_ignored (reaction : CPS1MolecularFrame.Reaction frame) :
    (∀ item ∈ reaction.reactants frame, molecularDNA? item = none) ∧
      (reaction.products frame).filterMap molecularDNA? = [] := by
  cases reaction
  case retained original =>
    exact ignored_map followingDNA? CPS1MolecularFrame.Species.retained molecularDNA? (fun _ => rfl)
      _ _ (following_reaction_ignored original)
  all_goals
    simp only [CPS1MolecularFrame.Reaction.reactants,CPS1MolecularFrame.Reaction.products,CPS1MolecularFrame.guards]
    repeat first
      | (solve | simp)
      | split

private theorem deformed_reaction_ignored (reaction : CPS1Deformation.Reaction frame) :
    (∀ item ∈ reaction.reactants frame, deformedDNA? item = none) ∧
      (reaction.products frame).filterMap deformedDNA? = [] := by
  cases reaction
  case retained original =>
    exact ignored_map molecularDNA? CPS1Deformation.Species.retained deformedDNA? (fun _ => rfl)
      _ _ (molecular_reaction_ignored original)
  all_goals
    simp only [CPS1Deformation.Reaction.reactants,CPS1Deformation.Reaction.products,CPS1Deformation.guards]
    repeat first
      | (solve | simp)
      | split

theorem recycled_stock_genome (program : List (CPS1Recycling.Primitive)) (stock : List (CPS1Recycling.Species frame)) :
    (Inventory.execute (CPS1Recycling.Primitive.reactants frame) (CPS1Recycling.Primitive.products frame) program stock).stock.filterMap recycledDNA? = stock.filterMap recycledDNA? :=
  inventory_filterMap_preserved recycledDNA? _ _ program stock (fun reaction _ => recycled_reaction_ignored reaction)

theorem local_stock_genome (program : List (CPS1LocalChemicalExecution.Reaction frame)) (stock : List (CPS1LocalChemicalExecution.Species frame)) :
    (Inventory.execute (CPS1LocalChemicalExecution.Reaction.reactants frame) (CPS1LocalChemicalExecution.Reaction.products frame) program stock).stock.filterMap localDNA? = stock.filterMap localDNA? :=
  inventory_filterMap_preserved localDNA? _ _ program stock (fun reaction _ => local_reaction_ignored reaction)

theorem atomized_stock_genome (program : List (CPS1AtomicSource.Current.Reaction frame)) (stock : List (CPS1AtomicSource.Current.Species frame)) :
    (Inventory.execute (CPS1AtomicSource.Current.Reaction.reactants frame) (CPS1AtomicSource.Current.Reaction.products frame) program stock).stock.filterMap atomizedDNA? = stock.filterMap atomizedDNA? :=
  inventory_filterMap_preserved atomizedDNA? _ _ program stock (fun reaction _ => atomized_reaction_ignored reaction)

theorem atomic_stock_genome (program : List (CPS1AtomicDynamics.Reaction frame)) (stock : List (CPS1AtomicDynamics.Species frame)) :
    (Inventory.execute (CPS1AtomicDynamics.Reaction.reactants frame) (CPS1AtomicDynamics.Reaction.products frame) program stock).stock.filterMap atomicDNA? = stock.filterMap atomicDNA? :=
  inventory_filterMap_preserved atomicDNA? _ _ program stock (fun reaction _ => atomic_reaction_ignored reaction)

theorem bath_stock_genome (program : List (CPS1EnzymeBath.Reaction frame)) (stock : List (CPS1EnzymeBath.Species frame)) :
    (Inventory.execute (CPS1EnzymeBath.Reaction.reactants frame) (CPS1EnzymeBath.Reaction.products frame) program stock).stock.filterMap bathDNA? = stock.filterMap bathDNA? :=
  inventory_filterMap_preserved bathDNA? _ _ program stock (fun reaction _ => bath_reaction_ignored reaction)

theorem electronic_stock_genome (program : List (CPS1ElectronicSource.Reaction frame)) (stock : List (CPS1ElectronicSource.Species frame)) :
    (Inventory.execute (CPS1ElectronicSource.Reaction.reactants frame) (CPS1ElectronicSource.Reaction.products frame) program stock).stock.filterMap electronicDNA? = stock.filterMap electronicDNA? :=
  inventory_filterMap_preserved electronicDNA? _ _ program stock (fun reaction _ => electronic_reaction_ignored reaction)

theorem nuclear_stock_genome (program : List (CPS1QuantumNuclear.Reaction frame)) (stock : List (CPS1QuantumNuclear.Species frame)) :
    (Inventory.execute (CPS1QuantumNuclear.Reaction.reactants frame) (CPS1QuantumNuclear.Reaction.products frame) program stock).stock.filterMap nuclearDNA? = stock.filterMap nuclearDNA? :=
  inventory_filterMap_preserved nuclearDNA? _ _ program stock (fun reaction _ => nuclear_reaction_ignored reaction)

theorem following_stock_genome (program : List (CPS1Following.Reaction frame)) (stock : List (CPS1Following.Species frame)) :
    (Inventory.execute (CPS1Following.Reaction.reactants frame) (CPS1Following.Reaction.products frame) program stock).stock.filterMap followingDNA? = stock.filterMap followingDNA? :=
  inventory_filterMap_preserved followingDNA? _ _ program stock (fun reaction _ => following_reaction_ignored reaction)

theorem molecular_stock_genome (program : List (CPS1MolecularFrame.Reaction frame)) (stock : List (CPS1MolecularFrame.Species frame)) :
    (Inventory.execute (CPS1MolecularFrame.Reaction.reactants frame) (CPS1MolecularFrame.Reaction.products frame) program stock).stock.filterMap molecularDNA? = stock.filterMap molecularDNA? :=
  inventory_filterMap_preserved molecularDNA? _ _ program stock (fun reaction _ => molecular_reaction_ignored reaction)

theorem deformed_stock_genome (program : List (CPS1Deformation.Reaction frame)) (stock : List (CPS1Deformation.Species frame)) :
    (Inventory.execute (CPS1Deformation.Reaction.reactants frame) (CPS1Deformation.Reaction.products frame) program stock).stock.filterMap deformedDNA? = stock.filterMap deformedDNA? :=
  inventory_filterMap_preserved deformedDNA? _ _ program stock (fun reaction _ => deformed_reaction_ignored reaction)

end
end CPS1BiologicalUpdate
