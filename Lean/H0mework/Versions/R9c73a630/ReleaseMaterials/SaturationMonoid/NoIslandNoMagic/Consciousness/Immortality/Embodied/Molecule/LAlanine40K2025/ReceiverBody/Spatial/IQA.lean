import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Fields
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAtomicIQA.Runtime.Consumers

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
open Propagation.Interface
open UnifiedOrbitals
open UnifiedOrbitals.Frame
open UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open BasinRefinement.WholeBandBasin.Family.All
open scoped BigOperators
noncomputable section
def originalIQA := BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.readMaterial BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.afterFirst

theorem original_iqa_from_source :
    type_of% (BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.material_read BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.afterFirst) :=
  BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.material_read BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.afterFirst

theorem original_iqa_total :
    type_of% (BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.target_iqa_original_ao BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.afterFirst) :=
  BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.target_iqa_original_ao BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.afterFirst

theorem original_iqa_independent :
    type_of% (BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.target_iqa_independent BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.afterFirst) :=
  BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.target_iqa_independent BasinRefinement.WholeBandBasin.Family.All.PreciseAtomicIQA.Runtime.afterFirst

def originalFace (face : PreciseAtomicIQA.Runtime.Face) :=
  PreciseAtomicIQA.Runtime.facade.readoutAt PreciseAtomicIQA.Runtime.afterFirst face

theorem original_face_factorizes (face : PreciseAtomicIQA.Runtime.Face) :
    type_of% (PreciseAtomicIQA.Runtime.face_factorizes PreciseAtomicIQA.Runtime.afterFirst face) :=
  PreciseAtomicIQA.Runtime.face_factorizes PreciseAtomicIQA.Runtime.afterFirst face

def iqaTotal (m : PreciseAtomicIQA.Material) : Prop :=
  (∑ a : Fin 13, m.selfEnergy a)+(∑ p ∈ AtomicIQA.pairSet, m.interaction p.1 p.2)+m.residualEnergy =
    (∑ i : Basis, ∑ j : Basis, (BasinRefinement.SourceFiniteData.densityMatrix i j : ℝ)*
      (UnifiedOrbitals.kinetic i j+UnifiedOrbitals.Attraction.Precise.aoIntegral i j))+
      (∑ p ∈ AtomicIQA.pairSet, m.nuclearRepulsion p.1 p.2)+pairCoulombEnergy.re

def iqaIndependent (m : PreciseAtomicIQA.Material) : Prop :=
  |((∑ a : Fin 13, m.selfEnergy a)+(∑ p ∈ AtomicIQA.pairSet, m.interaction p.1 p.2)+m.residualEnergy)-
    ((∑ z : Option (Fin 13), OneBody.zoneKinetic z)+m.parent.parent.independentWeighted+
      Nuclear.PreciseTarget.totalRepulsion+pairCoulombEnergy.re)| ≤ (1/10^9 : ℝ)

structure Material where
  body : ReceiverBody.Runtime.ActuationResult
  original : PreciseAtomicIQA.Material

def materialOf (body : ReceiverBody.Runtime.ActuationResult) : Material := ⟨body,originalIQA⟩

-- This historical occurrence keeps its M3 frame, clock and ledger after static transport.
theorem original_body_source : Frame.Runtime.parentResult=ReceiverBody.Runtime.bodyResponse := by
  exact (PreciseAtomicIQA.Runtime.response PreciseAtomicIQA.Runtime.afterFirst).symm

def jointTotal (m : Material) : Prop :=
  (∑ a : Fin 13, m.original.selfEnergy a)+
    (∑ p ∈ AtomicIQA.pairSet, m.original.interaction p.1 p.2)+m.original.residualEnergy =
    (∑ i : Basis, ∑ j : Basis, (BasinRefinement.SourceFiniteData.densityMatrix i j : ℝ)*
      (UnifiedOrbitals.kinetic i j+aoAttractionAt m.body i j))+
      (∑ p ∈ AtomicIQA.pairSet, nuclearRepulsionAt m.body p.1 p.2)+pairCoulombEnergy.re

theorem joint_total_from_source {body : ReceiverBody.Runtime.ActuationResult}
    (source : StaticClosure body) : jointTotal (materialOf body) := by
  have total := original_iqa_total
  have pair (a b : Fin 13) : originalIQA.nuclearRepulsion a b=
      Nuclear.PreciseTarget.nuclearRepulsion a b :=
    PreciseAtomicIQA.Runtime.target_repulsion_source _ a b
  change iqaTotal originalIQA at total
  unfold iqaTotal at total
  simp only [pair] at total
  simpa only [jointTotal,materialOf,ao_from_static source,repulsion_from_static source] using total

structure Closure (m : Material) : Prop where
  static : StaticClosure m.body
  fields : FieldClosure m.body
  jointTotal : Spatial.jointTotal m
  original : m.original=originalIQA
  source : type_of% original_iqa_from_source
  total : iqaTotal m.original
  independent : iqaIndependent m.original
  oldBody : type_of% original_body_source
  oldPhysical : type_of% (PreciseAtomicIQA.Runtime.read_commutes_with_physicalOccurrence
    PreciseAtomicIQA.Runtime.afterFirst)
  oldClock : type_of% (PreciseAtomicIQA.Runtime.clock_preserved PreciseAtomicIQA.Runtime.afterFirst)
  oldWhole : type_of% (PreciseAtomicIQA.Runtime.wholeLedger_same_occurrence PreciseAtomicIQA.Runtime.afterFirst)
  oldRow : type_of% (PreciseAtomicIQA.Runtime.row_identity PreciseAtomicIQA.Runtime.afterFirst)
  oldFaces : ∀ face, type_of% (original_face_factorizes face)

theorem sourceClosure : Closure (materialOf ReceiverBody.Runtime.sourceOutput) :=
  ⟨outputStaticClosure,fields_from_static outputStaticClosure,joint_total_from_source outputStaticClosure,
    rfl,original_iqa_from_source,original_iqa_total,original_iqa_independent,
    original_body_source,PreciseAtomicIQA.Runtime.read_commutes_with_physicalOccurrence _,
    PreciseAtomicIQA.Runtime.clock_preserved _,PreciseAtomicIQA.Runtime.wholeLedger_same_occurrence _,
    PreciseAtomicIQA.Runtime.row_identity _,original_face_factorizes⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial
