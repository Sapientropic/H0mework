import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.CoulombReplacement.Runtime.Consumers

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Coulomb
open BasinRefinement.WholeBandBasin.Family.All
open UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def parentRuntime := Spatial.Runtime.afterFirst
def parentMaterial := Spatial.Runtime.readMaterial parentRuntime Spatial.Runtime.first_ready

def sourceRuntime := CoulombReplacement.Runtime.afterFirst
def sourceMaterial := CoulombReplacement.Runtime.readMaterial sourceRuntime

theorem parent_certificate :
    type_of% (Spatial.Runtime.certificate_read parentRuntime Spatial.Runtime.first_ready) :=
  Spatial.Runtime.certificate_read parentRuntime Spatial.Runtime.first_ready

theorem source_certificate : type_of% (CoulombReplacement.Runtime.certificate_read sourceRuntime) :=
  CoulombReplacement.Runtime.certificate_read sourceRuntime

-- Root186 and the already-retained Root184 share the old spatial occurrence.
-- This does not identify that old occurrence with the later joint action.
theorem historical_same_visit :
    sourceRuntime.current.visit=PreciseAtomicIQA.Runtime.afterFirst.current.visit :=
  CoulombReplacement.Runtime.sourceGeneratedPhysicalCoulombReplacementNext.originalVisit.trans
    PreciseAtomicIQA.Runtime.sourceGeneratedPhysicalPreciseAtomicIQANext.originalVisit.symm

theorem historical_shared_face (face : PreciseAtomicIQA.Runtime.Face) :
    HEq (CoulombReplacement.Runtime.facade.readoutAt sourceRuntime (.inherited face))
      (Spatial.originalFace face) := by
  cases face with
  | component projection =>
    exact PreciseAtomicIQA.Runtime.componentInstallation.outcome_heq sourceRuntime.emittedOccurrence projection
  | inherited projection =>
    exact PreciseAtomicIQA.Runtime.inheritedInstallation.outcome_heq sourceRuntime.emittedOccurrence projection

def d3Energy (weight : Weight.Material) : ℝ := (1/2 : ℝ)*∑ a : Fin 4851,
  (weight.parent.sourceCoefficient a : ℝ)*
    weight.parent.targetJ (targetLeft a.val) (targetRight a.val)

def originalD3Energy : ℝ := d3Energy sourceMaterial

theorem original_d3_energy : originalD3Energy=Hartree.Charge.Residual.Interaction.d3HartreeEnergy :=
  (CoulombReplacement.Runtime.d3_hartree_address_read sourceRuntime).symm

theorem original_coulomb_columns :
    |10^9*originalD3Energy-
      ((Reentry.Runtime.reentryCurrentLedger sourceRuntime.tick.next.state.current).rowSum .coulomb : ℝ)-
      sourceMaterial.reportPotentialResidual| ≤ 863 ∧
    |10^9*originalD3Energy-
      (((Reentry.Runtime.reentryCurrentLedger sourceRuntime.tick.next.state.current).integral .coulomb).independentIntegral : ℝ)-
      sourceMaterial.reportPotentialResidual| ≤ 860 := by
  rw [original_d3_energy]
  exact CoulombReplacement.Runtime.blyp_coulomb_column_read sourceRuntime

def originalLedger := Reentry.Runtime.reentryCurrentLedger sourceRuntime.tick.next.state.current

theorem parent_generated : parentMaterial=Spatial.materialOf ReceiverBody.Runtime.sourceOutput :=
  Spatial.Runtime.actual_material.trans (congrArg Spatial.materialOf Spatial.current_generated)

theorem original_hartree_error :
    |originalD3Energy-sourceMaterial.reportHartree| ≤ (sourceMaterial.hartreeBound : ℝ) := by
  rw [original_d3_energy]
  exact CoulombReplacement.Runtime.blyp_replacement_read sourceRuntime

structure Material where
  joint : Spatial.Material
  weight : Weight.Material
  ledger : type_of% originalLedger

def materialOf (body : ReceiverBody.Runtime.ActuationResult) : Material :=
  ⟨Spatial.materialOf body,sourceMaterial,originalLedger⟩

def CoulombAccount (m : Material) : Prop :=
  |d3Energy m.weight-m.weight.reportHartree| ≤ (m.weight.hartreeBound : ℝ) ∧
  |10^9*d3Energy m.weight-(m.ledger.rowSum .coulomb : ℝ)-m.weight.reportPotentialResidual| ≤ 863 ∧
  |10^9*d3Energy m.weight-((m.ledger.integral .coulomb).independentIntegral : ℝ)-
      m.weight.reportPotentialResidual| ≤ 860

structure Closure (m : Material) : Prop where
  joint : Spatial.Closure m.joint
  parentAuthority : type_of% parent_certificate
  originalAuthority : type_of% source_certificate
  weight : m.weight=sourceMaterial
  ledger : m.ledger=originalLedger
  sharedVisit : type_of% historical_same_visit
  sharedFaces : ∀ face, type_of% (historical_shared_face face)
  hartree : d3Energy m.weight=Hartree.Charge.Residual.Interaction.d3HartreeEnergy
  account : CoulombAccount m
  potential : m.joint.body.frame.potential=Reentry.Source.stepReadout.nuclear.target.potential

theorem sourceClosure : Closure (materialOf ReceiverBody.Runtime.sourceOutput) :=
  ⟨Spatial.sourceClosure,parent_certificate,source_certificate,rfl,rfl,historical_same_visit,
    historical_shared_face,original_d3_energy,
    ⟨original_hartree_error,original_coulomb_columns⟩,rfl⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Coulomb
