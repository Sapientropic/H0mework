import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldTransfer
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceJointCausalField

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalFullFieldScattering
open PreparationVacuumFullSlowFieldResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Electromagnetic.CanonicalCoframe
open scoped Matrix BigOperators Topology InnerProductSpace

/-- One source leg of the four-point scattering vertex: only the original
    source response point, wave, causal-domain frequency, rest-state labels and
    the two nonreal-pole facts. It bundles no field, matrix, normalizer or
    external certificate; the root remains the fixed actual source. -/
structure CausalFieldLeg where
  q : PhysicalResponsePoint
  wave : CanonicalGradedSpatialSource.PhysicalMomentum
  frequency : sourceCausalDomain wave
  left : RestStateIndex
  right : RestStateIndex
  nonrealL : q.z.im ≠ 0
  nonrealR : q.w.im ≠ 0

/-- The joint causal field of one leg at causal scale `d`. -/
def causalField (leg : CausalFieldLeg) (d : ℝ) : Fin 289→ℂ :=
  sourceJointCausalField leg.q leg.wave leg.frequency.val leg.left leg.right d

/-- The joint field residue of one leg, produced by the same actual source root. -/
def residueField (leg : CausalFieldLeg) : Fin 289→ℂ :=
  sourceJointFieldResidue leg.q leg.wave leg.frequency.val leg.left leg.right

/-- The positive/negative transfer pair of two causal-field legs at scale `d`. -/
def causalTransfer (pos neg : CausalFieldLeg) (d : ℝ) : TransferPair :=
  originalTransferPair (causalField pos d) (causalField neg d)

/-- The positive/negative transfer pair of two leg residues. -/
def residueTransfer (pos neg : CausalFieldLeg) : TransferPair :=
  originalTransferPair (residueField pos) (residueField neg)

/-- The actual scattering pair of four source legs at causal scale `d`; all
    fields are the source joint causal fields of the four legs, not supplied
    limits. -/
def actualScatteringPair (momentum : Fin 3→ℝ)
    (Apos Aneg Bpos Bneg : CausalFieldLeg) (shift : Fin 3→ℝ) (time age : ℝ)
    (d : ℝ) : ℂ × ℂ :=
  originalScatteringPair momentum (causalTransfer Apos Aneg d)
    (causalTransfer Bpos Bneg d) shift time age

/-- The actual scattering residue pair of the same four legs, read on their
    joint field residues. -/
def actualScatteringResidue (momentum : Fin 3→ℝ)
    (Apos Aneg Bpos Bneg : CausalFieldLeg) (shift : Fin 3→ℝ) (time age : ℝ) :
    ℂ × ℂ :=
  originalScatteringPair momentum (residueTransfer Apos Aneg)
    (residueTransfer Bpos Bneg) shift time age

end LowEnergy.GaussComposite.PhysicalFullFieldScattering
