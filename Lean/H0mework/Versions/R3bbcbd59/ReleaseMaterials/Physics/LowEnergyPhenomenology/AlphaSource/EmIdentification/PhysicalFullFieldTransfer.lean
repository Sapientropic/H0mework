import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationMixedDensityContacts
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.Electromagnetic.CanonicalCoframe

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalFullFieldScattering
open PreparationVacuumMixedFieldReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Electromagnetic.CanonicalCoframe
open scoped Matrix BigOperators Topology InnerProductSpace

/-- A complex original field `v` restricted to its real and imaginary matter
    directions through the original source field map. The coframe, gauge,
    Lorentz and scalar slots are all kept; this is the original 289-coordinate
    matter-field restriction, not a gauge-only replacement. -/
def originalComplexDirection (v : Fin 289→ℂ) : ComplexDirection :=
  ⟨sourceField (fun j => (v j).re),sourceField (fun j => (v j).im)⟩

/-- A positive/negative pair of complex original fields as a canonical transfer
    pair. The two directions remain independent; the source's own opposite-dual
    two-time kernel governs them. -/
def originalTransferPair (positive negative : Fin 289→ℂ) : TransferPair :=
  ⟨originalComplexDirection positive,originalComplexDirection negative⟩

/-- The scalar four-point read of the canonical coframe mother: the first
    component is the Duhamel two-time kernel read, the second the direct mixed
    contact read which stays outside the age integral. -/
def originalScatteringPair (momentum : Fin 3→ℝ) (A B : TransferPair)
    (shift : Fin 3→ℝ) (time age : ℝ) : ℂ × ℂ :=
  (Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
    (Stage9DEF.Compatibility.responseMatrix
      (fieldMother momentum A B shift time age)),
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
    (Stage9DEF.Compatibility.responseMatrix
      (fieldContactMother momentum A B time)))

/-- The original scattering pair is the exact two ordered four-by-four CAR
    sums of the real-reader coefficients against the adjoint-shifted negative
    and positive complex-frequency legs, with the direct mixed contact read as
    second component. The source unit `packetNormalization` is fixed by the
    canonical packet; no extra observer normalization enters. -/
theorem original_scattering_pair_source (momentum : Fin 3→ℝ) (A B : TransferPair)
    (shift : Fin 3→ℝ) (time age : ℝ) :
    originalScatteringPair momentum A B shift time age=
      (packetNormalization momentum*Complex.I*
        ((∑ i : Fin 4,∑ j : Fin 4,
          orderedCARRead momentum
            (shiftCoefficients (adjointCoefficients
              (complexFrequencyCoefficients B.negative)) shift)
            (realReaderCoefficients A shift) (-shift) age time i j)-
          ∑ i : Fin 4,∑ j : Fin 4,
            orderedCARRead momentum (realReaderCoefficients A shift)
              (complexFrequencyCoefficients B.positive) shift time age i j),
        packetNormalization momentum*
          inner ℂ (Electromagnetic.CanonicalPacket.packet momentum)
            (fieldMixedContact A B time (Electromagnetic.CanonicalPacket.packet momentum))) := by
  rw [originalScatteringPair,fieldMother_fullCAR,fieldContactMother_read]

end LowEnergy.GaussComposite.PhysicalFullFieldScattering
