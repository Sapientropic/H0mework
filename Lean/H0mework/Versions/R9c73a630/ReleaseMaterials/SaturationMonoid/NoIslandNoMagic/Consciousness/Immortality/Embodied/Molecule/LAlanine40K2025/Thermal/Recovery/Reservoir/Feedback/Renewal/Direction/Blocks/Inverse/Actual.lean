import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Inverse.Core
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Projection
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.SourceGeneratedBodyOutputObservable

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.BasisInverse
open Collision Load.Source
open scoped Matrix ComplexOrder
noncomputable section

section Unitary
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem conjugation_pair (U : Matrix.unitaryGroup ι ℂ) (O rho : Matrix ι ι ℂ) :
    (Quantum.conjugation U O * Quantum.conjugation U rho).trace = (O * rho).trace := by
  have product := map_mul (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) O rho
  change Quantum.conjugation U (O * rho) = Quantum.conjugation U O * Quantum.conjugation U rho at product
  rw [← product, Quantum.conjugation_trace]
end Unitary

def actualAngle : ℝ := Real.pi / 2 - (Propagation.Producer.nativeClockStep : ℝ)

def actualOutput (O : LoadedJoint) : LoadedJoint :=
  Quantum.conjugation BodyKernel.bodyFree
    (bodyInverse Spectral.Projection.excitedIndex (Real.cos actualAngle) (Real.sin actualAngle) O)

attribute [local irreducible] BodyKernel.sourceBodyChannel Measurement.sourceOutputObservable
  BodyKernel.bodyFree Spectral.Projection.excitedIndex

theorem actualOutput_read (O rho : LoadedJoint) :
    (actualOutput O * BodyKernel.sourceBodyChannel rho).trace = (O * rho).trace := by
  rw [actualOutput, BodyKernel.sourceBodyChannel_factor, Spectral.Projection.actual_donor]
  change (Quantum.conjugation BodyKernel.bodyFree _ * Quantum.conjugation BodyKernel.bodyFree _).trace = _
  rw [conjugation_pair]
  exact bodyInverse_trace Spectral.Projection.excitedIndex actualAngle BodyKernel.source_cos_nonzero O rho

theorem original_inverse_formula (O : LoadedJoint) :
    Measurement.sourceOutputObservable O = actualOutput O := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro rho
  obtain ⟨input, generated⟩ := Measurement.sourceChannelEquiv.surjective rho
  rw [Measurement.sourceChannelEquiv_apply] at generated
  rw [← generated, Measurement.sourceOutputObservable_read, actualOutput_read]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.BasisInverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
