import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.BodyMeasurementLinearMap
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.SourceGeneratedBodyChannel

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement

open Load.Source BodyKernel
open scoped Matrix ComplexOrder
noncomputable section

def sourceChannelLinear : LoadedJoint →ₗ[ℂ] LoadedJoint where
  toFun := sourceBodyChannel
  map_add' left right := by
    unfold sourceBodyChannel
    simpa only [pulseBodyLinear_apply] using
      (pulseBodyLinear Source.donor (Current.pulse (Propagation.Producer.nativeClockStep : ℝ))).map_add left right
  map_smul' c rho := by
    unfold sourceBodyChannel
    simpa only [pulseBodyLinear_apply, RingHom.id_apply] using
      (pulseBodyLinear Source.donor (Current.pulse (Propagation.Producer.nativeClockStep : ℝ))).map_smul c rho

attribute [local irreducible] sourceBodyChannel

theorem sourceChannelLinear_injective : Function.Injective sourceChannelLinear := by
  intro left right same
  change sourceBodyChannel left = sourceBodyChannel right at same
  exact sourceBodyChannel_injective same

def sourceChannelEquiv : LoadedJoint ≃ₗ[ℂ] LoadedJoint :=
  LinearEquiv.ofInjectiveEndo sourceChannelLinear sourceChannelLinear_injective

theorem sourceChannelEquiv_apply (rho : LoadedJoint) :
    sourceChannelEquiv rho = sourceBodyChannel rho := rfl

theorem sourceChannel_trace (rho : LoadedJoint) :
    (sourceBodyChannel rho).trace = rho.trace := by
  rw [sourceBodyChannel, Incidence.bodyRead_trace, Quantum.conjugation_trace,
    Incidence.receivedJoint_trace, Source.donor_trace, mul_one]

theorem sourceChannel_positive (rho : LoadedJoint) (positive : rho.PosSemidef) :
    (sourceBodyChannel rho).PosSemidef := by
  unfold sourceBodyChannel
  exact Incidence.bodyRead_positive _ (Quantum.conjugation_posSemidef _ _
    (Incidence.receivedJoint_positive _ _ positive Source.donor_positive))

theorem sourceChannel_star (rho : LoadedJoint) :
    sourceBodyChannel (star rho) = star (sourceBodyChannel rho) := by
  unfold sourceBodyChannel
  simpa only [pulseBodyLinear_apply] using
    pulseBodyLinear_star Source.donor Source.donor_positive.isHermitian
      (Current.pulse (Propagation.Producer.nativeClockStep : ℝ)) rho

theorem sourceChannel_inverse_star (rho : LoadedJoint) :
    sourceChannelEquiv.symm (star rho) = star (sourceChannelEquiv.symm rho) := by
  apply sourceChannelEquiv.injective
  change sourceChannelEquiv (sourceChannelEquiv.symm (star rho)) =
    sourceBodyChannel (star (sourceChannelEquiv.symm rho))
  rw [sourceChannel_star]
  change sourceChannelEquiv (sourceChannelEquiv.symm (star rho)) =
    star (sourceChannelEquiv (sourceChannelEquiv.symm rho))
  simp

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
