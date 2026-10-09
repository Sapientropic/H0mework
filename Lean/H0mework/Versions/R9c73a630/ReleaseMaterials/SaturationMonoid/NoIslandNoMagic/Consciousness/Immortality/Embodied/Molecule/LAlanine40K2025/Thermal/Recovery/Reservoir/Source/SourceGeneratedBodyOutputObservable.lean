import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.SourceGeneratedBodyMeasurementChannel
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.BodyMeasurementTraceDual

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement

open Load.Source BodyKernel
noncomputable section

def sourceOutputObservable (O : LoadedJoint) : LoadedJoint :=
  inverseTraceObservable sourceChannelEquiv O

theorem sourceOutputObservable_hermitian (O : LoadedJoint) (hermitian : O.IsHermitian) :
    (sourceOutputObservable O).IsHermitian :=
  inverseTraceObservable_hermitian sourceChannelEquiv sourceChannel_inverse_star O hermitian

theorem sourceOutputObservable_read (O rho : LoadedJoint) :
    (sourceOutputObservable O * sourceBodyChannel rho).trace = (O * rho).trace := by
  have read := inverseTraceObservable_read sourceChannelEquiv O rho
  rw [sourceChannelEquiv_apply] at read
  exact read

theorem sourceOutputObservable_energy (O rho : LoadedJoint) :
    Collision.energy (sourceOutputObservable O) (sourceBodyChannel rho) = Collision.energy O rho := by
  have read := inverseTraceObservable_energy sourceChannelEquiv O rho
  rw [sourceChannelEquiv_apply] at read
  exact read

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
