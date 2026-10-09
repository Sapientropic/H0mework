import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.SourceGeneratedBodyOutputObservable
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.BoundedBodyMeasurement

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement

open Load.Source BodyKernel Collision
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] sourceBodyChannel sourceOutputObservable

def sourceMeasurementEffect (O : LoadedJoint) : LoadedJoint :=
  boundedEffect (sourceOutputObservable O)

def sourceMeasurementDecode (O : LoadedJoint) (z : ℝ) : ℝ :=
  decodeMeasurement (sourceOutputObservable O) z

theorem sourceMeasurement_lawful (O : LoadedJoint) (hermitian : O.IsHermitian) :
    (sourceMeasurementEffect O).PosSemidef ∧ (1 - sourceMeasurementEffect O).PosSemidef :=
  ⟨boundedEffect_positive _ (sourceOutputObservable_hermitian O hermitian),
    boundedEffect_complement_positive _ (sourceOutputObservable_hermitian O hermitian)⟩

theorem sourceMeasurement_probability (O rho : LoadedJoint) (hermitian : O.IsHermitian)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    0 ≤ energy (sourceMeasurementEffect O) (sourceBodyChannel rho) ∧
      energy (sourceMeasurementEffect O) (sourceBodyChannel rho) ≤ 1 :=
  boundedEffect_probability _ _ (sourceOutputObservable_hermitian O hermitian)
    (sourceChannel_positive rho positive) ((sourceChannel_trace rho).trans normalized)

theorem sourceMeasurement_contrast (O rho : LoadedJoint) (normalized : rho.trace = 1) :
    energy (sourceMeasurementEffect O) (sourceBodyChannel rho) =
      1 / 2 + energy O rho / (2 * measurementScale (sourceOutputObservable O)) := by
  rw [sourceMeasurementEffect, boundedEffect_read _ _ ((sourceChannel_trace rho).trans normalized),
    sourceOutputObservable_energy]

theorem sourceMeasurement_exact (O rho : LoadedJoint) (normalized : rho.trace = 1) :
    sourceMeasurementDecode O (energy (sourceMeasurementEffect O) (sourceBodyChannel rho)) = energy O rho := by
  unfold sourceMeasurementDecode sourceMeasurementEffect
  rw [decodeMeasurement_exact _ _ ((sourceChannel_trace rho).trans normalized), sourceOutputObservable_energy]

theorem sourceMeasurement_error (O rho : LoadedJoint) (normalized : rho.trace = 1)
    (z eps : ℝ) (measured : |z - energy (sourceMeasurementEffect O) (sourceBodyChannel rho)| ≤ eps) :
    |sourceMeasurementDecode O z - energy O rho| ≤
      2 * measurementScale (sourceOutputObservable O) * eps := by
  have bound := decodeMeasurement_error (sourceOutputObservable O) (sourceBodyChannel rho)
    ((sourceChannel_trace rho).trans normalized) z eps measured
  rw [sourceOutputObservable_energy] at bound
  exact bound

theorem sourceMeasurement_actual (O : LoadedJoint) :
    sourceMeasurementDecode O
      (energy (sourceMeasurementEffect O) (Incidence.bodyRead (Current.supplyNext Current.initial).joint)) =
        energy O Source.received.joint := by
  rw [← sourceBodyChannel_actual]
  exact sourceMeasurement_exact O Source.received.joint Source.received.normalized

theorem sourceMeasurement_actual_error (O : LoadedJoint) (z eps : ℝ)
    (measured : |z - energy (sourceMeasurementEffect O)
      (Incidence.bodyRead (Current.supplyNext Current.initial).joint)| ≤ eps) :
    |sourceMeasurementDecode O z - energy O Source.received.joint| ≤
      2 * measurementScale (sourceOutputObservable O) * eps := by
  rw [← sourceBodyChannel_actual] at measured
  exact sourceMeasurement_error O Source.received.joint Source.received.normalized z eps measured

theorem sourceGeneratedBodyMeasurement :
    (∀ O hermitian, type_of% (sourceMeasurement_lawful O hermitian)) ∧
    (∀ O rho hermitian positive normalized,
      type_of% (sourceMeasurement_probability O rho hermitian positive normalized)) ∧
    (∀ O rho normalized, type_of% (sourceMeasurement_contrast O rho normalized)) ∧
    (∀ O, type_of% (sourceMeasurement_actual O)) ∧
    (∀ O z eps measured, type_of% (sourceMeasurement_actual_error O z eps measured)) :=
  ⟨sourceMeasurement_lawful, sourceMeasurement_probability, sourceMeasurement_contrast,
    sourceMeasurement_actual, sourceMeasurement_actual_error⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
