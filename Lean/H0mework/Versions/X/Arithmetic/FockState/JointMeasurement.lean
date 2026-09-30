import H0mework.Versions.X.Arithmetic.FockState.Charge

/-!
# Zero-free joint particle--wave measurement

The parent is measured before any zero observation: its faithful raw theta
coimage and unconditional particle charge are sibling coordinates of one
linear read.  The kernel is the information lost by that measurement; the
quotient by the kernel is its faithful observable coimage.  The particle-only
coimage is a generated restriction of the joint observable coimage.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFock

open CanonicalRiemann.ClozelGeneralizedDual.ThetaJRoleRelationQuotient
open SourceGeneratedScalarDifferentialResidual

noncomputable section

abbrev JointMeasurementTarget :=
  JRoleFaithfulCoimage × AdditiveChargeCarrier

/-- Zero-free parent measurement: coherent relation coimage and discrete
charge are read at once. -/
def jointMeasurement : ParentCarrier →ₗ[ℤ] JointMeasurementTarget :=
  faithfulThetaCoimageRead.prod particleMeasurement

@[simp] theorem jointMeasurement_wave_read (state : ParentCarrier) :
    (jointMeasurement state).1 = faithfulThetaCoimageRead state :=
  rfl

@[simp] theorem jointMeasurement_particle_read (state : ParentCarrier) :
    (jointMeasurement state).2 = particleMeasurement state :=
  rfl

@[simp] theorem jointMeasurement_particleSector
    (particles : OrderedParticleTwo) :
    jointMeasurement (pairInclusion particles) =
      (0, pairCharge particles) := by
  ext
  · simp [jointMeasurement, faithfulThetaCoimageRead,
      coloredWaveProjection, pairInclusion]
  · simp [jointMeasurement, particleMeasurement]

/-- Information erased by the joint measurement. -/
abbrev JointMeasurementKernel : Submodule ℤ ParentCarrier :=
  LinearMap.ker jointMeasurement

/-- The full affine inverse fibre over one observed coordinate. -/
abbrev JointMeasurementFibreAt (observed : JointMeasurementTarget) :=
  { state : ParentCarrier // jointMeasurement state = observed }

def measuredStateFibre (state : ParentCarrier) :
    JointMeasurementFibreAt (jointMeasurement state) :=
  ⟨state, rfl⟩

/-- Two parent states have the same observable coordinate exactly when their
difference lies in the lost-information kernel. -/
theorem jointMeasurement_eq_iff_sub_mem_kernel
    (left right : ParentCarrier) :
    jointMeasurement left = jointMeasurement right ↔
      left - right ∈ JointMeasurementKernel := by
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- Faithful observable quotient.  This is not the lost inverse fibre; that
fibre is `JointMeasurementKernel` (or a translate of it). -/
abbrev JointMeasurementCoimage := ResidualCarrier jointMeasurement

def jointMeasurementCoimage :
    ParentCarrier →ₗ[ℤ] JointMeasurementCoimage :=
  canonicalResidual jointMeasurement

theorem jointMeasurementCoimage_zero_iff (state : ParentCarrier) :
    jointMeasurementCoimage state = 0 ↔ jointMeasurement state = 0 :=
  canonicalResidual_eq_zero_iff jointMeasurement state

theorem jointMeasurementCoimage_universal
    {Q : Type*} [AddCommGroup Q] [Module ℤ Q]
    (read : ParentCarrier →ₗ[ℤ] Q)
    (compatible : LinearMap.ker jointMeasurement ≤ LinearMap.ker read) :
    ∃! factor : JointMeasurementCoimage →ₗ[ℤ] Q,
      factor.comp jointMeasurementCoimage = read :=
  universal_factorization jointMeasurement read compatible

theorem jointMeasurement_ker_le_particleMeasurement_ker :
    LinearMap.ker jointMeasurement ≤ LinearMap.ker particleMeasurement := by
  intro state joint_zero
  have particle_zero := congrArg Prod.snd joint_zero
  simpa using particle_zero

theorem jointMeasurement_ker_le_particleCoimage_ker :
    LinearMap.ker jointMeasurement ≤
      LinearMap.ker particleMeasurementCoimage := by
  intro state joint_zero
  apply (particleMeasurementCoimage_zero_iff state).mpr
  exact jointMeasurement_ker_le_particleMeasurement_ker joint_zero

/-- The former particle-only observable coimage is a canonical restriction of
the joint parent observable coimage. -/
noncomputable def jointToParticleCoimage :
    JointMeasurementCoimage →ₗ[ℤ] ParticleMeasurementCoimage :=
  Classical.choose (jointMeasurementCoimage_universal
    particleMeasurementCoimage
    jointMeasurement_ker_le_particleCoimage_ker)

theorem jointToParticleCoimage_comp :
    jointToParticleCoimage.comp jointMeasurementCoimage =
      particleMeasurementCoimage :=
  (Classical.choose_spec (jointMeasurementCoimage_universal
    particleMeasurementCoimage
    jointMeasurement_ker_le_particleCoimage_ker)).1

end

end ParticleWaveFock
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
