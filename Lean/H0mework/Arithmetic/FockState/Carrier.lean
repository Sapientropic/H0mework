import Mathlib.LinearAlgebra.TensorProduct.Basic
import H0mework.Arithmetic.CoPoisson.RelationQuotient

/-!
# Raw-colored degree-at-most-two particle--wave state

The parent carrier retains both raw theta/J-theta roles and an ordered
two-particle tensor sector.  Known Poisson relations and analytic coimages
remain downstream faces, so their inverse fibres are not erased here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFock

open CanonicalRiemann.ClozelGeneralizedDual
open CanonicalRiemann.ClozelGeneralizedDual.ThetaJRoleRepresentation

noncomputable section

abbrev IntegralOneParticle := IntegralScaleCarrier
abbrev ColoredWaveOne := JRoleCarrier
abbrev OrderedParticleTwo :=
  TensorProduct ℤ IntegralOneParticle IntegralOneParticle

/-- Raw colored degree-one sector plus ordered degree-two sector. -/
abbrev ParentCarrier := ColoredWaveOne × OrderedParticleTwo

def thetaInclusion : IntegralOneParticle →ₗ[ℤ] ParentCarrier :=
  (LinearMap.inl ℤ ColoredWaveOne OrderedParticleTwo).comp
    (LinearMap.inl ℤ IntegralOneParticle IntegralOneParticle)

def jThetaInclusion : IntegralOneParticle →ₗ[ℤ] ParentCarrier :=
  (LinearMap.inl ℤ ColoredWaveOne OrderedParticleTwo).comp
    (LinearMap.inr ℤ IntegralOneParticle IntegralOneParticle)

def pairInclusion : OrderedParticleTwo →ₗ[ℤ] ParentCarrier :=
  LinearMap.inr ℤ ColoredWaveOne OrderedParticleTwo

/-- The installed A1c selected/reversal carrier is the diagonal restriction
of the two raw wave colors. -/
def diagonalInclusion : IntegralOneParticle →ₗ[ℤ] ParentCarrier :=
  thetaInclusion + jThetaInclusion

def coloredWaveProjection : ParentCarrier →ₗ[ℤ] ColoredWaveOne :=
  LinearMap.fst ℤ ColoredWaveOne OrderedParticleTwo

def thetaProjection : ParentCarrier →ₗ[ℤ] IntegralOneParticle :=
  (LinearMap.fst ℤ IntegralOneParticle IntegralOneParticle).comp
    coloredWaveProjection

def jThetaProjection : ParentCarrier →ₗ[ℤ] IntegralOneParticle :=
  (LinearMap.snd ℤ IntegralOneParticle IntegralOneParticle).comp
    coloredWaveProjection

def pairProjection : ParentCarrier →ₗ[ℤ] OrderedParticleTwo :=
  LinearMap.snd ℤ ColoredWaveOne OrderedParticleTwo

@[simp] theorem thetaProjection_thetaInclusion
    (value : IntegralOneParticle) :
    thetaProjection (thetaInclusion value) = value :=
  rfl

@[simp] theorem jThetaProjection_jThetaInclusion
    (value : IntegralOneParticle) :
    jThetaProjection (jThetaInclusion value) = value :=
  rfl

@[simp] theorem pairProjection_pairInclusion
    (value : OrderedParticleTwo) :
    pairProjection (pairInclusion value) = value :=
  rfl

@[simp] theorem thetaProjection_diagonalInclusion
    (value : IntegralOneParticle) :
    thetaProjection (diagonalInclusion value) = value := by
  simp [diagonalInclusion, thetaProjection, coloredWaveProjection,
    thetaInclusion, jThetaInclusion]

@[simp] theorem jThetaProjection_diagonalInclusion
    (value : IntegralOneParticle) :
    jThetaProjection (diagonalInclusion value) = value := by
  simp [diagonalInclusion, jThetaProjection, coloredWaveProjection,
    thetaInclusion, jThetaInclusion]

section UniversalRead

variable {X : Type*} [AddCommGroup X] [Module ℤ X]

/-- Universal linear read assembled from two one-particle colors and one
ordered two-particle read. -/
def linearRead
    (theta jTheta : IntegralOneParticle →ₗ[ℤ] X)
    (pair : OrderedParticleTwo →ₗ[ℤ] X) : ParentCarrier →ₗ[ℤ] X :=
  (theta.coprod jTheta).coprod pair

@[simp] theorem linearRead_theta
    (theta jTheta : IntegralOneParticle →ₗ[ℤ] X)
    (pair : OrderedParticleTwo →ₗ[ℤ] X)
    (value : IntegralOneParticle) :
    linearRead theta jTheta pair (thetaInclusion value) = theta value := by
  simp [linearRead, thetaInclusion]

@[simp] theorem linearRead_jTheta
    (theta jTheta : IntegralOneParticle →ₗ[ℤ] X)
    (pair : OrderedParticleTwo →ₗ[ℤ] X)
    (value : IntegralOneParticle) :
    linearRead theta jTheta pair (jThetaInclusion value) = jTheta value := by
  simp [linearRead, jThetaInclusion]

@[simp] theorem linearRead_pair
    (theta jTheta : IntegralOneParticle →ₗ[ℤ] X)
    (pair : OrderedParticleTwo →ₗ[ℤ] X)
    (value : OrderedParticleTwo) :
    linearRead theta jTheta pair (pairInclusion value) = pair value := by
  simp [linearRead, pairInclusion]

/-- Any linear read agreeing on the three canonical sectors is the generated
universal read. -/
theorem linearRead_unique
    (theta jTheta : IntegralOneParticle →ₗ[ℤ] X)
    (pair : OrderedParticleTwo →ₗ[ℤ] X)
    (candidate : ParentCarrier →ₗ[ℤ] X)
    (theta_eq : candidate.comp thetaInclusion = theta)
    (jTheta_eq : candidate.comp jThetaInclusion = jTheta)
    (pair_eq : candidate.comp pairInclusion = pair) :
    candidate = linearRead theta jTheta pair := by
  apply LinearMap.ext
  rintro ⟨⟨left, right⟩, particles⟩
  have decomposition :
      ((⟨left, right⟩, particles) : ParentCarrier) =
        thetaInclusion left + jThetaInclusion right + pairInclusion particles := by
    ext <;> simp [thetaInclusion, jThetaInclusion, pairInclusion]
  have theta_at := LinearMap.congr_fun theta_eq left
  have jTheta_at := LinearMap.congr_fun jTheta_eq right
  have pair_at := LinearMap.congr_fun pair_eq particles
  change candidate (thetaInclusion left) = theta left at theta_at
  change candidate (jThetaInclusion right) = jTheta right at jTheta_at
  change candidate (pairInclusion particles) = pair particles at pair_at
  rw [decomposition, map_add, map_add, theta_at, jTheta_at, pair_at]
  simp [linearRead, thetaInclusion, jThetaInclusion, pairInclusion]

end UniversalRead

end

end ParticleWaveFock
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
