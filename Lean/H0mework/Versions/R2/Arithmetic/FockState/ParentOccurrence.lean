import H0mework.Versions.R2.Arithmetic.EulerGlobal.CoordinateGerm
import H0mework.Arithmetic.FockState.Carrier
import H0mework.Arithmetic.CoPoisson.RoleRepresentation

/-!
# Global-germ-owned particle--wave parent occurrence

The determinant-generated global germ carries the canonical raw Fock
coordinate maps and its zero-free theta, presented, coimage, and remainder
reads.  The payload contains no zero observation or particle detector result.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFock

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open CanonicalRiemann
open CanonicalRiemann.ClozelGeneralizedDual
open CanonicalRiemann.ClozelGeneralizedDual.ThetaJRoleRepresentation
open CanonicalRiemann.ClozelGeneralizedDual.ThetaJRoleRelationQuotient
open CanonicalRiemann.ClozelGeneralizedDual.GlobalCoPoissonRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

def rawThetaRead : ParentCarrier →ₗ[ℤ] ComplexTempered :=
  representation.comp coloredWaveProjection

def poissonPresentedRead : ParentCarrier →ₗ[ℤ] PresentedCarrier :=
  presentedProjection.comp coloredWaveProjection

def faithfulThetaCoimageRead :
    ParentCarrier →ₗ[ℤ] JRoleFaithfulCoimage :=
  coimageProjection.comp coloredWaveProjection

def globalRemainderRead : ParentCarrier →ₗ[ℤ] ComplexTempered :=
  remainderRole.comp thetaProjection

abbrev GlobalParentOwner :=
  FactorizationPayload × GeneratedGlobalDeterminantCoordinateGerm

/-- Source-generated interface indexed by its exact global-germ owner. -/
structure GeneratedParentInterface (owner : GlobalParentOwner) where
  private mk ::
  globalCoefficients : ArithmeticFunction ℚ
  thetaCoordinate : IntegralOneParticle →ₗ[ℤ] ParentCarrier
  jThetaCoordinate : IntegralOneParticle →ₗ[ℤ] ParentCarrier
  pairCoordinate : OrderedParticleTwo →ₗ[ℤ] ParentCarrier
  diagonalCoordinate : IntegralOneParticle →ₗ[ℤ] ParentCarrier
  thetaRead : ParentCarrier →ₗ[ℤ] IntegralOneParticle
  jThetaRead : ParentCarrier →ₗ[ℤ] IntegralOneParticle
  pairRead : ParentCarrier →ₗ[ℤ] OrderedParticleTwo
  thetaDistributionRead : ParentCarrier →ₗ[ℤ] ComplexTempered
  presentedRead : ParentCarrier →ₗ[ℤ] PresentedCarrier
  coimageRead : ParentCarrier →ₗ[ℤ] JRoleFaithfulCoimage
  remainderRead : ParentCarrier →ₗ[ℤ] ComplexTempered
  primePowerCoordinate : Nat.Primes → Nat → ParentCarrier

def GeneratedParentInterface.generate (owner : GlobalParentOwner) :
    GeneratedParentInterface owner :=
  ⟨owner.2.coefficients,
    thetaInclusion, jThetaInclusion, pairInclusion, diagonalInclusion,
    thetaProjection, jThetaProjection, pairProjection,
    rawThetaRead, poissonPresentedRead, faithfulThetaCoimageRead,
    globalRemainderRead,
    fun prime exponent =>
      thetaInclusion (delta (primePowerUnit prime exponent))⟩

@[simp] theorem GeneratedParentInterface.generate_globalCoefficients
    (owner : GlobalParentOwner) :
    (GeneratedParentInterface.generate owner).globalCoefficients =
      owner.2.coefficients :=
  rfl

@[simp] theorem GeneratedParentInterface.generate_thetaCoordinate
    (owner : GlobalParentOwner) :
    (GeneratedParentInterface.generate owner).thetaCoordinate = thetaInclusion :=
  rfl

@[simp] theorem GeneratedParentInterface.generate_diagonalCoordinate
    (owner : GlobalParentOwner) :
    (GeneratedParentInterface.generate owner).diagonalCoordinate =
      diagonalInclusion :=
  rfl

@[simp] theorem GeneratedParentInterface.generate_pairCoordinate
    (owner : GlobalParentOwner) :
    (GeneratedParentInterface.generate owner).pairCoordinate = pairInclusion :=
  rfl

abbrev GlobalParentPayload :=
  Σ owner : GlobalParentOwner, GeneratedParentInterface owner

/-- The canonical parent is a dependent face of the literal determinant
germ occurrence. -/
def globalParentOccurrence :
    RootedAccountedUnfolding GlobalParentPayload :=
  globalGermOccurrence.map fun owner =>
    ⟨owner, GeneratedParentInterface.generate owner⟩

theorem globalParentOccurrence_projects :
    globalParentOccurrence.map Sigma.fst = globalGermOccurrence := by
  rw [globalParentOccurrence, RootedAccountedUnfolding.map_map]
  change globalGermOccurrence.map id = globalGermOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem globalParentOccurrence_projects_to_seed :
    (globalParentOccurrence.map Sigma.fst).map
        (fun owner : GlobalParentOwner => owner.1) = seedOccurrence := by
  rw [globalParentOccurrence_projects, globalGermOccurrence_projects]

@[simp] theorem globalParentOccurrence_root_interface :
    globalParentOccurrence.root.2 =
      GeneratedParentInterface.generate globalGermOccurrence.root :=
  rfl

end

end ParticleWaveFock
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
