import H0mework.Arithmetic.RiemannMellinOrbit.MellinOrbitQuotient

/-!
# Zero-owned q-rich Mellin orbit functionals

The selected and reversal zero Mellin incidences generate separate q-rich
orbit relations and descended quotient functionals.  Each functional is
nonzero by the independent low-correction readback `1 / z`, so neither
quotient can be a vacuous zero carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization

noncomputable section

def selectedZeroMellinRelation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    mellinConvergentSubmodule (observation.coordinate / 2) :=
  ⟨generatedClozelGaussianRemainderKernel owner,
    (generatedZero_clozelGaussianRemainderKernel_hasMellin_zero
      observation nontrivial).1⟩

theorem selectedZeroMellinRelation_annihilated
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    mellinFunctional (observation.coordinate / 2)
        (selectedZeroMellinRelation observation nontrivial) = 0 :=
  (generatedZero_clozelGaussianRemainderKernel_hasMellin_zero
    observation nontrivial).2

def selectedZeroMellinOrbitQuotientFunctional
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QRichMellinOrbitQuotient
        (observation.coordinate / 2)
        (selectedZeroMellinRelation observation nontrivial) →ₗ[ℂ] ℂ :=
  qRichMellinOrbitQuotientFunctional
    (observation.coordinate / 2)
    (selectedZeroMellinRelation observation nontrivial)
    (selectedZeroMellinRelation_annihilated observation nontrivial)

theorem selectedZeroMellinOrbitQuotientFunctional_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedZeroMellinOrbitQuotientFunctional observation nontrivial ≠ 0 := by
  have strip :=
    observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
  apply qRichMellinOrbitQuotientFunctional_ne_zero
  rw [div_ofNat_re]
  linarith

def reversalZeroMellinRelation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    mellinConvergentSubmodule
      (coordinateReversal observation.coordinate / 2) :=
  ⟨generatedClozelGaussianRemainderKernel owner,
    (generatedZero_reversalClozelGaussianRemainderKernel_hasMellin_zero
      observation nontrivial).1⟩

theorem reversalZeroMellinRelation_annihilated
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    mellinFunctional
        (coordinateReversal observation.coordinate / 2)
        (reversalZeroMellinRelation observation nontrivial) = 0 :=
  (generatedZero_reversalClozelGaussianRemainderKernel_hasMellin_zero
    observation nontrivial).2

def reversalZeroMellinOrbitQuotientFunctional
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QRichMellinOrbitQuotient
        (coordinateReversal observation.coordinate / 2)
        (reversalZeroMellinRelation observation nontrivial) →ₗ[ℂ] ℂ :=
  qRichMellinOrbitQuotientFunctional
    (coordinateReversal observation.coordinate / 2)
    (reversalZeroMellinRelation observation nontrivial)
    (reversalZeroMellinRelation_annihilated observation nontrivial)

theorem reversalZeroMellinOrbitQuotientFunctional_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalZeroMellinOrbitQuotientFunctional observation nontrivial ≠ 0 := by
  have strip :=
    observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
  apply qRichMellinOrbitQuotientFunctional_ne_zero
  rw [div_ofNat_re]
  simp [coordinateReversal]
  linarith

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
