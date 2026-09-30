import H0mework.Versions.Y.Arithmetic.RieszFiniteSource.Finite.Receipt

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction

open BurnolPhysicalState
noncomputable section

/-- The coordinate is recovered from the source projection of one zero
observation.  The right-half proof is a fibre, not another source value. -/
def originalKCoordinate
    (coordinate : ℂ) (belowOne : coordinate.re < 1)
    (rightHalf : 1 / 2 < coordinate.re) :
    BurnolCompletedMellinCoordinate :=
  ⟨coordinate, rightHalf, belowOne⟩

/-- A receipt can enter this face only as the original finite-source
generation at the exact observation coordinate. -/
abbrev OriginalKReceiptAt
    (coordinate : ℂ) (zero : riemannZeta coordinate = 0)
    (belowOne : coordinate.re < 1)
    (rightHalf : 1 / 2 < coordinate.re) :=
  { receipt : BurnolPhysicalState.OriginalRieszFiniteSource.Receipt //
      receipt = BurnolPhysicalState.OriginalRieszFiniteSource.Receipt.generate
        (originalKCoordinate coordinate belowOne rightHalf) zero }

structure OriginalKSourceFace where
  coordinate : ℂ
  zero : riemannZeta coordinate = 0
  belowOne : coordinate.re < 1
  receiptAt : (rightHalf : 1 / 2 < coordinate.re) →
    OriginalKReceiptAt coordinate zero belowOne rightHalf

def OriginalKSourceFace.generate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    OriginalKSourceFace where
  coordinate := observation.coordinate
  zero := observation.mathlibZero
  belowOne := (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial).2
  receiptAt := fun rightHalf =>
    ⟨BurnolPhysicalState.OriginalRieszFiniteSource.Receipt.generate
      (originalKCoordinate observation.coordinate
        (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial).2
        rightHalf)
      observation.mathlibZero, rfl⟩

end
end IntegralGraphJointAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
