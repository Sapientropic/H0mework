import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedBivariateTailPrice
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97CommonPrincipal

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97JointTail
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb
open ActualSourcePreparedBivariateTailPrice ActualSourcePreparedMatterClockBalance ActualSourcePreparedClockReducedPencil
open ActualSourcePreparedSchur97Polynomial ActualSourcePreparedSchur97Cofactor
open scoped Matrix BigOperators

/-- The complete source balance keeps its original bivariate support and
therefore has a source-generated first clock coefficient plus a tail budget. -/
def sourceSchur97BalanceTailMass (event : DressedEvent) (n : PhysicalMomentum) : ℝ :=
  clockTailMass (sourceMatterClockBalanceNumerator event n)

def sourceSchur97DeterminantTailMass (event : DressedEvent) (n : PhysicalMomentum) : ℝ :=
  clockTailMass (sourceSchur97Determinant event n)

theorem source_schur97_balance_tail_price (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (spatial : ‖(eps:ℂ)‖≤1) (clock : ‖(sigma:ℂ)‖≤1) :
    ‖sourceClockEval eps sigma (sourceMatterClockBalanceNumerator event n)-
      ((sourceMatterClockBalanceNumerator event n).coeff 0).eval (eps:ℂ)‖ ≤
      sourceSchur97BalanceTailMass event n*‖(sigma:ℂ)‖ := by
  exact bivariate_clock_tail_price _ _ _ spatial clock

theorem source_schur97_determinant_tail_price (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (spatial : ‖(eps:ℂ)‖≤1) (clock : ‖(sigma:ℂ)‖≤1) :
    ‖sourceClockEval eps sigma (sourceSchur97Determinant event n)-
      ((sourceSchur97Determinant event n).coeff 0).eval (eps:ℂ)‖ ≤
      sourceSchur97DeterminantTailMass event n*‖(sigma:ℂ)‖ := by
  exact bivariate_clock_tail_price _ _ _ spatial clock

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97JointTail
