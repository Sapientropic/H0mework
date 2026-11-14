import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedWordInverse
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence.Consumer

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

open BurnolPhysicalState

namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedNativeBeta

open OriginalKCofinalFullBranchFibre.KernelWrite

namespace WI
export BoundaryCountedWordInverse (equiv equiv_source action_commutes)
end WI
namespace Rec
export NativeDelta.BetaDecoder.Recurrence (updatedBranches original_updated_four_R original_updated_total)
end Rec

local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

abbrev Input := BurnolL2 × BurnolL2
abbrev Branches := Input × Input

private def pairChart (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) : Input ≃L[ℂ] Input :=
  (WI.equiv coordinate n).prodCongr (WI.equiv coordinate n)

def branchChart (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) : Branches ≃L[ℂ] Branches :=
  (pairChart coordinate n).prodCongr (pairChart coordinate n)

/-- The two original ports act on finite word coordinates by transport through the same inverse. -/
private def split (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) : BurnolL2 →L[ℂ] Input :=
  let chart := WI.equiv coordinate n
  (chart.conjContinuousAlgEquiv P).prod (chart.conjContinuousAlgEquiv O)

def total (branches : Branches) : BurnolL2 :=
  (branches.1.1+branches.1.2)+(branches.2.1+branches.2.2)

private theorem total_chart (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (branches : Branches) :
    total (branchChart coordinate n branches) = WI.equiv coordinate n (total branches) := by
  simp only [total, branchChart, pairChart, ContinuousLinearEquiv.prodCongr_apply, map_add]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R" => OriginalKCombPhysicalAction.R observation nontrivial half
local notation "F" => OriginalKCombFullResidualAction.branches observation nontrivial half

private theorem R_chart (n : Nat) (source : BurnolL2) :
    R (WI.equiv c n source) = WI.equiv c n (R source) := by
  let W := BoundaryCountedDivision.commonWord c n
  let A := burnolDirectRightResolventCLM c
  have commutes := congrArg (fun op : BurnolL2 →L[ℂ] BurnolL2 => op source)
    (WI.action_commutes c c n).eq
  change A (W source) = W (A source) at commutes
  have direct (value : BurnolL2) : R value = A value :=
    OriginalKCombCofinalRAction.original_R_direct observation nontrivial half value
  simpa only [WI.equiv_source, direct] using commutes

/-- Execute the original R on each encoded input and resolve its original two ports. -/
def action (n : Nat) : Input →L[ℂ] Branches :=
  let one := (split c n).comp R
  one.prodMap one

private theorem split_source (n : Nat) (source : BurnolL2) :
    split c n (R (WI.equiv c n source)) =
      (WI.equiv c n (P (R source)),WI.equiv c n (O (R source))) := by
  rw [R_chart observation nontrivial half]
  simp only [split, ContinuousLinearMap.prod_apply, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply]

theorem action_source (n : Nat) (source : Input) :
    action observation nontrivial half n (pairChart c n source) = branchChart c n (F source) :=
  Prod.ext (split_source observation nontrivial half n source.1)
    (split_source observation nontrivial half n source.2)

variable (depth : Nat)

local notation "increment" => NativeDelta.incrementInput observation nontrivial half depth
local notation "inverse" => NativeDelta.inverseBranches observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

/-- The input is the dependent increment of the original paid NativeSigma boundary. -/
def sigma (ordinal n : Nat) : Branches :=
  action observation nontrivial half n (pairChart c n (increment ordinal))

theorem sigma_source (ordinal n : Nat) :
    sigma observation nontrivial half depth ordinal n = branchChart c n (F (increment ordinal)) :=
  action_source observation nontrivial half n (increment ordinal)

theorem sigma_inverse (ordinal n : Nat) :
    (branchChart c n).symm (sigma observation nontrivial half depth ordinal n) = inverse ordinal := by
  rw [sigma_source, ContinuousLinearEquiv.symm_apply_apply, NativeDelta.actual_inverse_branches]

/-- The existing full branch readback independently recovers both actual input coordinates. -/
theorem sigma_readback (ordinal n : Nat) :
    OriginalKCofinalFullBranchFibre.branchReadback observation nontrivial half
      ((branchChart c n).symm (sigma observation nontrivial half depth ordinal n)) = increment ordinal := by
  rw [sigma_inverse]
  exact NativeDelta.actual_inverse_source_readback observation nontrivial half depth ordinal

/-- The native beta update has two separately generated receipt contributions. -/
def beta (ordinal n : Nat) : Branches :=
  sigma observation nontrivial half depth (ordinal+1) n+sigma observation nontrivial half depth (ordinal+2) n

theorem beta_source (ordinal n : Nat) :
    beta observation nontrivial half depth ordinal n =
      branchChart c n (Rec.updatedBranches observation nontrivial half depth ordinal) := by
  rw [beta, sigma_source, sigma_source, ← map_add, Rec.original_updated_four_R]

/-- The same finite inverse decodes the installed following beta with its four branches intact. -/
theorem beta_inverse (ordinal n : Nat) :
    (branchChart c n).symm (beta observation nontrivial half depth ordinal n) =
      Rec.updatedBranches observation nontrivial half depth ordinal := by
  rw [beta_source, ContinuousLinearEquiv.symm_apply_apply]

theorem beta_total (ordinal n : Nat) :
    total (beta observation nontrivial half depth ordinal n) =
      WI.equiv c n (raw (ordinal+3)-raw (ordinal+1)) := by
  rw [beta_source, total_chart]
  exact congrArg (WI.equiv c n) (Rec.original_updated_total observation nontrivial half depth ordinal)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedNativeBeta
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
