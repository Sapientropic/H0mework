import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedFiniteCutoffNative
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedFourier

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 140000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCellInverse

open BurnolPhysicalState OriginalRieszFinitePairing.CoPoisson.Ward
open CountedJointStrong
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open scoped Topology InnerProductSpace

local notation "R" => burnolDirectRightResolventCLM
local notation "Dilation" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "Cell" => BoundaryCountedFourier.dualEquiv

/-- Decode a full field from the two consecutive reverse counts of that same field. -/
def recoverOutput (N : Nat) (positive : 0 < N) (left right : BurnolL2) : BurnolL2 :=
  (Cell N positive).symm (right-left)

theorem recover_output (N : Nat) (positive : 0 < N) (y : BurnolL2) :
    recoverOutput N positive (DualSource.source N y) (DualSource.source (N+1) y) = y := by
  rw [recoverOutput, ← BoundaryCountedFourier.dualEquiv_apply N positive,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The same two paid cutoffs also recover the full Fourier field, at finite N. -/
theorem recover_wave (N : Nat) (positive : 0 < N) (w : BurnolL2) :
    (BoundaryCountedInverse.cellEquiv N positive).symm
      (FiniteForcing.source (N+1) w-FiniteForcing.source N w) = w := by
  rw [← BoundaryCountedInverse.cell_apply, ← BoundaryCountedInverse.cellEquiv_apply N positive,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The input is the inverse of the actual strong dilation equation of the recovered field. -/
def recoverInput (coordinate : BurnolCompletedMellinCoordinate) (y : BurnolL2) : BurnolL2 :=
  (-(1/2 : ℂ)) • (deriv (fun h : ℝ => Dilation h y) 0 + (coordinate.value-1/2) • y)

theorem recover_input (coordinate : BurnolCompletedMellinCoordinate) (x : BurnolL2) :
    recoverInput coordinate (R coordinate x) = x := by
  rw [recoverInput, (actual_resolvent_dilation_derivative coordinate x).deriv]
  module

/-- The action graph carries the analytic obligation of differentiating the recovered output. -/
def recoverIncidence (coordinate : BurnolCompletedMellinCoordinate)
    (N : Nat) (positive : 0 < N) (left right : BurnolL2) : BurnolL2 × BurnolL2 :=
  let y := recoverOutput N positive left right
  (recoverInput coordinate y,y)

theorem recover_incidence (coordinate : BurnolCompletedMellinCoordinate)
    (N : Nat) (positive : 0 < N) (x : BurnolL2) :
    recoverIncidence coordinate N positive (DualSource.source N (R coordinate x))
      (DualSource.source (N+1) (R coordinate x)) = (x,R coordinate x) := by
  unfold recoverIncidence
  rw [recover_output]
  exact congrArg (fun value : BurnolL2 => (value,R coordinate x)) (recover_input coordinate x)

/-- The signed Fourier generator is the same exact inverse in the wave coordinates. -/
def recoverWaveInput (coordinate : BurnolCompletedMellinCoordinate) (w : BurnolL2) : BurnolL2 :=
  (-(1/2 : ℂ)) • (deriv (fun h : ℝ => Dilation (-h) w) 0 + (coordinate.value-1/2) • w)

theorem recover_wave_input (coordinate : BurnolCompletedMellinCoordinate) (x : BurnolL2) :
    recoverWaveInput coordinate (F (R coordinate x)) = F x := by
  let y := R coordinate x
  let v := -((coordinate.value-1/2) • y + (2 : ℂ) • x)
  let transform := (F).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have derivative := transform.hasFDerivAt.comp_hasDerivAt 0
    (actual_resolvent_dilation_derivative coordinate x)
  change HasDerivAt (fun h : ℝ => F (Dilation h y)) (F v) 0 at derivative
  have orbit : (fun h : ℝ => F (Dilation h y)) = fun h : ℝ => Dilation (-h) (F y) :=
    funext (fun h => fourierL2_burnolMultiplicativeDilation h y)
  rw [orbit] at derivative
  change (-(1/2 : ℂ)) • (deriv (fun h : ℝ => Dilation (-h) (F y)) 0 +
      (coordinate.value-1/2) • F y) = F x
  rw [derivative.deriv]
  simp only [v, map_neg, map_add, map_smul]
  module

def recoverWaveIncidence (coordinate : BurnolCompletedMellinCoordinate)
    (N : Nat) (positive : 0 < N) (left right : BurnolL2) : BurnolL2 × BurnolL2 :=
  let w := (BoundaryCountedInverse.cellEquiv N positive).symm (right-left)
  (recoverWaveInput coordinate w,w)

theorem recover_wave_incidence (coordinate : BurnolCompletedMellinCoordinate)
    (N : Nat) (positive : 0 < N) (x : BurnolL2) :
    recoverWaveIncidence coordinate N positive (FiniteForcing.source N (F (R coordinate x)))
      (FiniteForcing.source (N+1) (F (R coordinate x))) = (F x, F (R coordinate x)) := by
  unfold recoverWaveIncidence
  rw [recover_wave]
  exact congrArg (fun value : BurnolL2 => (value,F (R coordinate x))) (recover_wave_input coordinate x)

/-- The actual reverse cell has the same inverse bound as the forward cell. -/
theorem recover_output_stable (N : Nat) (positive : 0 < N) (left right left' right' : BurnolL2) :
    ‖recoverOutput N positive left right-recoverOutput N positive left' right'‖ ≤
      ‖(right-left)-(right'-left')‖ / BoundaryCountedInverse.margin N := by
  let d := (right-left)-(right'-left')
  rw [recoverOutput, recoverOutput, ← map_sub]
  change ‖(F).symm ((BoundaryCountedInverse.cellEquiv N positive).symm (F d))‖ ≤
    ‖d‖ / BoundaryCountedInverse.margin N
  rw [LinearIsometryEquiv.norm_map, ← LinearIsometryEquiv.norm_map F d]
  exact BoundaryCountedInverse.cell_inverse_bound N positive (F d)

end CountedCellInverse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
