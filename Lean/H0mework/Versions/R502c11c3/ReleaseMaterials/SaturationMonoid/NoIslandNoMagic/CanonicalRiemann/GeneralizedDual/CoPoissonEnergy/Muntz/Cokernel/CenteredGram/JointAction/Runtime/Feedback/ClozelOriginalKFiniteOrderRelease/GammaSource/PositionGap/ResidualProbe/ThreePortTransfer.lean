import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Topological.ConservativePort.Transfer
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ThreePortCausal
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePowerWindow.Geometric

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.ThreePortTransfer

open BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace

open private opening_source from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ThreePortCausal
open private total_actual from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ThreePortFeedback
open private actual_step from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePowerWindow.Geometric

namespace Port
export SourceGeneratedCompressedUnitaryDefectPort.Feedback
  (action_bound field field_source field_visible eq_geometric_of_solve transfer returnStock transfer_energy visible)
end Port
namespace Read
export SaturationMonoid.OrthogonalSourceObservation (observe representative read_representative representative_orthogonal)
end Read
namespace Clock
export BurnolPhysicalState.OriginalRSourceJointContact.OutsideHistory.FinitePowerWindow
  (ratio ratio_norm_lt_one)
end Clock

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R" => burnolDirectRightResolventCLM
local notation "δ" => (sourceDamping c : ℂ)
local notation "columns" => ThreePortFibre.columns observation half
local notation "fees" => Read.observe columns
local notation "kernel" => LinearMap.ker (ContinuousLinearMap.toLinearMap fees)

def face : ClosedSubmodule ℂ BurnolL2 := ⟨kernelᗮ, (kernel).isClosed_orthogonal⟩

local notation "K" => face observation half
local notation "P" => Submodule.starProjection (ClosedSubmodule.toSubmodule K)
local notation "Q" => Submodule.starProjection (Submodule.orthogonal (ClosedSubmodule.toSubmodule K))

def cayley : BurnolL2 →ₗᵢ[ℂ] BurnolL2 :=
  { (sourceCayley c).toLinearMap with norm_map' := sourceCayley_norm c }

local notation "T" => cayley observation half
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "total" => ThreePortFeedback.NativePair.pairTotal
local notation "record" => ThreePortFeedback.encode observation nontrivial half

include nontrivial in
private theorem projection_is_gram (point : BurnolL2) :
    P point = Read.representative columns (fees point) := by
  let v := Read.representative columns (fees point)
  have visible : v ∈ (K).toSubmodule := by
    intro unobserved invisible
    exact inner_eq_zero_symm.mp
      (Read.representative_orthogonal columns (fees point) (LinearMap.mem_ker.mp invisible))
  have hidden : point - v ∈ kernel := by
    change fees (point-Read.representative columns (fees point)) = 0
    rw [map_sub, Read.read_representative columns (ThreePortFibre.columns_orthogonal observation nontrivial half)
      (ThreePortFibre.columns_live observation nontrivial half), sub_self]
  have orth : point - v ∈ (K).toSubmoduleᗮ := (kernel).le_orthogonal_orthogonal hidden
  have vanishes : P (point-v) = 0 := by
    rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal orth]
    rfl
  calc
    P point = P (v + (point-v)) := congrArg P (by module)
    _ = v := by rw [map_add, Submodule.starProjection_eq_self_iff.mpr visible, vanishes, add_zero]

include nontrivial in
private theorem fees_from_projection (point : BurnolL2) : fees (P point) = fees point := by
  rw [projection_is_gram observation nontrivial half]
  exact Read.read_representative columns (ThreePortFibre.columns_orthogonal observation nontrivial half)
    (ThreePortFibre.columns_live observation nontrivial half) _

/-- The frequency-domain forcing retains the same hidden field as the time-domain opening. -/
theorem actual_hidden_opening (ordinal : Nat) :
    Q (raw ordinal) = ThreePortCausal.opening observation nontrivial half depth ordinal := by
  have parts : P (raw ordinal) + Q (raw ordinal) = raw ordinal :=
    Submodule.starProjection_add_starProjection_orthogonal _
  rw [opening_source observation nontrivial half depth ordinal]
  change Q (raw ordinal) = raw ordinal - Read.representative columns (fees (raw ordinal))
  rw [projection_is_gram observation nontrivial half] at parts
  exact eq_sub_of_add_eq' parts

private def scale (parameter : BurnolCompletedMellinCoordinate) : ℂ := 1 - Clock.ratio c parameter

private theorem parameter_equation (parameter : BurnolCompletedMellinCoordinate) (point : BurnolL2) :
    R parameter point - Clock.ratio c parameter • T (R parameter point) =
      scale observation half parameter • R c point := by
  let z := Clock.ratio c parameter
  let U : BurnolL2 →L[ℂ] BurnolL2 := sourceCayley c
  let A : BurnolL2 →L[ℂ] BurnolL2 := 1 - z • U
  let B : BurnolL2 →L[ℂ] BurnolL2 := (1-z) • R c
  let G := SourceGeneratedCompressedUnitaryDefectPort.Feedback.geometric U z
  have original : R parameter * A = B := actual_step c parameter
  have bound : ‖U‖ ≤ 1 := Port.action_bound T
  have small : ‖z • U‖ < 1 := by
    rw [norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg z) bound).trans_lt (Clock.ratio_norm_lt_one c parameter)
  have invert : A*G = 1 := mul_neg_geom_series (z • U) small
  have same : Commute U (R c) :=
    (Commute.one_left (R c)).add_left ((Commute.refl (R c)).smul_left δ)
  have commute : Commute A B :=
    ((Commute.one_left (R c)).sub_left (same.smul_left z)).smul_right (1-z)
  have action : A * R parameter = B := calc
    _ = (A * R parameter) * (A * G) := by rw [invert, mul_one]
    _ = (A * (R parameter * A)) * G := by simp only [mul_assoc]
    _ = _ := by rw [original, commute.eq, mul_assoc, invert, mul_one]
  have written := congrArg (fun op : BurnolL2 →L[ℂ] BurnolL2 => op point) action
  change R parameter point - z • U (R parameter point) = (1-z) • R c point at written
  exact written

/-- The original write and its complete Model are the forcing for the parameter action. -/
private def forcing (parameter : BurnolCompletedMellinCoordinate) (ordinal : Nat) : BurnolL2 :=
  scale observation half parameter • total (ThreePortFeedback.recover observation nontrivial half
    (ThreePortFeedback.advance observation nontrivial half (record (input ordinal))))

private theorem forcing_source (parameter : BurnolCompletedMellinCoordinate) (ordinal : Nat) :
    forcing observation nontrivial half depth parameter ordinal =
      scale observation half parameter • R c (raw ordinal) := by
  rw [forcing, ThreePortFeedback.actual_advance observation nontrivial half depth,
    ThreePortFeedback.recover_encoded, total_actual observation nontrivial half depth,
    OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth ordinal]
  have same : OriginalKCombPhysicalAction.R observation nontrivial half (raw ordinal) = R c (raw ordinal) :=
    OriginalKCombCofinalRAction.original_R_direct observation nontrivial half (raw ordinal)
  exact congrArg (fun value : BurnolL2 => scale observation half parameter • value) same

attribute [local irreducible] face cayley forcing

def parameterField (parameter : BurnolCompletedMellinCoordinate) (ordinal : Nat) : BurnolL2 :=
  Port.field K T (Clock.ratio c parameter) (forcing observation nontrivial half depth parameter ordinal)

theorem actual_parameter_field (parameter : BurnolCompletedMellinCoordinate) (ordinal : Nat) :
    parameterField observation nontrivial half depth parameter ordinal = R parameter (raw ordinal) := by
  let z := Clock.ratio c parameter
  let u := forcing observation nontrivial half depth parameter ordinal
  let x := R parameter (raw ordinal)
  let act : BurnolL2 →L[ℂ] BurnolL2 := LinearIsometry.toContinuousLinearMap T
  have disk : ‖z‖ < 1 := Clock.ratio_norm_lt_one c parameter
  have solved : x - z • act x = u :=
    (parameter_equation observation half parameter (raw ordinal)).trans
      (forcing_source observation nontrivial half depth parameter ordinal).symm
  have inverse : x = SourceGeneratedCompressedUnitaryDefectPort.Feedback.geometric act z u :=
    Port.eq_geometric_of_solve act (Port.action_bound T) disk solved
  change Port.field K T z u = x
  exact (Port.field_source K T disk u).trans inverse.symm

def parameterFees (parameter : BurnolCompletedMellinCoordinate) (ordinal : Nat) : Fin 3 → ℂ :=
  fees (Port.visible K T (Clock.ratio c parameter) (forcing observation nontrivial half depth parameter ordinal) : BurnolL2)

theorem actual_parameter_fees (parameter : BurnolCompletedMellinCoordinate) (ordinal : Nat) :
    parameterFees observation nontrivial half depth parameter ordinal =
      fees (R parameter (raw ordinal)) := by
  have projected := Port.field_visible K T (Clock.ratio_norm_lt_one c parameter)
    (forcing observation nontrivial half depth parameter ordinal)
  unfold parameterFees
  rw [← projected]
  change fees (P (parameterField observation nontrivial half depth parameter ordinal)) = _
  rw [fees_from_projection observation nontrivial half, actual_parameter_field observation nontrivial half depth]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.ThreePortTransfer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
