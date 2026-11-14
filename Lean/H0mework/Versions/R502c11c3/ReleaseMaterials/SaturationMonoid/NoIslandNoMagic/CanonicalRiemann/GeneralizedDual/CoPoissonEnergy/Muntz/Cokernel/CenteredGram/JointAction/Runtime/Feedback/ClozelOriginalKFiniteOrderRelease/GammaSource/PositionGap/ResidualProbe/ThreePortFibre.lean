import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Hilbert.OrthogonalObservation
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PaBJointVisibility
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.PhysicalPortDefect

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.ThreePortFibre

open BurnolPhysicalState OriginalKSourceResolventReconstruction
open SourceGeneratedScalarDifferentialResidual SourceGeneratedObservationAction
open scoped InnerProductSpace

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private betaRead anchor_beta_ne from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn
open private read_scalar_dual from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.FullCayleyCoupling
open private orthogonal_duals amount_dual_ne from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.UnitPortEnergy
open private pair_fields from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PaBJointVisibility

namespace Orth
export SaturationMonoid.OrthogonalSourceObservation
  (observe representative read_representative coimageEquiv coimage_source fibre_split)
end Orth

namespace Pa
export OriginalKCombCofinalPaAction (E Q)
end Pa

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate c
local notation "K" => burnolCompletedMellinRieszVector c
local notation "FK" => fourierL2 (K : BurnolL2)
local notation "α" => FullCayleyCoupling.sourceAmount observation half
local notation "β" => betaRead observation half
local notation "A" => ContinuousLinearMap.adjoint α 1
local notation "B" => ContinuousLinearMap.adjoint β 1
local notation "ClosedPa" => burnolCompactCoPoissonClosedRange.toSubmodule

private def fk : BurnolPaOrthogonalCarrier :=
  burnolCompactCoPoissonActionSquare.orthogonalAction
    ⟨K, riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero⟩

private theorem ambient_fk :
    burnolEvenAmbientProjection FK = (fk observation half : BurnolPaAmbientCarrier) := by
  let z := (fk observation half : BurnolPaAmbientCarrier)
  change (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto
    (z : BurnolL2) = z
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self z

private theorem alpha_FK_zero : inner ℂ A FK = 0 := by
  rw [read_scalar_dual]
  change burnolPaResolventSourceCoefficient c (Pa.E FK) = 0
  have hidden : (fk observation half : BurnolPaAmbientCarrier) ∈ ClosedPaᗮ := (fk observation half).property
  have projection : (ClosedPa).starProjection (fk observation half : BurnolPaAmbientCarrier) = 0 := by
    rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hidden]
    rfl
  change burnolPaResolventSourceCoefficient c ((ClosedPa).starProjection (burnolEvenAmbientProjection FK)) = 0
  rw [ambient_fk observation half, projection, map_zero]

include nontrivial in
private theorem beta_FK_zero : inner ℂ B FK = 0 := by
  rw [read_scalar_dual]
  have fixed : Pa.Q FK = (fk observation half : BurnolPaAmbientCarrier) := by
    let z := fk observation half
    change ClosedPaᗮ.starProjection (burnolEvenAmbientProjection FK) = (z : BurnolPaAmbientCarrier)
    rw [ambient_fk observation half, Submodule.starProjection_apply]
    exact congrArg Subtype.val (ClosedPaᗮ.orthogonalProjectionOnto_mem_subspace_eq_self z)
  change inner ℂ (fourierL2 (burnolUnitTailResponse barC 4)) (Pa.Q FK : BurnolL2) = 0
  rw [fixed]
  change inner ℂ (fourierL2 (burnolUnitTailResponse barC 4)) FK = 0
  have price := OriginalKCrossParameterRAdjointSource.CrossUnitKSource.conjugate_unit_FK_reentry_price_zero
    observation nontrivial half
  rw [generatedK_eq_original] at price
  exact price

include nontrivial in
private theorem beta_dual_ne : B ≠ 0 := by
  intro zero
  have silent (value : BurnolL2) : β value = 0 := by
    rw [← read_scalar_dual β value, zero, inner_zero_left]
  have live := anchor_beta_ne observation nontrivial half
  exact live (silent _)

include nontrivial in
private theorem FK_ne : FK ≠ 0 := by
  intro zero
  have live := FixedFourierKFeedback.original_opening_price_ne_zero observation nontrivial half
  rw [zero, inner_zero_left] at live
  exact live rfl

/-- The actual Division injection, Pa return and fixed Fourier–K outside covectors. -/
def columns : Fin 3 → BurnolL2 := ![A, B, FK]

include nontrivial in
theorem columns_orthogonal :
    Pairwise (fun i j : Fin 3 => inner ℂ (columns observation half i) (columns observation half j) = 0) := by
  have ab := orthogonal_duals observation half
  have ac := alpha_FK_zero observation half
  have bc := beta_FK_zero observation nontrivial half
  have ba := inner_eq_zero_symm.mp ab
  have ca := inner_eq_zero_symm.mp ac
  have cb := inner_eq_zero_symm.mp bc
  intro i j different
  fin_cases i <;> fin_cases j <;> simp_all [columns]

include nontrivial in
theorem columns_live (i : Fin 3) : columns observation half i ≠ 0 := by
  fin_cases i
  · exact amount_dual_ne observation nontrivial half
  · exact beta_dual_ne observation nontrivial half
  · exact FK_ne observation nontrivial half

local notation "ports" => Orth.observe (columns observation half)
local notation "represent" => Orth.representative (columns observation half)

theorem physical_fibre_zero (value : BurnolL2) (outside : burnolEvenAmbientProjection value = 0) :
    ports value = 0 := by
  have paZero : Pa.E value = 0 := by
    simp only [Pa.E, ContinuousLinearMap.comp_apply, outside, map_zero]
  have qZero : Pa.Q value = 0 := by
    simp only [Pa.Q, ContinuousLinearMap.comp_apply, outside, map_zero]
  funext i
  fin_cases i
  · change inner ℂ A value = 0
    rw [read_scalar_dual]
    change burnolPaResolventSourceCoefficient c (Pa.E value) = 0
    rw [paZero, map_zero]
  · change inner ℂ B value = 0
    rw [read_scalar_dual]
    change inner ℂ (fourierL2 (burnolUnitTailResponse barC 4)) (Pa.Q value : BurnolL2) = 0
    rw [qZero, Submodule.coe_zero, inner_zero_right]
  · change inner ℂ FK value = 0
    have tested := OriginalKPaCountingSourceAction.actual_original_Q_orthogonal_reader (fk observation half) value
    rw [qZero, inner_zero_right] at tested
    exact tested.symm

include nontrivial in
/-- The actual source retains a genuine next-observation difference on the current three-port fibre. -/
theorem original_port_defect :
    actionDefect (OriginalKCombPhysicalAction.R observation nontrivial half).toLinearMap (ports).toLinearMap ≠ 0 := by
  have direct : OriginalKCombPhysicalAction.R observation nontrivial half = burnolDirectRightResolventCLM c :=
    ContinuousLinearMap.ext (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half)
  rw [direct]
  exact OriginalRSourceJointContact.OutsideHistory.PhysicalPortDefect.nonzero c (ports).toLinearMap FK
    (FK_ne observation nontrivial half) (physical_fibre_zero observation half) (LinearMap.proj (2 : Fin 3))
    (fun _ => rfl)

/-- The finite read is exactly the canonical coimage of the three original covectors. -/
def portEquiv :=
  Orth.coimageEquiv (columns observation half)
    (columns_orthogonal observation nontrivial half) (columns_live observation nontrivial half)

variable (depth : Nat)

local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "R" => OriginalKCombPhysicalAction.R observation nontrivial half
local notation "αfee" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth
local notation "βfee" => ReentryDifferenceClock.fee observation nontrivial half depth
local notation "γfee" => FixedFourierKFeedback.price observation nontrivial half depth

private theorem actual_read (ordinal : Nat) :
    ports (raw ordinal) = ![αfee ordinal, βfee ordinal, γfee ordinal] := by
  funext i
  fin_cases i
  · change inner ℂ A (raw ordinal) = αfee ordinal
    exact read_scalar_dual α (raw ordinal)
  · change inner ℂ B (raw ordinal) = βfee ordinal
    exact (read_scalar_dual β (raw ordinal)).trans
      (ReentryDifferenceClock.literal_fee observation nontrivial half depth ordinal).symm
  · change inner ℂ FK (raw ordinal) = γfee ordinal
    exact FixedFourierKFeedback.actual_whole_price observation nontrivial half depth ordinal

local notation "index" => PaBJointVisibility.selected observation nontrivial half depth
local notation "pairAt" => PaBJointVisibility.actualPair observation nontrivial half depth
local notation "whole" => PacketFit.packetWhole

private theorem actual_packet_input (cutoff : Nat) :
    whole (pairAt cutoff).1 = raw (index cutoff) := by
  have fields := pair_fields observation nontrivial half depth cutoff
  exact congrArg Prod.fst fields

private theorem actual_packet_next (cutoff : Nat) :
    whole (pairAt cutoff).2 = R (whole (pairAt cutoff).1) := by
  have old := actual_packet_input observation nontrivial half depth cutoff
  have fields := pair_fields observation nontrivial half depth cutoff
  have next : whole (pairAt cutoff).2 = raw (index cutoff+1) := congrArg Prod.snd fields
  exact next.trans ((OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth
    (index cutoff)).trans (congrArg (fun v : BurnolL2 => R v) old.symm))

private theorem joint_at (action : BurnolL2 →ₗ[ℂ] BurnolL2) (read : BurnolL2 →ₗ[ℂ] (Fin 3 → ℂ))
    (source target : BurnolL2) (actual : target = action source) :
    jointNext action read (canonicalResidual (jointObservation action read) source) =
      canonicalResidual read target :=
  (joint_next_source action read source).trans (congrArg (canonicalResidual read) actual.symm)

/-- The current and next read use the existing joint coimage at the literal original packet pair. -/
theorem selected_joint_next (cutoff : Nat) :
    type_of% (joint_at (R).toLinearMap (ports).toLinearMap (whole (pairAt cutoff).1) (whole (pairAt cutoff).2)
      (actual_packet_next observation nontrivial half depth cutoff)) :=
  joint_at (R).toLinearMap (ports).toLinearMap (whole (pairAt cutoff).1) (whole (pairAt cutoff).2)
    (actual_packet_next observation nontrivial half depth cutoff)

private def ActionAt (source target : BurnolL2) (fees : Fin 3 → ℂ) : Prop :=
  let visible := represent (ports source)
  let residual := source - visible
  ports source = fees ∧ ports residual = 0 ∧
    ‖source‖^2 = ‖visible‖^2 + ‖residual‖^2 ∧ target = R visible + R residual

private theorem action_at (source target : BurnolL2) (fees : Fin 3 → ℂ)
    (observed : ports source = fees) (actual : target = R source) :
    ActionAt observation nontrivial half source target fees := by
  let visible := represent (ports source)
  let residual := source - visible
  have fibre := Orth.fibre_split (columns observation half)
    (columns_orthogonal observation nontrivial half) (columns_live observation nontrivial half) source
  have wholeInput : source = visible + residual := by dsimp [residual]; abel
  have acted : target = R visible + R residual :=
    actual.trans ((congrArg (fun v : BurnolL2 => R v) wholeInput).trans (map_add R visible residual))
  exact ⟨observed, fibre.1, fibre.2, acted⟩

/-- The original write reads its three fees, keeps the complete invisible residual, and
    acts on both summands of the same literal input in its next packet. -/
theorem selected_action (cutoff : Nat) :
    ActionAt observation nontrivial half (whole (pairAt cutoff).1) (whole (pairAt cutoff).2)
      ![αfee (index cutoff), βfee (index cutoff), γfee (index cutoff)] := by
  have old := actual_packet_input observation nontrivial half depth cutoff
  have observed := (congrArg (fun v : BurnolL2 => ports v) old).trans
    (actual_read observation nontrivial half depth (index cutoff))
  exact action_at observation nontrivial half _ _ _ observed
    (actual_packet_next observation nontrivial half depth cutoff)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.ThreePortFibre
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
