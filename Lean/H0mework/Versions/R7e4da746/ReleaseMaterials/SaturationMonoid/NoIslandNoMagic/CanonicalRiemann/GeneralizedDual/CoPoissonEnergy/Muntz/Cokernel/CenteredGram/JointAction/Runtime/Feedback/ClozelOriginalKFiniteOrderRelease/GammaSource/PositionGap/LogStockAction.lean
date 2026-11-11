import Mathlib.Analysis.Normed.Operator.Banach
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LogStock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierInventoryAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.LogStock

open BurnolPhysicalState Filter
open OriginalGamma.Source.ConductorDual OriginalGamma.Source.WindowLog
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.RelativeConductorGapReadback
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open BurnolPhysicalState.OriginalRSourceJointContact.LogAction
open scoped Topology

open private log_pair_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ConductorDualSource
open private inverse_log_from_complete_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
open private next_field from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierInventoryAction

local notation "F" => fourierL2
local notation "R" => burnolDirectRightResolventCLM
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "q" => burnolUnscaledCommonGapRadius

def gamma : Whole →L[ℂ] BurnolL2 :=
  positionLog + fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp inverseLog

private theorem gamma_graph (x : Whole) : GammaPair (field x) (gamma x) :=
  gamma_pair_of_log_pairs _ _ _ (log_pairs x).1 (log_pairs x).2

/-- A paid graph action inherits continuity from its field write and the closed graph norm. -/
private def boundedLift (action : BurnolL2 →L[ℂ] BurnolL2) (perform : Whole → Whole)
    (writes : ∀ x, field (perform x) = action (field x)) : Whole →L[ℂ] Whole := by
  let linear : Whole →ₗ[ℂ] Whole :=
    { toFun := perform
      map_add' := fun x y => field_injective (by
        change field (perform (x+y)) = field (perform x + perform y)
        simp only [writes, map_add])
      map_smul' := fun a x => field_injective (by
        change field (perform (a • x)) = field (a • perform x)
        simp only [writes, map_smul]) }
  refine ⟨linear, linear.continuous_of_seq_closed_graph ?_⟩
  intro u x y input output
  apply field_injective
  change field y = field (perform x)
  have observed := (field.continuous.tendsto y).comp output
  change Tendsto (fun n => field (perform (u n))) atTop (𝓝 (field y)) at observed
  simp only [writes] at observed
  have written := ((action.continuous.comp field.continuous).tendsto x).comp input
  exact (tendsto_nhds_unique observed written).trans (writes x).symm

private def projectedStock (x : Whole) : Whole := by
  have frequency := log_pair_reflect _ _ (log_pairs x).2
  rw [fourierL2_symm_eq_reflect_fourierL2, reflectL2_reflectL2] at frequency
  have projected := actual_physical_projection_log_pairs _ _ _ (log_pairs x).1 frequency
  have inverse := log_pair_reflect _ _ projected.2
  rw [← fourierL2_symm_eq_reflect_fourierL2] at inverse
  have inside : P (field x) ∈ evenBurnolClosedFace q :=
    Submodule.starProjection_apply_mem (evenBurnolClosedFace q).toSubmodule (field x)
  exact ofLogs ⟨P (field x), inside.1.1, inside.2⟩ _ _ projected.1 inverse

/-- The existing physical projection acts continuously on the stronger graph. -/
def physical : Whole →L[ℂ] Whole :=
  boundedLift P projectedStock (fun _ => rfl)

theorem physical_field (x : Whole) : field (physical x) = P (field x) := rfl

def split : Whole →L[ℂ] Whole × Whole :=
  physical.prod (ContinuousLinearMap.id ℂ Whole - physical)

private def advancedStock (c : BurnolCompletedMellinCoordinate) (x : Whole) : Whole := by
  have read : ((basis c).repr.symm (coordinates c x) : BurnolL2) = field x :=
    congrArg Subtype.val ((basis c).repr.symm_apply_apply (⟨field x, field_mem x⟩ : PositionField))
  have actual := next_field c (coordinates c x)
  rw [read] at actual
  have inside : R c (field x) ∈ PositionField := by
    rw [← actual]
    exact ((basis c).repr.symm (nextCoefficients c (coordinates c x))).property
  have parameter : 1/4 < (c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have newPosition := actual_direct_R_log (c.value/2) parameter _ _ (log_pairs x).1
  have newGamma := actual_Gamma_R c _ _ (gamma_graph x)
  exact ofLogs ⟨R c (field x), inside⟩ _ _ newPosition
    (inverse_log_from_complete_source _ _ _ newGamma newPosition)

/-- The native R action advances both logarithmic fields with its paid commutator. -/
def advance (c : BurnolCompletedMellinCoordinate) : Whole →L[ℂ] Whole :=
  boundedLift (R c) (advancedStock c) (fun _ => rfl)

theorem advance_field (c : BurnolCompletedMellinCoordinate) (x : Whole) :
    field (advance c x) = R c (field x) := rfl

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.LogStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
