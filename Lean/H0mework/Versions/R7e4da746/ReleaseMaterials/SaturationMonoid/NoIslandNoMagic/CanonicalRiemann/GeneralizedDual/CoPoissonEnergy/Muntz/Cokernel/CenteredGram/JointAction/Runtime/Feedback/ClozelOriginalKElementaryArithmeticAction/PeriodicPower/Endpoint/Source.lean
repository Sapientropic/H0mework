import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Alias.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.ResponseForcing.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszSource.Translator
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open scoped Topology ENNReal InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "F" => fourierL2
local notation "Rq" => burnolQuarterRestriction
local notation "P0" => Constructor.zeroMean
local notation "BI" => burnolMeanZeroBlockInverse
local notation "C" => ConstantDual.seed
local instance finiteQuarter : IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem alias_quarter_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (aliasRaw c) (symmetricInterval q) :=
  (actual_alias_raw_continuous c).mono (by intro x h;constructor <;> linarith [h.1,h.2])

private theorem alias_quarter_memLp (c : BurnolCompletedMellinCoordinate) :
    MemLp (aliasRaw c) 2 μq := by
  have regular:=alias_quarter_continuous c
  obtain ⟨bound,bounded⟩:=isCompact_Icc.exists_bound_of_continuousOn regular
  apply MemLp.of_bound (regular.aestronglyMeasurable (measurableSet_symmetricInterval q)) bound
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  exact bounded x inside

def aliasQuarter (c : BurnolCompletedMellinCoordinate) : Hq :=
  (alias_quarter_memLp c).toLp (aliasRaw c)

theorem actual_alias_quarter_raw (c : BurnolCompletedMellinCoordinate) :
    (aliasQuarter c:ℝ→ℂ)=ᵐ[μq]aliasRaw c := (alias_quarter_memLp c).coeFn_toLp

def periodicQuarter (c : BurnolCompletedMellinCoordinate) : Hq :=
  Rq (F (resolvedSource c))+aliasQuarter c-resolvedRaw c 0 • intervalConstant q

theorem actual_periodic_quarter_raw (c : BurnolCompletedMellinCoordinate) :
    (periodicQuarter c:ℝ→ℂ)=ᵐ[μq]periodicRaw c := by
  filter_upwards [Lp.coeFn_sub (Rq (F (resolvedSource c))+aliasQuarter c) (resolvedRaw c 0 • intervalConstant q),
    Lp.coeFn_add (Rq (F (resolvedSource c))) (aliasQuarter c),
    Lp.coeFn_smul (resolvedRaw c 0) (intervalConstant q),intervalConstant_coeFn q,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (F (resolvedSource c)),
    ae_restrict_of_ae (actual_resolved_fourier_raw c),actual_alias_quarter_raw c]
    with x difference addition scalar constant restricted source aliasRead
  change (Rq (F (resolvedSource c))+aliasQuarter c-resolvedRaw c 0 • intervalConstant q:Hq) x=_
  change Rq (F (resolvedSource c)) x=F (resolvedSource c) x at restricted
  rw [difference,Pi.sub_apply,addition,Pi.add_apply,scalar,Pi.smul_apply,smul_eq_mul,
    constant,mul_one,restricted,source,aliasRead]
  rfl

/-- The whole periodic field and every alias enter the original quarter forcing before the inverse. -/
def completeQuarterForcing (c : BurnolCompletedMellinCoordinate) : Hq :=
  periodicQuarter c-aliasQuarter c+jumpCoefficient c • Rq (F C)

theorem actual_complete_forcing (c : BurnolCompletedMellinCoordinate) :
    completeQuarterForcing c=Rq (F (elementarySource c))-resolvedRaw c 0 • intervalConstant q := by
  unfold completeQuarterForcing periodicQuarter resolvedSource
  rw [map_sub,map_smul,map_sub,map_smul]
  module

theorem actual_original_B_periodic_source (c : BurnolCompletedMellinCoordinate) :
    burnolRieszSingleFourierSource c=BI (P0 (completeQuarterForcing c)) := by
  rw [actual_complete_forcing,map_sub,map_smul,Constructor.zeroMean_constant,smul_zero,sub_zero]
  rfl

def positionEndpoint (c : BurnolCompletedMellinCoordinate) : ℂ :=
  jumpCoefficient c+burnolRieszReturnRaw c q

def fourierEndpoint (c : BurnolCompletedMellinCoordinate) : ℂ :=
  resolvedRaw c 0+jumpCoefficient c*burnolRadiusTruncatedFourierRaw q (intervalConstant q) q-
    aliasRaw c q-ForcingMeanZero.mean c+Constructor.secondReturnRaw c q

theorem actual_original_A (c : BurnolCompletedMellinCoordinate) : Kernel.A c=positionEndpoint c := by
  have gap:=GapEuler.gapMean_primitive q (by norm_num) c
  unfold Kernel.A positionEndpoint jumpCoefficient
  linear_combination -gap

/-- The literal periodic point is separated from all original mean and inverse-return terms. -/
theorem actual_original_beta_field (c : BurnolCompletedMellinCoordinate) :
    Kernel.beta c=periodicRaw c q+fourierEndpoint c := by
  rw [Kernel.beta,burnolRieszSingleFourierSourceRaw,ForcingMeanZero.forcingRaw_eq]
  change ForcingWhole.raw c q-ForcingMeanZero.mean c+Constructor.secondReturnRaw c q=_
  unfold periodicRaw fourierEndpoint resolvedFourierRaw
  ring

theorem actual_original_forcing_point (c : BurnolCompletedMellinCoordinate) :
    ForcingWhole.raw c q=periodicRaw c q+resolvedRaw c 0+
      jumpCoefficient c*burnolRadiusTruncatedFourierRaw q (intervalConstant q) q-aliasRaw c q := by
  unfold periodicRaw resolvedFourierRaw
  ring

/-- This is the complete actual endpoint bill before any zero observation is read. -/
theorem actual_original_endpoint_field_bill (c : BurnolCompletedMellinCoordinate) :
    star (Kernel.A c)*Kernel.A c-star (Kernel.beta c)*Kernel.beta c=
      star (positionEndpoint c)*positionEndpoint c-
        star (periodicRaw c q+fourierEndpoint c)*(periodicRaw c q+fourierEndpoint c) := by
  rw [actual_original_A,actual_original_beta_field]

end OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
