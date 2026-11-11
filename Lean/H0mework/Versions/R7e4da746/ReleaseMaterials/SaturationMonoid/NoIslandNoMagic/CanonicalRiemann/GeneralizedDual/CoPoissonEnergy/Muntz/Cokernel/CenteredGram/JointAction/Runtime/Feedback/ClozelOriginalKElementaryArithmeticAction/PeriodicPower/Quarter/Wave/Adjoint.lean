import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Adjoint
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceResolventReconstruction OriginalKCrossParameterRAdjointSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "F"=>fourierL2
local notation "K"=>burnolCompletedMellinRieszVector
local notation "E"=>burnolQuarterZeroExtension
local notation "Rq"=>burnolQuarterRestriction
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem original_gap_restriction (c:BurnolCompletedMellinCoordinate):
    Rq (K c:BurnolL2)=positionMean c • intervalConstant q ∧
    Rq (F (K c:BurnolL2))=fourierMean c • intervalConstant q := by
  constructor
  · apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (K c:BurnolL2),
      ae_restrict_of_ae (burnolRieszState_ae_raw c),ae_restrict_mem (measurableSet_symmetricInterval q),
      Lp.coeFn_smul (positionMean c) (intervalConstant q),intervalConstant_coeFn q]
      with x restricted source inside scalar constant
    change Rq (K c:BurnolL2) x=_ at restricted
    rw [restricted,source,position_raw,if_pos inside,add_zero,scalar,Pi.smul_apply,
      smul_eq_mul,constant,mul_one]
  · apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (F (K c:BurnolL2)),
      ae_restrict_of_ae (burnolRieszFourier_ae_raw c),ae_restrict_mem (measurableSet_symmetricInterval q),
      Lp.coeFn_smul (fourierMean c) (intervalConstant q),intervalConstant_coeFn q]
      with x restricted source inside scalar constant
    change Rq (F (K c:BurnolL2)) x=_ at restricted
    rw [restricted,source,fourier_raw,if_pos inside,add_zero,scalar,Pi.smul_apply,
      smul_eq_mul,constant,mul_one]

/-- Both original K gaps read the actual compact wave, retaining its full mean. -/
theorem actual_quarter_wave_gap_prices (c:BurnolCompletedMellinCoordinate):
    inner ℂ (K c:BurnolL2) (quarterWave c)=
      star (positionMean c)*inner ℂ ConstantDual.seed (quarterWave c) ∧
    inner ℂ (F (K c:BurnolL2)) (quarterWave c)=
      star (fourierMean c)*inner ℂ ConstantDual.seed (quarterWave c) := by
  have cPair:inner ℂ (intervalConstant q) (periodicQuarter c)=
      inner ℂ ConstantDual.seed (quarterWave c):=by
    change inner ℂ (intervalConstant q) (periodicQuarter c)=
      inner ℂ (burnolQuarterRestriction.adjoint (intervalConstant q)) (E (periodicQuarter c))
    rw [ContinuousLinearMap.adjoint_inner_left,burnolQuarterRestriction_zeroExtension]
  constructor
  · have paired:inner ℂ (K c:BurnolL2) (quarterWave c)=inner ℂ (Rq (K c:BurnolL2)) (periodicQuarter c):=
      ContinuousLinearMap.adjoint_inner_right Rq _ _
    rw [paired,(original_gap_restriction c).1,inner_smul_left,cPair,starRingEnd_apply]
  · have paired:inner ℂ (F (K c:BurnolL2)) (quarterWave c)=inner ℂ (Rq (F (K c:BurnolL2))) (periodicQuarter c):=
      ContinuousLinearMap.adjoint_inner_right Rq _ _
    rw [paired,(original_gap_restriction c).2,inner_smul_left,cPair,starRingEnd_apply]

/-- The two independent native R adjoints actually consume the generated FH field. -/
theorem actual_original_two_adjoint_prices (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    (1/2:ℂ)*inner ℂ (sourceFKResponse c c) (companion c)=
      star (fourierMean c)*inner ℂ ConstantDual.seed (quarterWave c) ∧
    (1/2:ℂ)*inner ℂ (burnolDirectRightResolvent (c.value/2) (K c:BurnolL2)) (companion c)=
      star (positionMean c)*inner ℂ ConstantDual.seed (quarterWave c) := by
  have even:reflectL2 (K c:BurnolL2)=(K c:BurnolL2):=
    mem_evenL2ClosedFace_iff.mp (K c).property.2
  have first:=sourceResolvent_actual_adjoint_read (barC c) (F (K c:BurnolL2)) (resolventForcing c)
  have second:=sourceResolvent_actual_adjoint_read (barC c) (K c:BurnolL2) (resolventForcing c)
  simp only [sourceResolvent,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] at first second
  change inner ℂ (F (burnolDirectRightResolvent (c.value/2) (F (K c:BurnolL2)))) (resolventForcing c)=
    inner ℂ (F (F (K c:BurnolL2))) (burnolDirectRightResolvent (star c.value/2) (resolventForcing c)) at first
  change inner ℂ (F (burnolDirectRightResolvent (c.value/2) (K c:BurnolL2))) (resolventForcing c)=
    inner ℂ (F (K c:BurnolL2)) (burnolDirectRightResolvent (star c.value/2) (resolventForcing c)) at second
  rw [←actual_fourier_resolvent c zero,fourierL2_fourierL2] at first
  rw [even] at first
  rw [←actual_fourier_resolvent c zero] at second
  change inner ℂ (F (burnolDirectRightResolvent (c.value/2) (F (K c:BurnolL2))))
    ((1/2:ℂ) • F (companion c))=inner ℂ (K c:BurnolL2) (F (quarterWave c)) at first
  change inner ℂ (F (burnolDirectRightResolvent (c.value/2) (K c:BurnolL2)))
    ((1/2:ℂ) • F (companion c))=inner ℂ (F (K c:BurnolL2)) (F (quarterWave c)) at second
  rw [inner_smul_right,fourierL2.inner_map_map,source_FK_response] at first
  rw [inner_smul_right,fourierL2.inner_map_map,fourierL2.inner_map_map,(actual_quarter_wave_gap_prices c).1] at second
  have swap:inner ℂ (K c:BurnolL2) (F (quarterWave c))=inner ℂ (F (K c:BurnolL2)) (quarterWave c):=by
    have same:=fourierL2.inner_map_map (F (K c:BurnolL2)) (quarterWave c)
    rw [fourierL2_fourierL2,even] at same
    exact same
  rw [swap,(actual_quarter_wave_gap_prices c).2] at first
  exact ⟨first,second⟩

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Adjoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
