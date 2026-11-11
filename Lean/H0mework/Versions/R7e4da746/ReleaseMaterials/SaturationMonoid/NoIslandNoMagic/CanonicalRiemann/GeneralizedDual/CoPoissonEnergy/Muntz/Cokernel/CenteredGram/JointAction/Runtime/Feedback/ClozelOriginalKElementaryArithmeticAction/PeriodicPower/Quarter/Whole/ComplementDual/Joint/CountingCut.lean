import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusCross

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusCross
open scoped Topology
local notation "A"=>sourceAnnulusCut
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem dual_dilation (N:ℕ) (time:ℝ) (value:BurnolL2):
    DualSource.source N (burnolMultiplicativeDilation time value)=
      burnolMultiplicativeDilation time (DualSource.source N value):=by
  have channel (radius:ℝ):
      ContinuousChannels.channel 1 radius (burnolMultiplicativeDilation time value)=
        burnolMultiplicativeDilation time (ContinuousChannels.channel 1 radius value):=by
    simp only [ContinuousChannels.channel,map_smul,burnolMultiplicativeDilation_add]
    rw [add_comm]
  unfold DualSource.source
  simp_rw [channel]
  rw [map_sub,map_sum]
  congr 1
  exact (burnolMultiplicativeDilation time).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N value)

private theorem rightQuarter (d:BurnolCompletedMellinCoordinate):1/4<(d.value/2).re:=by
  rw [Complex.div_re]
  norm_num
  linarith [d.rightHalf]

private theorem volterra_Rplus (d:BurnolCompletedMellinCoordinate) (value:BurnolL2):
    sourceVolterraResolvent d value=FiniteMobiusResolventFlux.Rplus (d.value/2) value:=
  (FiniteMobiusResolventFlux.Rplus_tate _ (rightQuarter d) _).symm

/-- The original reverse programme and the actual outgoing R commute before any source cut. -/
theorem actual_reverse_volterra (N:ℕ) (d:BurnolCompletedMellinCoordinate) (value:BurnolL2):
    DualSource.source N (sourceVolterraResolvent d value)=
      sourceVolterraResolvent d (DualSource.source N value):=by
  have move (time:ℝ):
      (CountingDual.sourceCLM N).adjoint (burnolMultiplicativeDilation time value)=
        burnolMultiplicativeDilation time ((CountingDual.sourceCLM N).adjoint value):=by
    simpa only [CountingDual.dual_eq_adjoint] using dual_dilation N time value
  simp only [volterra_Rplus,CountingDual.dual_eq_adjoint]
  unfold FiniteMobiusResolventFlux.Rplus
  rw [map_neg,←(CountingDual.sourceCLM N).adjoint.integral_comp_comm
    (FiniteMobiusResolventFlux.Rplus_integrable _ (rightQuarter d) value)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro time _
  simp only [FiniteMobiusResolventFlux.RplusIntegrand,map_smul,move]

/-- The two finite cutcrosses are paid on the same actual source and the same integer/continuous clock. -/
theorem actual_joint_cut_ward (N:ℕ) (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    (A (DualSource.source N (sourceVolterraResolvent (barC c) (tateSource c j)))-
      DualSource.source N (A (sourceVolterraResolvent (barC c) (tateSource c j))))-
      sourceVolterraResolvent (barC c)
        (A (DualSource.source N (tateSource c j))-DualSource.source N (A (tateSource c j)))=
    (A (sourceVolterraResolvent (barC c) (DualSource.source N (tateSource c j)))-
      sourceVolterraResolvent (barC c) (A (DualSource.source N (tateSource c j))))-
      DualSource.source N (annulusCross c j):=by
  have full:=actual_reverse_volterra N (barC c) (tateSource c j)
  have cut:=actual_reverse_volterra N (barC c) (A (tateSource c j))
  simp only [CountingDual.dual_eq_adjoint] at full cut ⊢
  rw [annulusCross]
  simp only [map_sub]
  rw [full,cut]
  module

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
