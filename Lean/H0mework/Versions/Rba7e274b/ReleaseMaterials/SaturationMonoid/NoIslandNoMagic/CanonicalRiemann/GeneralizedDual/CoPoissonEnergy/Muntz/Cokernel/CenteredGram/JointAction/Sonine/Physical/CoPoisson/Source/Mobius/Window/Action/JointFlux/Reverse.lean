import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Mean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalJointFluxSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators

theorem fullS_source_even (value : BurnolL2) (even : reflectL2 value=value) :
    reflectL2 (Paid.fullS value)=Paid.fullS value := by
  unfold Paid.fullS
  simp only [sum_apply,smul_apply,map_sum,map_smul,Paid.fullPullback,
    LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry,
    reflectL2_burnolMultiplicativeDilation,even]

theorem actual_reverse_flux_source (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) :
    Paid.reverseFlux (coordinate.value/2) value=Paid.reverseRankSource coordinate value := by
  have right : 1/4<(coordinate.value/2).re := by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have source := FiniteMobiusResolventFlux.actual_M_Rplus_action (coordinate.value/2) right value
  rw [FiniteMobiusResolventFlux.lower_full_source,FiniteMobiusResolventFlux.lower_full_source,
    Paid.fullS_Rplus _ right,Paid.Rplus_sub _ right,Paid.Rplus_smul _ _ right] at source
  unfold Paid.reverseRankSource Paid.exteriorMoment
  rw [← Paid.cutoff_Rplus_rank coordinate (Paid.fullS value) (fullS_source_even value even)]
  calc
    _=(Paid.cutoff 4 (Paid.Rplus (coordinate.value/2) (Paid.fullS value))-
      (Paid.sigma*Paid.actualMean (Paid.Rplus (coordinate.value/2) value)) • Paid.box 4)-
      (Paid.Rplus (coordinate.value/2) (Paid.cutoff 4 (Paid.fullS value))-
        (Paid.sigma*Paid.actualMean value) • Paid.Rplus (coordinate.value/2) (Paid.box 4)) := by
      rw [source]
      module
    _=_ := by module
end OriginalJointFluxSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
