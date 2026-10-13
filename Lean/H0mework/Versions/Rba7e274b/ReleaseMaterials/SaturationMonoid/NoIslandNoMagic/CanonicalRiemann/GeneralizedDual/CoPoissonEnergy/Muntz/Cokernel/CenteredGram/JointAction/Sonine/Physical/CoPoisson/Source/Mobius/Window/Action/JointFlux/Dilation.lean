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

def sourceMeanDifference (shift : ℝ) (value : BurnolL2) : ℂ :=
  (2:ℂ)*((Real.exp (shift/2):ℂ)*(∫ x : ℝ in symmetricInterval (1/4:ℝ),value x)-
    (Real.exp (-shift/2):ℂ)*(∫ x : ℝ in symmetricInterval ((1/4:ℝ)*Real.exp shift),value x))

theorem source_mean_difference_actual (shift : ℝ) (value : BurnolL2) :
    sourceMeanDifference shift value=(Real.exp (shift/2):ℂ)*Paid.actualMean value-
      Paid.actualMean (burnolMultiplicativeDilation shift value) := by
  rw [actual_mean_source_integral,actual_mean_dilation_source]
  unfold sourceMeanDifference
  ring

 theorem actual_negative_M_source (value : BurnolL2) (shift : ℝ) (nonpositive : shift≤0) :
    Paid.M (burnolMultiplicativeDilation shift value)=
      Paid.cutoff 4 (burnolMultiplicativeDilation shift (Paid.M value))+
      (Paid.sigma*sourceMeanDifference shift value) • Paid.box 4 := by
  have movedRadius : (4:ℝ)≤4*Real.exp (-shift) := by
    have scale : 1≤Real.exp (-shift) := Real.one_le_exp_iff.mpr (by linarith)
    nlinarith
  have source := FiniteMobiusResolventFlux.lower_source_cutoff value
  have moved := congrArg (burnolMultiplicativeDilation shift) source
  simp only [map_sum,map_smul,map_sub,FiniteMobiusResolventFlux.action_cutoff 4 (by norm_num),
    FiniteMobiusResolventFlux.action_box 4 (by norm_num),FiniteMobiusResolventFlux.full_pullback_action] at moved
  have inner := congrArg (Paid.cutoff 4) moved
  simp only [map_sum,map_smul,map_sub,FiniteMobiusResolventFlux.cutoff_nested 4 (4*Real.exp (-shift)) (by norm_num) movedRadius,
    FiniteMobiusResolventFlux.cutoff_box 4 (4*Real.exp (-shift)) (by norm_num) movedRadius] at inner
  rw [inner,FiniteMobiusResolventFlux.lower_source_cutoff]
  unfold Paid.sigma
  rw [source_mean_difference_actual,Finset.sum_mul,Finset.sum_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [smul_sub,smul_smul]
  module

 theorem actual_negative_flux_source (value : BurnolL2) (shift : ℝ) (nonpositive : shift≤0) :
    Paid.tailFlux shift value+Paid.meanFlux shift value=
      -(Paid.outerCut (burnolMultiplicativeDilation shift (Paid.M value)))+
        (Paid.sigma*sourceMeanDifference shift value) • Paid.box 4 := by
  rw [← FiniteMobiusResolventFlux.finite_source_dilation,actual_negative_M_source value shift nonpositive]
  unfold Paid.outerCut
  simp only [sub_apply,ContinuousLinearMap.id_apply]
  module
end OriginalJointFluxSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
