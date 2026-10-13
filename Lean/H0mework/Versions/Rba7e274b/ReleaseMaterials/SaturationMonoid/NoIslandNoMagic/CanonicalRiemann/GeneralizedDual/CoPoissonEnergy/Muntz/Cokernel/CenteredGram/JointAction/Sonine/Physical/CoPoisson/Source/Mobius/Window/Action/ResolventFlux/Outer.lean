import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Resolvent
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Mean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

def outerCut : BurnolL2 →L[ℂ] BurnolL2 := ContinuousLinearMap.id ℂ BurnolL2-cutoff 4

theorem cutoff_nested (small large : ℝ) (_nonnegative : 0≤small) (bounded : small≤large) (value : BurnolL2) :
    cutoff small (cutoff large value)=cutoff small value := by
  apply Lp.ext
  filter_upwards [cutoff_read small (cutoff large value),cutoff_read large value,cutoff_read small value] with x twice once direct
  rw [twice,direct]
  by_cases inside : x∈symmetricInterval small
  · rw [indicator_of_mem inside,indicator_of_mem inside,once,indicator_of_mem]
    exact ⟨by linarith [inside.1],by linarith [inside.2]⟩
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

theorem cutoff_box (small large : ℝ) (_nonnegative : 0≤small) (bounded : small≤large) :
    cutoff small (box large)=box small := by
  apply Lp.ext
  filter_upwards [cutoff_read small (box large),box_read large,box_read small] with x twice once direct
  rw [twice,direct]
  by_cases inside : x∈symmetricInterval small
  · rw [indicator_of_mem inside,indicator_of_mem inside,once,indicator_of_mem]
    exact ⟨by linarith [inside.1],by linarith [inside.2]⟩
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

-- The source quarter gap pays the mean response, leaving the actual outer-window flux.
theorem source_negative_flux (value : Ambient) (shift : ℝ) (nonpositive : shift≤0) :
    tailFlux shift (value : BurnolL2)+meanFlux shift (value : BurnolL2)=
      -(outerCut (burnolMultiplicativeDilation shift (M (value : BurnolL2)))) := by
  have movedRadius : (4:ℝ)≤4*Real.exp (-shift) := by
    have scale : 1≤Real.exp (-shift) := Real.one_le_exp_iff.mpr (by linarith)
    nlinarith
  rw [← finite_source_dilation]
  have sourceRead := lower_source_cutoff (value : BurnolL2)
  have movedRead := congrArg (burnolMultiplicativeDilation shift) sourceRead
  simp only [map_sum,map_smul,map_sub,action_cutoff 4 (by norm_num),action_box 4 (by norm_num),full_pullback_action] at movedRead
  have innerRead := congrArg (cutoff 4) movedRead
  simp only [map_sum,map_smul,map_sub,cutoff_nested 4 (4*Real.exp (-shift)) (by norm_num) movedRadius,
    cutoff_box 4 (4*Real.exp (-shift)) (by norm_num) movedRadius] at innerRead
  have same : M (burnolMultiplicativeDilation shift (value : BurnolL2))=
      cutoff 4 (burnolMultiplicativeDilation shift (M (value : BurnolL2))) := by
    rw [lower_source_cutoff,actual_mean_source_negative value shift nonpositive,innerRead]
    apply Finset.sum_congr rfl
    intro n _
    simp only [smul_smul,mul_comm]
  rw [same]
  unfold outerCut
  simp only [sub_apply,ContinuousLinearMap.id_apply]
  module

theorem source_forward_flux_outer (z : ℂ) (rightQuarter : 1/4<z.re) (value : Ambient) :
    actualFlux z (value : BurnolL2)=-outerCut (burnolDirectRightResolvent z (M (value : BurnolL2))) := by
  unfold actualFlux burnolDirectRightResolvent
  rw [map_neg,← outerCut.integral_comp_comm (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter (M (value : BurnolL2)))]
  have inside : (∫ tau : ℝ in Ioi 0,actualFluxIntegrand z (value : BurnolL2) tau)=
      -(∫ tau : ℝ in Ioi 0,outerCut (burnolDirectRightResolventIntegrand z (M (value : BurnolL2)) tau)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro tau positive
    unfold actualFluxIntegrand burnolDirectRightResolventIntegrand
    rw [source_negative_flux value (-tau/2) (by have a:0<tau:=positive;linarith),smul_neg]
    change -(positiveMellinQuarterRightResolventWeight z tau • outerCut (burnolMultiplicativeDilation (-tau/2) (M (value : BurnolL2))))=
      -(outerCut (positiveMellinQuarterRightResolventWeight z tau • burnolMultiplicativeDilation (-tau/2) (M (value : BurnolL2))))
    rw [map_smul]
  rw [inside]

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
