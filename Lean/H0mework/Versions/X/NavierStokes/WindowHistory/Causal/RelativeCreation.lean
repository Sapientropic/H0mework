import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.CreationEnergy

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalRelativeCreation
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H)
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryMeanProjection (embed)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryMeanBlocks (bath)
open NativeWindowHistoryCausalPassivity (creationResponse creationInput creationInput_continuous)
open NativeWindowHistorySchurWeakPairing (potential)
open NativeWindowTraceWholeHistory (gradient)
open NativeWindowHistoryCausalDissipation (gradient_continuous)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM)
open NativeFiniteActionResolvent (physicalSpace pairing)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

theorem source_potential (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧ ∀ M t,t∈Icc 0 horizon → ∀ v : physicalSpace (modes M),
      potential seed M t v≤epsilon*gradient M (embed (includeCLM (modes M) (modes_closed M) v))+
        C*‖includeCLM (modes M) (modes_closed M) v‖^2 := by
  refine ⟨NativeWindowHistoryCreationSource.budget seed horizon epsilon,
    NativeWindowHistoryCreationSource.budget_nonnegative seed horizon epsilon positive,fun M t inside v => ?_⟩
  have source:=NativeWindowHistorySchurWeakPairing.source_potential_bound seed horizon epsilon positive M t inside v
  have pair := (NativePhysicalPairing.include_inner (modes M) (modes_zero M) (modes_closed M) v
    (includeCLM (modes M) (modes_closed M) v)).trans
      (congrArg (pairing (modes M) v) (NativePhysicalPairing.restrict_include (modes M) (modes_zero M) (modes_closed M) v))
  have mass := (real_inner_self_eq_norm_sq (includeCLM (modes M) (modes_closed M) v)).symm.trans pair
  rwa [← NativeWindowHistoryMeanGradient.gradient_embed M v,← mass] at source

private theorem rescale (n w p g : ℝ) (positive : 0<n)
    (paid : 2*n⁻¹*w≤(n⁻¹)^2*p+g) : 2*w≤n⁻¹*p+n*g := by
  have multiplied:=mul_le_mul_of_nonneg_left paid positive.le
  have first : n*(2*n⁻¹*w)=2*w := by field_simp
  have last : n*((n⁻¹)^2*p+g)=n⁻¹*p+n*g := by field_simp
  rwa [first,last] at multiplied

set_option backward.isDefEq.respectTransparency false in
theorem source_energy (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧ ∀ M (v : ℝ → physicalSpace (modes M)) (vc : Continuous v)
      (a : ℝ) (start : a∈Icc 0 horizon) (b : ℝ) (_inside : b∈Icc a horizon),
      let w:=fun t => includeCLM (modes M) (modes_closed M) (v t)
      let wc:Continuous w:=(includeCLM (modes M) (modes_closed M)).continuous.comp vc
      let y:=creationResponse seed M w wc a horizon start.2
      ‖y b‖^2+nu.coeff*(∫t in a..b,gradient M (y t))≤
        epsilon*(∫t in a..b,gradient M (embed (w t)))+C*(∫t in a..b,‖w t‖^2) := by
  obtain ⟨C,C0,paid⟩:=source_potential seed horizon (nu.coeff*epsilon) (mul_pos nu.coeff_pos positive)
  refine ⟨nu.coeff⁻¹*C,mul_nonneg (inv_nonneg.mpr nu.coeff_pos.le) C0,?_⟩
  intro M v vc a start b inside
  dsimp only
  let w:=fun t => includeCLM (modes M) (modes_closed M) (v t)
  have wc:Continuous w:=(includeCLM (modes M) (modes_closed M)).continuous.comp vc
  let y:=creationResponse seed M w wc a horizon start.2
  let f:=creationInput seed M w
  have fc:=creationInput_continuous seed M w wc
  have derivative:=NativeWindowHistoryCausalPassivity.bathResponse_derivative seed M f fc a horizon start.2
  have energy:=NativeWindowHistoryCausalDissipation.energy_write seed M y f a horizon start.2
    fc.continuousOn derivative (NativeWindowHistoryCausalCreationEnergy.centered seed M w wc a horizon start.2) b inside
  have initial:y a=0:=NativeWindowHistoryCausalPassivity.bathResponse_initial seed M f fc a horizon start.2
  rw [initial,norm_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add] at energy
  have yc:ContinuousOn y (Icc a b):=fun t ht =>
    ((derivative t ⟨ht.1,ht.2.trans inside.2⟩).mono (Icc_subset_Icc le_rfl inside.2)).continuousWithinAt
  have work:IntervalIntegrable (fun t => inner ℝ (f t) (y t)) volume a b:=
    (fc.continuousOn.inner (𝕜 := ℝ) yc).intervalIntegrable_of_Icc (μ := volume) inside.1
  have mass:IntervalIntegrable (fun t => ‖w t‖^2) volume a b:=(wc.norm.pow 2).intervalIntegrable a b
  have inputGrad:IntervalIntegrable (fun t => gradient M (embed (w t))) volume a b:=
    ((gradient_continuous nu M).comp (embed.continuous.comp wc)).intervalIntegrable a b
  have gradients:=((gradient_continuous nu M).comp_continuousOn yc).intervalIntegrable_of_Icc (μ := volume) inside.1
  have point (t : ℝ) (ht : t∈Icc a b) :
      2*inner ℝ (f t) (y t)≤epsilon*gradient M (embed (w t))+(nu.coeff⁻¹*C)*‖w t‖^2+nu.coeff*gradient M (y t) := by
    have weak:=NativeWindowHistorySchurWeakPairing.creation_young seed M t (v t) (y t) nu.coeff⁻¹
    have bound:=rescale nu.coeff _ _ _ nu.coeff_pos weak
    have source:=mul_le_mul_of_nonneg_left (paid M t ⟨start.1.trans ht.1,ht.2.trans inside.2⟩ (v t))
      (inv_nonneg.mpr nu.coeff_pos.le)
    have paidSource : nu.coeff⁻¹*potential seed M t (v t)≤
        epsilon*gradient M (embed (w t))+(nu.coeff⁻¹*C)*‖w t‖^2 := by
      simpa only [mul_add,← mul_assoc,inv_mul_cancel₀ nu.coeff_pos.ne',one_mul] using source
    exact bound.trans (add_le_add paidSource (le_refl _))
  have integral:=intervalIntegral.integral_mono_on inside.1 (work.const_mul 2)
    (((inputGrad.const_mul epsilon).add (mass.const_mul (nu.coeff⁻¹*C))).add (gradients.const_mul nu.coeff)) point
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((inputGrad.const_mul epsilon).add (mass.const_mul (nu.coeff⁻¹*C))) (gradients.const_mul nu.coeff),
    intervalIntegral.integral_add (inputGrad.const_mul epsilon) (mass.const_mul (nu.coeff⁻¹*C)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at integral
  change ‖y b‖^2+nu.coeff*(∫t in a..b,gradient M (y t))≤
    epsilon*(∫t in a..b,gradient M (embed (w t)))+(nu.coeff⁻¹*C)*(∫t in a..b,‖w t‖^2)
  simp only [Function.comp_def] at integral
  linarith only [energy,integral]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalRelativeCreation
