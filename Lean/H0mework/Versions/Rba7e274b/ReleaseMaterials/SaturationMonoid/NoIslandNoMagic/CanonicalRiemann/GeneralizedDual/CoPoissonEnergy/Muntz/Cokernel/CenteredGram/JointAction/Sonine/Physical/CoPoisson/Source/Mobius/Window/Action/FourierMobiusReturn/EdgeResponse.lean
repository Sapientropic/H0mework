import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.Profile
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open OriginalRieszSource
attribute [local instance 1100] NormedSpace.complexToReal

theorem literal_edge_inventory (x : ℝ) : sourceEdge x=
    ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n*
      (((1/4:ℝ):ℂ)*(Constructor.phase (x/(n:ℕ)) (1/4:ℝ)+Constructor.phase (x/(n:ℕ)) (-(1/4:ℝ)))-
        burnolRadiusTruncatedFourierRaw (1/4:ℝ) (intervalConstant (1/4:ℝ)) (x/(n:ℕ))) := by
  unfold sourceEdge
  simp_rw [Edge.raw_apply]

 theorem edge_primitive_continuous (coordinate : BurnolCompletedMellinCoordinate) : Continuous (edgeResponsePrimitive coordinate) := by
  have exponent : -1<(star coordinate.value-1).re := by simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re];linarith [coordinate.rightHalf]
  exact intervalIntegral.continuous_primitive (fun a b=>(intervalIntegral.intervalIntegrable_cpow' exponent).mul_continuousOn finite_edge_continuous.continuousOn) 0

 theorem edge_primitive_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    HasDerivAt (edgeResponsePrimitive coordinate) ((x:ℂ)^(star coordinate.value-1)*sourceEdge x) x := by
  have exponent : -1<(star coordinate.value-1).re := by simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re];linarith [coordinate.rightHalf]
  have continuous : ContinuousAt (fun y : ℝ=>(y:ℂ)^(star coordinate.value-1)*sourceEdge y) x :=
    (Complex.continuousAt_ofReal_cpow_const x (star coordinate.value-1) (Or.inr positive.ne')).mul finite_edge_continuous.continuousAt
  have measured : StronglyMeasurable (fun y : ℝ=>(y:ℂ)^(star coordinate.value-1)*sourceEdge y) := by
    apply Measurable.stronglyMeasurable
    apply Measurable.mul
    · apply measurable_of_continuousOn_compl_singleton (0:ℝ)
      intro y nonzero
      exact (Complex.continuousAt_ofReal_cpow_const y (star coordinate.value-1) (Or.inr nonzero)).continuousWithinAt
    · exact finite_edge_continuous.measurable
  exact intervalIntegral.integral_hasDerivAt_right
    ((intervalIntegral.intervalIntegrable_cpow' exponent).mul_continuousOn finite_edge_continuous.continuousOn)
    measured.stronglyMeasurableAtFilter continuous

 theorem fixed_edge_inside_derivative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (positive : 0<x) (inside : x<4) :
    HasDerivAt (fixedEdgeReturnRaw coordinate)
      (-star coordinate.value/x*fixedEdgeReturnRaw coordinate x-(2:ℂ)*sourceEdge x/x) x := by
  have computed := ((burnolMellinTailPower_hasDerivAt (star coordinate.value) positive).mul
    (edge_primitive_hasDerivAt coordinate x positive)).const_mul (-(2:ℂ))
  have localRead : fixedEdgeReturnRaw coordinate =ᶠ[𝓝 x]
      fun y : ℝ=>-(2:ℂ)*(y:ℂ)^(-star coordinate.value)*edgeResponsePrimitive coordinate y := by
    filter_upwards [Ioo_mem_nhds positive inside] with y inWindow
    unfold fixedEdgeReturnRaw
    rw [abs_of_pos inWindow.1,min_eq_left inWindow.2.le]
  simp only [Pi.mul_apply] at computed
  have source : fixedEdgeReturnRaw coordinate =ᶠ[𝓝 x] fun y : ℝ=>-(2:ℂ)*((y:ℂ)^(-star coordinate.value)*edgeResponsePrimitive coordinate y) := by
    filter_upwards [localRead] with y read
    rw [read]
    ring
  apply (computed.congr_of_eventuallyEq source).congr_deriv
  have shifted : (x:ℂ)^(-(star coordinate.value+1))=(x:ℂ)^(-star coordinate.value)*(x:ℂ)⁻¹ := by
    rw [show -(star coordinate.value+1)=-star coordinate.value-1 by ring,
      Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),Complex.cpow_one,div_eq_mul_inv]
  have inverse : (x:ℂ)^(-star coordinate.value)*(x:ℂ)^(star coordinate.value-1)=(x:ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),
      show -star coordinate.value+(star coordinate.value-1)=-(1:ℂ) by ring,Complex.cpow_neg_one]
  unfold fixedEdgeReturnRaw
  rw [abs_of_pos positive,min_eq_left inside.le,shifted]
  rw [div_eq_mul_inv,div_eq_mul_inv]
  linear_combination -(2:ℂ)*sourceEdge x*inverse

 theorem fixed_edge_outside_profile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (outside : 4 < |x|) :
    fixedEdgeReturnRaw coordinate x=fixedEdgeReturnRaw coordinate 4*
      (4:ℂ)^(star coordinate.value)*((|x|:ℝ):ℂ)^(-star coordinate.value) := by
  unfold fixedEdgeReturnRaw
  rw [min_eq_right outside.le]
  norm_num only [show |(4:ℝ)|=4 by norm_num,min_self,Complex.ofReal_ofNat]
  have inverse : (4:ℂ)^(-star coordinate.value)*(4:ℂ)^(star coordinate.value)=1 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (4:ℂ)≠0),neg_add_cancel,Complex.cpow_zero]
  linear_combination ((2:ℂ)*((|x|:ℝ):ℂ)^(-star coordinate.value)*edgeResponsePrimitive coordinate 4)*inverse

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
