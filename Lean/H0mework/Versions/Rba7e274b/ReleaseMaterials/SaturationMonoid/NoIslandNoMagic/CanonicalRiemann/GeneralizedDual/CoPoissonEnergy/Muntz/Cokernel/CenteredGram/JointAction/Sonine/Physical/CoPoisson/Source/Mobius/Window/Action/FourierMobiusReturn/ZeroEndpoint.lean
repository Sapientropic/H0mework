import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.Primitive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators Topology
open OriginalRieszSource

theorem weighted_source_zero_endpoint (coordinate : BurnolCompletedMellinCoordinate) :
    (0:ℂ)^(star coordinate.value)*sourceH coordinate 0=0 := by
  have nonzero : star coordinate.value≠0 := by
    intro eq0
    have real:=congrArg Complex.re eq0
    simp only [Complex.star_def,Complex.conj_re,Complex.zero_re] at real
    linarith [coordinate.rightHalf]
  rw [Complex.zero_cpow nonzero,zero_mul]

 theorem actual_fourier_response_primitive (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (nonnegative : 0≤x) :
    fourierResponsePrimitive coordinate x=Kernel.beta coordinate*edgeResponsePrimitive coordinate x-
      (x:ℂ)^(star coordinate.value)*sourceH coordinate x-
        sourceSigma*sourceGamma coordinate*(x:ℂ)^(star coordinate.value)/star coordinate.value := by
  have rePositive : 0<(star coordinate.value).re := by simpa only [Complex.star_def,Complex.conj_re] using lt_trans (by norm_num : (0:ℝ)<1/2) coordinate.rightHalf
  have exponent : -1<(star coordinate.value-1).re := by simp only [Complex.sub_re,Complex.one_re];linarith
  have pI : IntervalIntegrable (fun x : ℝ=>(x:ℂ)^(star coordinate.value-1)) volume 0 x := intervalIntegral.intervalIntegrable_cpow' exponent
  have eI : IntervalIntegrable (fun x : ℝ=>(x:ℂ)^(star coordinate.value-1)*sourceEdge x) volume 0 x :=
    pI.mul_continuousOn finite_edge_continuous.continuousOn
  have dI : IntervalIntegrable (fun x : ℝ=>(x:ℂ)^(star coordinate.value-1)*((x:ℂ)*sourceHprime coordinate x+star coordinate.value*sourceH coordinate x)) volume 0 x :=
    pI.mul_continuousOn ((Complex.continuous_ofReal.mul (finite_source_derivative_continuous coordinate)).add
      ((finite_source_continuous coordinate).const_mul (star coordinate.value))).continuousOn
  have primitive := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le nonnegative
    (((Complex.continuous_ofReal_cpow_const rePositive).mul (finite_source_continuous coordinate)).continuousOn)
    (fun y inside=>weighted_source_derivative coordinate y inside.1) dI
  simp only [Pi.mul_apply] at primitive
  rw [Complex.ofReal_zero,weighted_source_zero_endpoint,sub_zero] at primitive
  have power := integral_cpow (a:=0) (b:=x) (r:=star coordinate.value-1) (Or.inl exponent)
  have nonzero : star coordinate.value≠0 := ne_of_apply_ne Complex.re rePositive.ne'
  simp only [show (star coordinate.value-1)+1=star coordinate.value by ring,
    Complex.ofReal_zero,Complex.zero_cpow nonzero,sub_zero] at power
  have split : (fun x : ℝ=>(x:ℂ)^(star coordinate.value-1)*(Kernel.beta coordinate*sourceEdge x-(x:ℂ)*sourceHprime coordinate x-star coordinate.value*sourceH coordinate x-sourceSigma*sourceGamma coordinate))=
      fun x : ℝ=>Kernel.beta coordinate*((x:ℂ)^(star coordinate.value-1)*sourceEdge x)-
        (x:ℂ)^(star coordinate.value-1)*((x:ℂ)*sourceHprime coordinate x+star coordinate.value*sourceH coordinate x)-
          (sourceSigma*sourceGamma coordinate)*(x:ℂ)^(star coordinate.value-1) := by funext y;ring
  unfold fourierResponsePrimitive edgeResponsePrimitive
  rw [split,intervalIntegral.integral_sub ((eI.const_mul _).sub dI) (pI.const_mul _),
    intervalIntegral.integral_sub (eI.const_mul _) dI,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,primitive,power]
  ring

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
