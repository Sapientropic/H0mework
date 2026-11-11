import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Homogeneous
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Remainder
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Homogeneous
open scoped Topology

private theorem kernel_mem (test:SchwartzMap ℝ ℂ):
    MemLp (fun x:ℝ=>coPoissonMuntzScaleRemainder test |x|) 2 volume:=
  (Lp.memLp (burnolRemainderL2Kernel test)).ae_eq (burnolRemainderL2Kernel_coeFn test)

/-- The actual homogeneous subtraction supplies the entire missing Fp/comb domain, including its non-L2 tail. -/
theorem actual_dual_fourier_remainder_integrable (c:BurnolCompletedMellinCoordinate)
    (test:SchwartzMap ℝ ℂ):
    Integrable (fun x:ℝ=>dualFourierRaw c x*coPoissonMuntzScaleRemainder test |x|):=by
  have native:=((Lp.memLp (jointSource c)).integrable_mul (kernel_mem test)).sub
    ((Lp.memLp (quarterWave c)).integrable_mul (kernel_mem test))
  have power:=(actual_homogeneous_remainder_integrable c test).const_mul
    (ForcingPrimitive.leadingCoefficient c)
  apply (native.add power).congr
  filter_upwards [actual_joint_homogeneous_raw c,actual_quarter_raw c] with x joint whole
  simp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply]
  rw [joint,whole]
  unfold homogeneousRaw
  ring

/-- The common L2 source consumes the original zero on the complete comb remainder, before any projection. -/
theorem actual_joint_remainder (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (test:SchwartzMap ℝ ℂ):
    burnolRemainderSourceRead (jointSource c) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (wholeValue c zero h positive)) test+
        (1/2:ℂ)*(∫x:ℝ,dualFourierRaw c x*coPoissonMuntzScaleRemainder test |x|):=by
  have original:Integrable (fun x:ℝ=>quarterWave c x*coPoissonMuntzScaleRemainder test |x|):=
    (Lp.memLp (quarterWave c)).integrable_mul (kernel_mem test)
  have dual:=actual_dual_fourier_remainder_integrable c test
  have power:=(actual_homogeneous_remainder_integrable c test).const_mul
    (ForcingPrimitive.leadingCoefficient c)
  have same:(fun x:ℝ=>jointSource c x*coPoissonMuntzScaleRemainder test |x|)=ᵐ[volume]
      (fun x:ℝ=>quarterWave c x*coPoissonMuntzScaleRemainder test |x|+
        dualFourierRaw c x*coPoissonMuntzScaleRemainder test |x|-
        ForcingPrimitive.leadingCoefficient c*(homogeneousRaw c x*coPoissonMuntzScaleRemainder test |x|)):=by
    filter_upwards [actual_joint_homogeneous_raw c,actual_quarter_raw c] with x joint whole
    rw [joint,whole]
    unfold homogeneousRaw
    ring
  have subIntegral:=integral_sub (original.add dual) power
  have addIntegral:=integral_add original dual
  simp only [Pi.add_apply] at subIntegral addIntegral
  rw [burnolRemainderSourceRead_integral,integral_congr_ae same,
    subIntegral,addIntegral,integral_const_mul]
  calc
    _=burnolRemainderSourceRead (quarterWave c) test+
        (1/2:ℂ)*(∫x:ℝ,dualFourierRaw c x*coPoissonMuntzScaleRemainder test |x|)-
        ForcingPrimitive.leadingCoefficient c*((1/2:ℂ)*
          ∫x:ℝ,homogeneousRaw c x*coPoissonMuntzScaleRemainder test |x|):=by
      rw [burnolRemainderSourceRead_integral]
      ring
    _=_:=by rw [actual_original_homogeneous_action_zero c zero test,mul_zero,sub_zero,
      actual_whole_realizes c zero h positive test]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Remainder
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
