import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierPrimitiveAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierPrimitiveActionSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource

def anchoredEdgeIntegral (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∫ t : ℝ in (1/4:ℝ)..x,(t:ℂ)^(-star coordinate.value)*Edge.raw (1/4:ℝ) t

def sourceFourierAnchor (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  Paid.primitiveScale coordinate*burnolEvenRaw
    (fun x:ℝ=>burnolGapTailFourierNumerator (1/4:ℝ) coordinate x/
      (2*(Real.pi:ℂ)*Complex.I*(x:ℂ))) (1/4:ℝ)

theorem original_FP_anchor (coordinate : BurnolCompletedMellinCoordinate) :
    primitiveFourierRaw coordinate (1/4:ℝ)=sourceFourierAnchor coordinate := rfl

def anchoredFourierProfile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (x:ℂ)^(star coordinate.value-1)*
    (((1/4:ℝ):ℂ)^(1-star coordinate.value)*sourceFourierAnchor coordinate-anchoredEdgeIntegral coordinate x)

theorem original_FP_weighted_power_derivative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    HasDerivAt (fun t:ℝ=>(t:ℂ)^(1-star coordinate.value)*primitiveFourierRaw coordinate t)
      (-((x:ℂ)^(-star coordinate.value)*Edge.raw (1/4:ℝ) x)) x := by
  have parameterNonzero : 1-star coordinate.value≠0 := by
    intro zero
    have real := congrArg Complex.re zero
    norm_num [Complex.star_def] at real
    linarith [coordinate.belowOne]
  have actual := (hasDerivAt_ofReal_cpow_const positive.ne' parameterNonzero).mul
    (original_FP_ordinary_derivative coordinate x positive.ne')
  convert! actual using 1
  have castNonzero : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
  rw [show 1-star coordinate.value-1= -star coordinate.value by ring]
  have power : (x:ℂ)^(1-star coordinate.value)/(x:ℂ)=(x:ℂ)^(-star coordinate.value) := by
    calc
      _=(x:ℂ)^(1-star coordinate.value)/(x:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
      _=(x:ℂ)^((1-star coordinate.value)-1) := (Complex.cpow_sub _ _ castNonzero).symm
      _=_ := by congr 1;ring
  rw [div_eq_mul_inv] at power
  simp only [div_eq_mul_inv]
  norm_num only [div_eq_mul_inv,one_mul] at *
  linear_combination -((star coordinate.value-1)*primitiveFourierRaw coordinate x-Edge.raw (1/4:ℝ) x)*power

theorem original_FP_anchored_profile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    primitiveFourierRaw coordinate x=anchoredFourierProfile coordinate x := by
  have lowerPositive : 0<min (1/4:ℝ) x := lt_min (by norm_num) positive
  have actual : (∫ t : ℝ in (1/4:ℝ)..x,-((t:ℂ)^(-star coordinate.value)*Edge.raw (1/4:ℝ) t))=
    (x:ℂ)^(1-star coordinate.value)*primitiveFourierRaw coordinate x-
      ((1/4:ℝ):ℂ)^(1-star coordinate.value)*primitiveFourierRaw coordinate (1/4:ℝ) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t inside=>original_FP_weighted_power_derivative coordinate t (lowerPositive.trans_le (show min (1/4:ℝ) x≤t from inside.1)))
    have continuous : ContinuousOn (fun t:ℝ=>-((t:ℂ)^(-star coordinate.value)*Edge.raw (1/4:ℝ) t)) (uIcc (1/4:ℝ) x) := by
      intro t inside
      have positive := lowerPositive.trans_le inside.1
      exact ((hasDerivAt_ofReal_cpow_const positive.ne' (by intro zero;have re := congrArg Complex.re zero;norm_num [Complex.star_def] at re;linarith [coordinate.rightHalf])).continuousAt.mul
        (Edge.raw_continuous (1/4:ℝ)).continuousAt).neg.continuousWithinAt
    exact continuous.intervalIntegrable
  rw [intervalIntegral.integral_neg] at actual
  have relation : (x:ℂ)^(1-star coordinate.value)*primitiveFourierRaw coordinate x=
      ((1/4:ℝ):ℂ)^(1-star coordinate.value)*primitiveFourierRaw coordinate (1/4:ℝ)-anchoredEdgeIntegral coordinate x := by
    unfold anchoredEdgeIntegral
    linear_combination -actual
  unfold anchoredFourierProfile
  rw [← original_FP_anchor,← relation,← mul_assoc,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),
    show star coordinate.value-1+(1-star coordinate.value)=0 by ring,Complex.cpow_zero,one_mul]
end OriginalFourierPrimitiveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
