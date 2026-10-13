import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.Word
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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
attribute [local instance 1100] NormedSpace.complexToReal

def edgeResponsePrimitive (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..x,(t:ℂ)^(star coordinate.value-1)*sourceEdge t

def fourierResponsePrimitive (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..x,(t:ℂ)^(star coordinate.value-1)*
    (Kernel.beta coordinate*sourceEdge t-(t:ℂ)*sourceHprime coordinate t-
      star coordinate.value*sourceH coordinate t-sourceSigma*sourceGamma coordinate)

theorem full_source_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    HasDerivAt (fullFourierSource coordinate) (burnolRieszReturnRawDerivative coordinate x) x := by
  have source := (burnolRieszReturnRaw_hasDerivAt coordinate x).add_const
    (burnolQuarterMeanCoefficient (burnolTruncatedFourier (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2)))
  convert! source using 1
  funext y
  exact original_full_source_mean coordinate y

 theorem finite_source_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    HasDerivAt (sourceH coordinate) (sourceHprime coordinate x) x := by
  unfold sourceH sourceHprime
  apply HasDerivAt.fun_sum
  intro n _
  have scalar : HasDerivAt (fun y : ℝ=>y/(n:ℕ)) (((n:ℕ):ℝ)⁻¹) x := by
    convert! (hasDerivAt_id x).div_const ((n:ℕ):ℝ) using 1
    simp
  have pulled :=  (full_source_hasDerivAt coordinate (x/(n:ℕ))).scomp x scalar
  have generated := pulled.const_mul (Paid.coefficient n)
  simpa only [Function.comp_apply,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,mul_assoc,mul_comm,mul_left_comm] using generated

 theorem finite_source_continuous (coordinate : BurnolCompletedMellinCoordinate) : Continuous (sourceH coordinate) :=
  continuous_iff_continuousAt.mpr fun x=>(finite_source_hasDerivAt coordinate x).continuousAt

theorem finite_source_derivative_continuous (coordinate : BurnolCompletedMellinCoordinate) : Continuous (sourceHprime coordinate) := by
  unfold sourceHprime
  exact continuous_finsetSum _ fun n _=>continuous_const.mul
    ((burnolRieszReturnRawDerivative_continuous coordinate).comp (by fun_prop))

 theorem finite_edge_continuous : Continuous sourceEdge := by
  unfold sourceEdge
  exact continuous_finsetSum _ fun n _=>continuous_const.mul ((Edge.raw_continuous (1/4:ℝ)).comp (by fun_prop))

 theorem weighted_source_derivative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    HasDerivAt (fun y : ℝ=>(y:ℂ)^(star coordinate.value)*sourceH coordinate y)
      ((x:ℂ)^(star coordinate.value-1)*((x:ℂ)*sourceHprime coordinate x+star coordinate.value*sourceH coordinate x)) x := by
  have power := burnolMellinTailPower_hasDerivAt (-star coordinate.value) positive
  have generated := power.mul (finite_source_hasDerivAt coordinate x)
  convert! generated using 1
  · funext y
    simp only [neg_neg,Pi.mul_apply]
  · rw [show -(-star coordinate.value+1)=star coordinate.value-1 by ring,neg_neg]
    have shifted : (x:ℂ)^(star coordinate.value)=(x:ℂ)^(star coordinate.value-1)*(x:ℂ) := by
      calc
        _ = (x:ℂ)^((star coordinate.value-1)+1) := by congr 1;ring
        _ = _ := by rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),Complex.cpow_one]
    rw [shifted]
    ring

-- Positive-band FTC computes the complete finite Fourier ordinary forcing without changing its source.
theorem actual_fourier_response_band (coordinate : BurnolCompletedMellinCoordinate) (lower upper : ℝ)
    (positive : 0<lower) (ordered : lower≤upper) :
    (∫ x : ℝ in lower..upper,(x:ℂ)^(star coordinate.value-1)*
      (Kernel.beta coordinate*sourceEdge x-(x:ℂ)*sourceHprime coordinate x-
        star coordinate.value*sourceH coordinate x-sourceSigma*sourceGamma coordinate))=
      Kernel.beta coordinate*(edgeResponsePrimitive coordinate upper-edgeResponsePrimitive coordinate lower)-
        ((upper:ℂ)^(star coordinate.value)*sourceH coordinate upper-(lower:ℂ)^(star coordinate.value)*sourceH coordinate lower)-
          sourceSigma*sourceGamma coordinate*(∫ x : ℝ in lower..upper,(x:ℂ)^(star coordinate.value-1)) := by
  have exponent : -1<(star coordinate.value-1).re := by simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re];linarith [coordinate.rightHalf]
  have pw : IntervalIntegrable (fun x : ℝ=>(x:ℂ)^(star coordinate.value-1)) volume lower upper := intervalIntegral.intervalIntegrable_cpow' exponent
  have edgeI : ∀ a b : ℝ,IntervalIntegrable (fun x : ℝ=>(x:ℂ)^(star coordinate.value-1)*sourceEdge x) volume a b := fun a b=>
    (intervalIntegral.intervalIntegrable_cpow' exponent).mul_continuousOn finite_edge_continuous.continuousOn
  have derivativeContinuous : ContinuousOn (fun x : ℝ=>(x:ℂ)^(star coordinate.value-1)*((x:ℂ)*sourceHprime coordinate x+star coordinate.value*sourceH coordinate x)) (uIcc lower upper) := by
    apply ContinuousOn.mul
    · exact continuousOn_of_forall_continuousAt (fun x inside=>
        Complex.continuousAt_ofReal_cpow_const x (star coordinate.value-1)
          (Or.inr (ne_of_gt (positive.trans_le ((uIcc_of_le ordered ▸ inside).1)))))
    · exact ((Complex.continuous_ofReal.mul (finite_source_derivative_continuous coordinate)).add
        ((finite_source_continuous coordinate).const_mul (star coordinate.value))).continuousOn
  have derivativeInt : IntervalIntegrable (fun x : ℝ=>(x:ℂ)^(star coordinate.value-1)*((x:ℂ)*sourceHprime coordinate x+star coordinate.value*sourceH coordinate x)) volume lower upper := derivativeContinuous.intervalIntegrable
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x inside=>weighted_source_derivative coordinate x (positive.trans_le ((uIcc_of_le ordered ▸ inside).1))) derivativeInt
  have adjacent := intervalIntegral.integral_add_adjacent_intervals (edgeI 0 lower) (edgeI lower upper)
  unfold edgeResponsePrimitive
  have split : (fun x : ℝ=>(x:ℂ)^(star coordinate.value-1)*(Kernel.beta coordinate*sourceEdge x-(x:ℂ)*sourceHprime coordinate x-star coordinate.value*sourceH coordinate x-sourceSigma*sourceGamma coordinate))=
      fun x : ℝ=>Kernel.beta coordinate*((x:ℂ)^(star coordinate.value-1)*sourceEdge x)-
        (x:ℂ)^(star coordinate.value-1)*((x:ℂ)*sourceHprime coordinate x+star coordinate.value*sourceH coordinate x)-
          (sourceSigma*sourceGamma coordinate)*(x:ℂ)^(star coordinate.value-1) := by funext x;ring
  rw [split,intervalIntegral.integral_sub ((edgeI lower upper).const_mul _ |>.sub derivativeInt) (pw.const_mul _),
    intervalIntegral.integral_sub ((edgeI lower upper).const_mul _) derivativeInt,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,generated]
  linear_combination Kernel.beta coordinate*adjacent

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
