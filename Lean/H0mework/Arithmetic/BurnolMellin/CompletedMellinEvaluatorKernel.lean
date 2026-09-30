import H0mework.Arithmetic.MellinProjection.CompletedEvaluator

/-!
# Fixed quarter-radius completed-Mellin evaluator

These declarations preserve the historical public interface. Every kernel,
functional, and Riesz statement is now the `r = 1/4` specialization of the
radius-parametrized completed-Mellin construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

private theorem burnolCommonGapRadius_positive :
    0 < burnolUnscaledCommonGapRadius := by
  norm_num [burnolUnscaledCommonGapRadius]

def burnolMellinTailKernelRaw (coordinate : ℂ) (t : ℝ) : ℂ :=
  burnolRadiusMellinTailKernelRaw
    burnolUnscaledCommonGapRadius coordinate t

theorem star_burnolMellinTailKernelRaw
    (coordinate : ℂ) (t : ℝ) :
    star (burnolMellinTailKernelRaw coordinate t) =
      if t ∈ Ioi burnolUnscaledCommonGapRadius then
        (t : ℂ) ^ (-coordinate)
      else 0 := by
  exact star_burnolRadiusMellinTailKernelRaw
    burnolCommonGapRadius_positive coordinate t

theorem burnolMellinTailKernelRaw_measurable (coordinate : ℂ) :
    Measurable (burnolMellinTailKernelRaw coordinate) := by
  exact burnolRadiusMellinTailKernelRaw_measurable
    burnolCommonGapRadius_positive coordinate

theorem burnolMellinTailKernelRaw_memLp
    (coordinate : ℂ) (rightHalf : 1 / 2 < coordinate.re) :
    MemLp (burnolMellinTailKernelRaw coordinate) 2 volume := by
  exact burnolRadiusMellinTailKernelRaw_memLp
    burnolCommonGapRadius_positive coordinate rightHalf

def burnolMellinTailKernelL2
    (coordinate : ℂ) (rightHalf : 1 / 2 < coordinate.re) : BurnolL2 :=
  burnolRadiusMellinTailKernelL2 burnolUnscaledCommonGapRadius
    burnolCommonGapRadius_positive coordinate rightHalf

def burnolMellinTailEvaluator
    (coordinate : ℂ) (rightHalf : 1 / 2 < coordinate.re) :
    BurnolL2 →L[ℂ] ℂ :=
  burnolRadiusMellinTailEvaluator burnolUnscaledCommonGapRadius
    burnolCommonGapRadius_positive coordinate rightHalf

theorem burnolMellinTailEvaluator_eq_integral
    (coordinate : ℂ) (rightHalf : 1 / 2 < coordinate.re)
    (value : BurnolL2) :
    burnolMellinTailEvaluator coordinate rightHalf value =
      ∫ t : ℝ in Ioi burnolUnscaledCommonGapRadius,
        (t : ℂ) ^ (-coordinate) * value t := by
  exact burnolRadiusMellinTailEvaluator_eq_integral
    burnolUnscaledCommonGapRadius burnolCommonGapRadius_positive
      coordinate rightHalf value

theorem burnolMellinWeight_integrableOn_tail
    (coordinate : ℂ) (rightHalf : 1 / 2 < coordinate.re)
    (value : BurnolL2) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-coordinate) * value t)
      (Ioi burnolUnscaledCommonGapRadius) := by
  exact burnolRadiusMellinWeight_integrableOn_tail
    burnolUnscaledCommonGapRadius burnolCommonGapRadius_positive
      coordinate rightHalf value

def burnolMellinGapMoment (coordinate : ℂ) : ℂ :=
  burnolRadiusMellinGapMoment burnolUnscaledCommonGapRadius coordinate

def burnolCompletedMellinEvaluator
    (coordinate : BurnolCompletedMellinCoordinate) :
    EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius →L[ℂ] ℂ :=
  burnolRadiusCompletedMellinEvaluator burnolUnscaledCommonGapRadius
    burnolCommonGapRadius_positive coordinate

theorem burnolCompletedMellinEvaluator_apply
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    burnolCompletedMellinEvaluator coordinate value =
      burnolMellinGapMoment coordinate.value •
          burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value +
        burnolMellinTailEvaluator coordinate.value coordinate.rightHalf
          (value : BurnolL2) := by
  rfl

def burnolCompletedMellinRieszVector
    (coordinate : BurnolCompletedMellinCoordinate) :
    EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius :=
  burnolRadiusCompletedMellinRieszVector burnolUnscaledCommonGapRadius
    burnolCommonGapRadius_positive coordinate

theorem burnolCompletedMellinRieszVector_readback
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate) value =
      burnolCompletedMellinEvaluator coordinate value := by
  exact burnolRadiusCompletedMellinRieszVector_readback
    burnolUnscaledCommonGapRadius burnolCommonGapRadius_positive
      coordinate value

theorem burnolCompletedMellinEvaluator_eq_radiusSpecialization
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolCompletedMellinEvaluator coordinate =
      burnolRadiusCompletedMellinEvaluator (1 / 4 : ℝ)
        (by norm_num) coordinate := by
  rfl

theorem burnolCompletedMellinRieszVector_eq_radiusSpecialization
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolCompletedMellinRieszVector coordinate =
      burnolRadiusCompletedMellinRieszVector (1 / 4 : ℝ)
        (by norm_num) coordinate := by
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
