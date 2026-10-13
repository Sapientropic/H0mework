import H0mework.Versions.V2.Arithmetic.MobiusSource.Tate
import H0mework.Versions.V2.Arithmetic.RemainderSource.ResolventBoundary
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory Set
open scoped ArithmeticFunction BigOperators InnerProductSpace
abbrev Window := BurnolRadiusIntervalL2 4
abbrev Ambient := BurnolPaAmbientCarrier

def actualMean : BurnolL2 →L[ℂ] ℂ :=
  (‖intervalConstant (1/4:ℝ)‖^2:ℂ)⁻¹ •
    (innerSL ℂ (intervalConstant (1/4:ℝ))).comp (burnolRadiusRestriction (1/4:ℝ))
def coefficient (n : ℕ+) : ℂ := (ArithmeticFunction.moebius (n:ℕ):ℂ)*((n:ℕ):ℂ)⁻¹

def lowerPullback (n : ℕ+) : BurnolL2 →L[ℂ] Window := burnolWindowScalePullback 4 n-
  (ContinuousLinearMap.toSpanSingleton ℂ (intervalConstant 4)).comp actualMean
def lowerWindow : BurnolL2 →L[ℂ] Window := ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,coefficient n • lowerPullback n
def M : BurnolL2 →L[ℂ] BurnolL2 := (burnolRadiusZeroExtension 4).comp lowerWindow

theorem actual_mean_physical (value : Ambient) : actualMean (value : BurnolL2) =
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := rfl

theorem lower_pullback_physical (n : ℕ+) (value : Ambient) : lowerPullback n (value : BurnolL2)=burnolMobiusWindowPullback n value := rfl

theorem lower_window_physical (value : Ambient) : lowerWindow (value : BurnolL2)=burnolMobiusWindowSourceRead value := by
  simp only [lowerWindow,sum_apply,smul_apply,lower_pullback_physical,burnolMobiusWindowSourceRead,coefficient]

theorem lower_source_physical (value : Ambient) : M (value : BurnolL2)=burnolMobiusSourceL2 value := by
  unfold M burnolMobiusSourceL2
  simp only [ContinuousLinearMap.comp_apply,lower_window_physical]

-- The literal finite source receives actual L² input and its actual mean; no Pa membership is added.
theorem lower_pullback_read (n : ℕ+) (value : BurnolL2) :
    (lowerPullback n value : ℝ→ℂ) =ᵐ[volume.restrict (symmetricInterval 4)]
      fun x => value (x/(n:ℕ))-actualMean value := by
  apply (Lp.coeFn_sub _ _).trans
  filter_upwards [burnolWindowScalePullback_coeFn 4 n value,
    Lp.coeFn_smul (actualMean value) (intervalConstant 4),intervalConstant_coeFn 4] with x read scalar unit
  change burnolWindowScalePullback 4 n value x-(actualMean value • intervalConstant 4 : Window) x = _
  rw [read,scalar]
  simp only [Pi.smul_apply,smul_eq_mul,unit,mul_one]

theorem lower_window_read (value : BurnolL2) : (lowerWindow value : ℝ→ℂ) =ᵐ[volume.restrict (symmetricInterval 4)]
    fun x => ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,coefficient n*(value (x/(n:ℕ))-actualMean value) := by
  have read (indices : Finset ℕ+) : ((∑ n ∈ indices,coefficient n • lowerPullback n value : Window):ℝ→ℂ) =ᵐ[volume.restrict (symmetricInterval 4)]
      fun x => ∑ n ∈ indices,coefficient n*(value (x/(n:ℕ))-actualMean value) := by
    induction indices using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using! (Lp.coeFn_zero ℂ 2 (volume.restrict (symmetricInterval 4)))
    | @insert n indices missing previous =>
      rw [Finset.sum_insert missing]
      simp_rw [Finset.sum_insert missing]
      filter_upwards [Lp.coeFn_add (coefficient n • lowerPullback n value)
          (∑ m ∈ indices,coefficient m • lowerPullback m value),Lp.coeFn_smul (coefficient n) (lowerPullback n value),lower_pullback_read n value,previous] with x add scalar pull old
      rw [add]
      simp only [Pi.add_apply]
      rw [scalar]
      change coefficient n*lowerPullback n value x+_= _
      rw [pull,old]
  simpa only [lowerWindow,sum_apply,smul_apply] using read (burnolCenteredMobiusCutoffFinset 4)

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
