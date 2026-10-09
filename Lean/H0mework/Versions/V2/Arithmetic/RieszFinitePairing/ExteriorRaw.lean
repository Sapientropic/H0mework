import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.PairingRaw
import H0mework.Versions.V2.Arithmetic.RieszGreen.SourceDerivative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszSourceGreen
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "Fq" => burnolRadiusTruncatedFourierRaw q
local notation "b" => burnolRieszSingleFourierSource
local notation "bRaw" => burnolRieszSingleFourierSourceRaw
local notation "rRaw" => burnolRieszReturnRaw

private theorem fourier_raw_even_of_fixed (state : BurnolQuarterIntervalL2)
    (fixed : reflectRestricted q state = state) (frequency : ℝ) : Fq state (-frequency) = Fq state frequency := by
  let value := fourierL2 (burnolQuarterZeroExtension state)
  have even : reflectL2 value = value := by
    change reflectL2 (fourierL2 (burnolRadiusZeroExtension q state)) = _
    rw [← fourierL2_reflectL2_commute, burnolRadiusZeroExtension_reflect, fixed]
    rfl
  have read : (value : ℝ → ℂ) =ᵐ[volume] Fq state :=
    burnolRadiusFourierL2_zeroExtension_ae_eq_raw state
  have reflected : (fun x : ℝ => Fq state (-x)) =ᵐ[volume] Fq state := by
    filter_upwards [Lp.coeFn_compMeasurePreserving value negMeasurePreserving,
      negMeasurePreserving.quasiMeasurePreserving.ae read, read] with x reflection negative direct
    change reflectL2 value x = value (-x) at reflection
    rw [even] at reflection
    exact negative.symm.trans (reflection.symm.trans direct)
  have continuous := burnolRadiusTruncatedFourierRaw_continuous state
  exact congrFun (Measure.eq_of_ae_eq (μ := (volume : Measure ℝ)) reflected
    (continuous.comp continuous_neg) continuous) frequency

theorem source_fourier_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    Fq (b coordinate : BurnolQuarterIntervalL2) (-x) = Fq (b coordinate : BurnolQuarterIntervalL2) x :=
  fourier_raw_even_of_fixed _ (burnolRieszSingleFourierSource_reflection_fixed coordinate) x

theorem return_fourier_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    Fq (Constructor.returnState coordinate : BurnolQuarterIntervalL2) (-x) =
      Fq (Constructor.returnState coordinate : BurnolQuarterIntervalL2) x :=
  fourier_raw_even_of_fixed _ (burnolRieszSingleFourierReturn_reflection_fixed coordinate) x

theorem return_raw_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    rRaw coordinate (-x) = rRaw coordinate x := by
  unfold burnolRieszReturnRaw burnolMeanZeroFourierRaw
  rw [source_fourier_even]

theorem source_raw_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    bRaw coordinate (-x) = bRaw coordinate x := by
  change (burnolRieszFourierForcingRaw coordinate (-x) +
      (Fq (Constructor.returnState coordinate : BurnolQuarterIntervalL2) (-x) -
        burnolQuarterMeanCoefficient (burnolTruncatedFourier (Constructor.returnState coordinate : BurnolQuarterIntervalL2)))) =
    (burnolRieszFourierForcingRaw coordinate x +
      (Fq (Constructor.returnState coordinate : BurnolQuarterIntervalL2) x -
        burnolQuarterMeanCoefficient (burnolTruncatedFourier (Constructor.returnState coordinate : BurnolQuarterIntervalL2))))
  rw [Translator.ForcingMeanZero.forcingRaw_eq, Translator.ForcingMeanZero.forcingRaw_eq,
    Translator.ForcingWhole.raw_even, return_fourier_even]

theorem position_exterior_return_read (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszStatePositiveOuterRaw coordinate x = (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) -
      (rRaw coordinate x + burnolQuarterMeanCoefficient (burnolTruncatedFourier (b coordinate : BurnolQuarterIntervalL2))) := by
  unfold burnolRieszStatePositiveOuterRaw burnolRieszReturnRaw burnolMeanZeroFourierRaw
  rw [source_fourier_even]
  ring

theorem fourier_exterior_source_read (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszFourierExteriorRaw coordinate x = bRaw coordinate x + fourierMean coordinate := by
  change Translator.ForcingWhole.raw coordinate x +
      (1 / 2 : ℂ) * (Fq (Constructor.returnState coordinate : BurnolQuarterIntervalL2) x +
        Fq (Constructor.returnState coordinate : BurnolQuarterIntervalL2) (-x)) =
    (burnolRieszFourierForcingRaw coordinate x +
      (Fq (Constructor.returnState coordinate : BurnolQuarterIntervalL2) x -
        burnolQuarterMeanCoefficient (burnolTruncatedFourier (Constructor.returnState coordinate : BurnolQuarterIntervalL2)))) +
      (Translator.ForcingMeanZero.mean coordinate +
        burnolQuarterMeanCoefficient (burnolTruncatedFourier (Constructor.returnState coordinate : BurnolQuarterIntervalL2)))
  rw [return_fourier_even, Translator.ForcingMeanZero.forcingRaw_eq]
  ring

theorem fourier_raw_eq_exterior (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (outside : q < x) : burnolRieszFourierRaw coordinate x = burnolRieszFourierExteriorRaw coordinate x := by
  have positiveOutside : x ∉ symmetricInterval q := fun member => not_lt_of_ge member.2 outside
  have negativeOutside : -x ∉ symmetricInterval q := by intro member; linarith [member.1]
  simp only [burnolRieszFourierRaw, burnolEvenRaw, indicator_of_notMem positiveOutside,
    indicator_of_notMem negativeOutside, zero_add, mul_zero, sub_zero]

theorem fourier_raw_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszFourierRaw coordinate (-x) = burnolRieszFourierRaw coordinate x := by
  unfold burnolRieszFourierRaw burnolRieszFourierExteriorRaw burnolEvenRaw
  simp only [neg_neg]
  ring

def positionExteriorDerivative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ((-star coordinate.value) * (x : ℂ) ^ (-(star coordinate.value + 1))) -
    burnolRieszReturnRawDerivative coordinate x

theorem position_exterior_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (outside : q < x) : HasDerivAt (burnolRieszStatePositiveOuterRaw coordinate)
      (positionExteriorDerivative coordinate x) x := by
  have positive : 0 < x := lt_trans (by norm_num : (0 : ℝ) < q) outside
  rw [funext (position_exterior_return_read coordinate)]
  exact ((burnolMellinTailPower_hasDerivAt (star coordinate.value) positive).const_mul (1 / 2 : ℂ)).sub
    ((burnolRieszReturnRaw_hasDerivAt coordinate x).add_const
      (burnolQuarterMeanCoefficient (burnolTruncatedFourier (b coordinate : BurnolQuarterIntervalL2))))

theorem fourier_exterior_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (outside : q < x) : HasDerivAt (burnolRieszFourierExteriorRaw coordinate) (sourceRawDerivative coordinate x) x := by
  rw [funext (fourier_exterior_source_read coordinate)]
  exact (sourceRaw_hasDerivAt coordinate x (by linarith)).add_const (fourierMean coordinate)

theorem position_raw_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (outside : q < x) : HasDerivAt (burnolRieszStateRaw coordinate) (positionExteriorDerivative coordinate x) x := by
  apply (position_exterior_hasDerivAt coordinate outside).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds outside] with y hy
  exact burnolRieszStateRaw_eq_positiveOuter coordinate hy

theorem fourier_raw_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (outside : q < x) : HasDerivAt (burnolRieszFourierRaw coordinate) (sourceRawDerivative coordinate x) x := by
  apply (fourier_exterior_hasDerivAt coordinate outside).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds outside] with y hy
  exact fourier_raw_eq_exterior coordinate hy

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
