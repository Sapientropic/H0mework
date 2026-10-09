import H0mework.Arithmetic.RieszGreen.WeakDerivative
import H0mework.Versions.V2.Arithmetic.RieszGreen.SourceNormalization
import H0mework.Versions.V2.Arithmetic.RieszSourceKernel.Generated

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex Filter MeasureTheory
open scoped Topology
open OriginalRieszSource OriginalRieszSource.Translator

noncomputable section

local notation "q" => (1 / 4 : ℝ)

theorem forcing_weighted_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (nonzero : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * ForcingWhole.raw coordinate y)
      (star coordinate.value * ForcingWhole.raw coordinate x +
        ForcingWhole.coefficient coordinate * Edge.raw q x) x := by
  apply weak_hasDerivAt
    (fun y : ℝ => (y : ℂ) * ForcingWhole.raw coordinate y)
    (fun y : ℝ => star coordinate.value * ForcingWhole.raw coordinate y +
      ForcingWhole.coefficient coordinate * Edge.raw q y)
    (LocallyIntegrable.continuous_mul Complex.continuous_ofReal (ForcingWhole.raw_local coordinate))
    ((LocallyIntegrable.continuous_mul continuous_const (ForcingWhole.raw_local coordinate)).add
      ((Edge.raw_continuous q).const_mul (ForcingWhole.coefficient coordinate)).locallyIntegrable)
    (ForcingWhole.raw_weighted_weak coordinate) x
  · filter_upwards [eventually_ne_nhds nonzero] with y hy
    exact Complex.continuous_ofReal.continuousAt.mul (ForcingWhole.raw_continuousAt coordinate hy)
  · exact (continuousAt_const.mul (ForcingWhole.raw_continuousAt coordinate nonzero)).add
      (continuousAt_const.mul (Edge.raw_continuous q).continuousAt)

theorem forcing_raw_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (nonzero : x ≠ 0) :
    HasDerivAt (ForcingWhole.raw coordinate)
      (((star coordinate.value - 1) * ForcingWhole.raw coordinate x +
        ForcingWhole.coefficient coordinate * Edge.raw q x) / (x : ℂ)) x := by
  have castNonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  have identity : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x :=
    Complex.ofRealCLM.hasDerivAt
  have quotient := (forcing_weighted_hasDerivAt coordinate x nonzero).div identity castNonzero
  have same : ForcingWhole.raw coordinate =ᶠ[𝓝 x]
      fun y : ℝ => ((y : ℂ) * ForcingWhole.raw coordinate y) / (y : ℂ) := by
    filter_upwards [eventually_ne_nhds nonzero] with y hy
    field_simp [Complex.ofReal_ne_zero.mpr hy]
  convert! quotient.congr_of_eventuallyEq same using 1
  field_simp
  ring

def sourceRawDerivative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((star coordinate.value - 1) * ForcingWhole.raw coordinate x +
    ForcingWhole.coefficient coordinate * Edge.raw q x) / (x : ℂ) +
      Constructor.fourierDerivative (burnolRieszReturnRaw coordinate) x

theorem sourceRaw_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (nonzero : x ≠ 0) :
    HasDerivAt (burnolRieszSingleFourierSourceRaw coordinate)
      (sourceRawDerivative coordinate x) x := by
  have forcing := (forcing_raw_hasDerivAt coordinate x nonzero).sub_const
    (ForcingMeanZero.mean coordinate)
  exact forcing.add (Constructor.secondReturnRaw_hasDerivAt coordinate x)

theorem sourceRaw_weighted (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (nonzero : x ≠ 0) :
    (x : ℂ) * sourceRawDerivative coordinate x +
        (1 / 2 : ℂ) * burnolRieszSingleFourierSourceRaw coordinate x =
      (star coordinate.value - 1 / 2) * burnolRieszFourierForcingRaw coordinate x +
        ForcingWhole.coefficient coordinate * Edge.raw q x +
        Constructor.secondEulerRaw coordinate x +
        (star coordinate.value - 1) * ForcingMeanZero.mean coordinate := by
  change (x : ℂ) * sourceRawDerivative coordinate x +
    (1 / 2 : ℂ) * (burnolRieszFourierForcingRaw coordinate x +
      Constructor.secondReturnRaw coordinate x) = _
  rw [ForcingMeanZero.forcingRaw_eq]
  unfold sourceRawDerivative Constructor.secondEulerRaw
  have castNonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  field_simp
  ring

theorem sourceRaw_weighted_eq (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (nonzero : x ≠ 0) :
    (x : ℂ) * sourceRawDerivative coordinate x +
        (1 / 2 : ℂ) * burnolRieszSingleFourierSourceRaw coordinate x = weightedRaw coordinate x := by
  rw [sourceRaw_weighted coordinate x nonzero, weightedRaw_eq, ForcingMeanZero.forcingRaw_eq]
  unfold ForcingWhole.coefficient
  ring

theorem source_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (nonzero : x ≠ 0) :
    HasDerivAt (burnolRieszSingleFourierSourceRaw coordinate)
      ((weightedRaw coordinate x - (1 / 2 : ℂ) * burnolRieszSingleFourierSourceRaw coordinate x) /
        (x : ℂ)) x := by
  have equal : sourceRawDerivative coordinate x =
      (weightedRaw coordinate x - (1 / 2 : ℂ) * burnolRieszSingleFourierSourceRaw coordinate x) /
        (x : ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr nonzero)).mpr
    linear_combination sourceRaw_weighted_eq coordinate x nonzero
  rw [← equal]
  exact sourceRaw_hasDerivAt coordinate x nonzero

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
