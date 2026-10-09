import H0mework.Versions.V2.Arithmetic.RieszEuler.Forcing
import H0mework.Versions.V2.Arithmetic.RieszEuler.EdgeFourier
import H0mework.Versions.V2.Arithmetic.MellinProjection.Canonical
import H0mework.Arithmetic.RieszForcing.WeakInterval

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Translator.ForcingWhole

open Complex Filter MeasureTheory Set FourierTransform
open scoped ENNReal Topology FourierTransform
noncomputable section

local notation "q" => (1 / 4 : ℝ)

def whole (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate))

def raw (coordinate : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  burnolEvenRaw (burnolGapTailFourierRaw q coordinate)

def coefficient (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  star coordinate.value * GapEuler.gapMean q coordinate

theorem whole_read (coordinate : BurnolCompletedMellinCoordinate) :
    (whole coordinate : ℝ → ℂ) =ᵐ[volume] raw coordinate := by
  have source := burnolEvenRaw_ae
    (fourierL2 (burnolAmbientCompletedMellinKernelFormula coordinate))
    (burnolGapTailFourierRaw q coordinate)
    (burnolGapTailFourier_ae_canonical q (by norm_num) coordinate)
  rw [← fourierL2_burnolAmbientEvenPart] at source
  exact source

theorem raw_local (coordinate : BurnolCompletedMellinCoordinate) :
    LocallyIntegrable (raw coordinate) :=
  ((Lp.memLp (whole coordinate)).locallyIntegrable (by norm_num)).congr (whole_read coordinate)

theorem raw_continuousAt (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ} (nonzero : x ≠ 0) :
    ContinuousAt (raw coordinate) x :=
  continuousAt_const.mul
    ((burnolGapTailFourierRaw_continuousAt q (by norm_num) coordinate nonzero).add
      ((burnolGapTailFourierRaw_continuousAt q (by norm_num) coordinate
        (neg_ne_zero.mpr nonzero)).comp continuous_neg.continuousAt))

theorem raw_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    raw coordinate (-x) = raw coordinate x := by
  unfold raw burnolEvenRaw
  simp only [neg_neg]
  ring

theorem whole_weighted_derivative (coordinate : BurnolCompletedMellinCoordinate) :
    TemperedDistribution.derivCLM ℂ
        (GapEuler.position (whole coordinate : TemperedDistribution ℝ ℂ)) =
      star coordinate.value • (whole coordinate : TemperedDistribution ℝ ℂ) +
        coefficient coordinate • 𝓕 (GapEuler.edge q) := by
  have source := GapEuler.original_fourier_euler q (by norm_num) coordinate
  change GapEuler.euler (whole coordinate : TemperedDistribution ℝ ℂ) -
      (star coordinate.value - 1 / 2) • (whole coordinate : TemperedDistribution ℝ ℂ) =
    coefficient coordinate • 𝓕 (GapEuler.edge q) at source
  have split : TemperedDistribution.derivCLM ℂ
        (GapEuler.position (whole coordinate : TemperedDistribution ℝ ℂ)) =
      GapEuler.euler (whole coordinate : TemperedDistribution ℝ ℂ) +
        (1 / 2 : ℂ) • (whole coordinate : TemperedDistribution ℝ ℂ) := by
    rw [GapEuler.derivative_position]
    unfold GapEuler.euler
    simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
    module
  rw [split, eq_add_of_sub_eq source]
  module

theorem raw_test_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) : Integrable (fun x : ℝ => raw coordinate x * test x) := by
  have source := (Lp.memLp (whole coordinate)).integrable_mul (test.memLp 2)
  apply source.congr
  filter_upwards [whole_read coordinate] with x read
  change whole coordinate x * test x = _
  rw [read]

theorem raw_weighted_weak (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, ((x : ℂ) * raw coordinate x) * deriv test x) =
      -(∫ x : ℝ,
        (star coordinate.value * raw coordinate x + coefficient coordinate * Edge.raw q x) * test x) := by
  have source := congrArg (fun value : TemperedDistribution ℝ ℂ => value test)
    (whole_weighted_derivative coordinate)
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [TemperedDistribution.derivCLM_apply_apply, GapEuler.position,
    TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    add_apply, smul_apply, smul_eq_mul] at source
  rw [Edge.fourier_edge_pairing q (by norm_num) test] at source
  have leftRead :
      (∫ x : ℝ, SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
        (-SchwartzMap.derivCLM ℂ ℂ test) x * whole coordinate x) =
      -(∫ x : ℝ, ((x : ℂ) * raw coordinate x) * deriv test x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [whole_read coordinate] with x read
    rw [read, SchwartzMap.smulLeftCLM_apply growth]
    simp only [smul_eq_mul, neg_apply, SchwartzMap.derivCLM_apply]
    ring
  have valueRead : (∫ x : ℝ, test x * whole coordinate x) =
      ∫ x : ℝ, raw coordinate x * test x := by
    apply integral_congr_ae
    filter_upwards [whole_read coordinate] with x read
    rw [read, mul_comm]
  rw [leftRead, valueRead] at source
  have edgeIntegrable : Integrable (fun x : ℝ => Edge.raw q x * test x) := by
    simpa only [mul_comm] using Edge.test_integrable q (by norm_num) test
  have rightRead : (∫ x : ℝ,
      (star coordinate.value * raw coordinate x + coefficient coordinate * Edge.raw q x) * test x) =
      star coordinate.value * (∫ x : ℝ, raw coordinate x * test x) +
        coefficient coordinate * (∫ x : ℝ, test x * Edge.raw q x) := by
    have first := (raw_test_integrable coordinate test).const_mul (star coordinate.value)
    have second := edgeIntegrable.const_mul (coefficient coordinate)
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add first (by simpa only [mul_comm] using second)]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [rightRead]
  exact neg_eq_iff_eq_neg.mp source

theorem raw_interval_ibp (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ in Ioc (-q) q,
      ((x : ℂ) * raw coordinate x) * deriv test x +
        (star coordinate.value * raw coordinate x + coefficient coordinate * Edge.raw q x) * test x) =
      (q : ℂ) * raw coordinate q * (test q + test (-q)) := by
  have valueLocal : LocallyIntegrable (fun x : ℝ => (x : ℂ) * raw coordinate x) :=
    LocallyIntegrable.continuous_mul Complex.continuous_ofReal (raw_local coordinate)
  have rhsLocal : LocallyIntegrable (fun x : ℝ =>
      star coordinate.value * raw coordinate x + coefficient coordinate * Edge.raw q x) :=
    (LocallyIntegrable.continuous_mul continuous_const (raw_local coordinate)).add
      ((Edge.raw_continuous q).const_mul (coefficient coordinate)).locallyIntegrable
  have result := WeakInterval.schwartz_interval_ibp _ _ valueLocal rhsLocal
    (raw_weighted_weak coordinate)
    (Complex.continuous_ofReal.continuousAt.mul (raw_continuousAt coordinate (by norm_num)))
    (Complex.continuous_ofReal.continuousAt.mul (raw_continuousAt coordinate (by norm_num))) test
  rw [raw_even] at result
  push_cast at result
  exact result.trans (by push_cast; ring)

end
end OriginalRieszSource.Translator.ForcingWhole
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
