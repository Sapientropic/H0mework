import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.NativeRead
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped Topology InnerProductSpace ENNReal
open OriginalTwoWindowInverseForcing
local notation "q" => (1/4:ℝ)

def sourceBand (h : ℝ) : Set ℝ := uIcc (lowerRadius h) (upperRadius h)
def bLeg (coordinate : BurnolCompletedMellinCoordinate) (scale : ℝ) (x : ℝ) : ℂ :=
  b coordinate (Real.exp scale*x)
def pLeg (coordinate : BurnolCompletedMellinCoordinate) (scale : ℝ) (x : ℝ) : ℂ :=
  p coordinate (Real.exp scale*x)

theorem bLeg_continuousOn (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) :
    ContinuousOn (bLeg coordinate scale) (sourceBand h) := by
  intro x inside
  exact ((b_hasDerivAt coordinate _ (mul_pos (Real.exp_pos scale)
    (two_window_positive h x inside))).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>Real.exp scale*y) x)).continuousWithinAt
theorem pLeg_continuousOn (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) :
    ContinuousOn (pLeg coordinate scale) (sourceBand h) := by
  intro x inside
  exact ((p_hasDerivAt coordinate _ (mul_pos (Real.exp_pos scale)
    (two_window_positive h x inside))).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>Real.exp scale*y) x)).continuousWithinAt

private theorem band_memLp (h : ℝ) (f : ℝ→ℂ)
    (continuous : ContinuousOn f (sourceBand h)) :
    MemLp f 2 (volume.restrict (sourceBand h)) := by
  have : IsFiniteMeasure (volume.restrict (sourceBand h)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact isCompact_uIcc.measure_lt_top
  obtain ⟨C,bounded⟩:=isCompact_uIcc.exists_bound_of_continuousOn continuous
  exact MemLp.of_bound (continuous.aestronglyMeasurable measurableSet_uIcc) C
    (ae_restrict_of_forall_mem measurableSet_uIcc fun x inside=>bounded x inside)

theorem bLeg_memLp (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) :
    MemLp (bLeg coordinate scale) 2 (volume.restrict (sourceBand h)) := by
  exact band_memLp h _ (bLeg_continuousOn coordinate h scale)
theorem pLeg_memLp (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) :
    MemLp (pLeg coordinate scale) 2 (volume.restrict (sourceBand h)) := by
  exact band_memLp h _ (pLeg_continuousOn coordinate h scale)

def bBand (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) : BurnolL2 :=
  ((memLp_indicator_iff_restrict (show MeasurableSet (sourceBand h) from measurableSet_uIcc)).mpr
    (bLeg_memLp coordinate h scale)).toLp
    ((sourceBand h).indicator (bLeg coordinate scale))
def pBand (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) : BurnolL2 :=
  ((memLp_indicator_iff_restrict (show MeasurableSet (sourceBand h) from measurableSet_uIcc)).mpr
    (pLeg_memLp coordinate h scale)).toLp
    ((sourceBand h).indicator (pLeg coordinate scale))

-- These columns are actual finite-band Fourier adjoints of the same original b/p legs.
def cotestColumn (scale : ℝ) (field : BurnolL2) : BurnolQuarterMeanZeroCarrier :=
  Constructor.zeroMean (burnolQuarterRestriction
    (burnolAmbientEvenPart (fourierL2 (burnolMultiplicativeDilation (-scale) field))))
def sourceColumns (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier)×
      (BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier) :=
  ((cotestColumn (-h/2) (bBand coordinate h (h/2)),
    cotestColumn (-h/2) (pBand coordinate h (h/2))),
   (cotestColumn (h/2) (bBand coordinate h (-h/2)),
    cotestColumn (h/2) (pBand coordinate h (-h/2))))

def inverseCotest (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier :=
  (burnolMeanZeroBlockInverse
    ((sourceColumns coordinate h).1.1-burnolMeanZeroTruncatedFourier (sourceColumns coordinate h).1.2),
   burnolMeanZeroBlockInverse
    ((sourceColumns coordinate h).2.1-burnolMeanZeroTruncatedFourier (sourceColumns coordinate h).2.2))

theorem actual_inverse_cotest (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    burnolMeanZeroOneMinusSquare (inverseCotest coordinate h).1=
      (sourceColumns coordinate h).1.1-burnolMeanZeroTruncatedFourier (sourceColumns coordinate h).1.2 ∧
    burnolMeanZeroOneMinusSquare (inverseCotest coordinate h).2=
      (sourceColumns coordinate h).2.1-burnolMeanZeroTruncatedFourier (sourceColumns coordinate h).2.2 := by
  constructor <;> change (burnolMeanZeroOneMinusSquare*burnolMeanZeroBlockInverse) _=_ <;>
    rw [burnolMeanZeroBlockInverse_right] <;> rfl

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
