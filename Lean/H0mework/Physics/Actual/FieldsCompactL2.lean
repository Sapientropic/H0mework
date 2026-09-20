import H0mework.Physics.Actual.FieldsRegularity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Every spacetime scale and every primitive coordinate share one real
Hilbert carrier. The compact read retains the complete four-dimensional field. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fields

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open MeasureTheory Set Metric

noncomputable section

def unitCompact : Set BasePoint := closedBall 0 1

def compactMeasure : Measure BasePoint := volume.restrict unitCompact

instance compactMeasure_finite : IsFiniteMeasure compactMeasure where
  measure_univ_lt_top := by
    simpa [compactMeasure, unitCompact] using
      (isCompact_closedBall (0 : BasePoint) 1).measure_lt_top (μ := volume)

instance compactMeasure_separable : MeasureTheory.IsSeparable compactMeasure :=
  MeasureTheory.isSeparable_of_sigmaFinite _

abbrev CompactL2 := Lp ℝ 2 compactMeasure

local instance two_ne_top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

instance compactL2_secondCountable : SecondCountableTopology CompactL2 :=
  MeasureTheory.Lp.SecondCountableTopology

def scaleRadius (scale : ℕ) : ℝ := (scale : ℝ) + 1

theorem scaleRadius_pos (scale : ℕ) : 0 < scaleRadius scale := by
  unfold scaleRadius
  positivity

def compactPullback (configuration : StageNineHolonomicConfiguration)
    (scale : ℕ) (coordinate : Coordinate) (point : BasePoint) : ℝ :=
  realCoordinate configuration coordinate (scaleRadius scale • point)

theorem compactPullback_continuous
    {configuration : StageNineHolonomicConfiguration}
    (smooth : configuration.Smooth) (scale : ℕ) (coordinate : Coordinate) :
    Continuous (compactPullback configuration scale coordinate) :=
  (realCoordinate_continuous smooth coordinate).comp
    (continuous_id.const_smul (scaleRadius scale))

theorem compactPullback_memLp
    {configuration : StageNineHolonomicConfiguration}
    (smooth : configuration.Smooth) (scale : ℕ) (coordinate : Coordinate) :
    MemLp (compactPullback configuration scale coordinate) 2 compactMeasure := by
  have continuous := compactPullback_continuous smooth scale coordinate
  obtain ⟨bound, bounded⟩ := (isCompact_closedBall (0 : BasePoint) 1
    ).exists_bound_of_continuousOn continuous.continuousOn
  apply MemLp.of_bound continuous.aestronglyMeasurable bound
  filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet :
    MeasurableSet unitCompact)] with point pointMem
  exact bounded point pointMem

def compactRead (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (scale : ℕ) (coordinate : Coordinate) : CompactL2 :=
  (compactPullback_memLp smooth scale coordinate).toLp
    (compactPullback configuration scale coordinate)

theorem compactRead_coe_ae (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (scale : ℕ) (coordinate : Coordinate) :
    compactRead configuration smooth scale coordinate =ᵐ[compactMeasure]
      compactPullback configuration scale coordinate :=
  (compactPullback_memLp smooth scale coordinate).coeFn_toLp

end
end SaturationMonoid.PhysicsCore.Stage9CU.Fields
