import H0mework.Physics.LowEnergy.FullQuantum.GaugeHistory.Generator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A pairwise one-way history has an exact, globally invertible first-insertion evolution. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def insertionIntegral (B : ℝ → E →L[ℂ] E) (start time : ℝ) (initial : E) : E :=
  ∫ r in start..time, B r initial

theorem insertionIntegral_derivative (B : ℝ → E →L[ℂ] E)
    (continuousB : ∀ v, Continuous (fun t => B t v)) (start time : ℝ) (initial : E) :
    HasDerivAt (fun t => insertionIntegral B start t initial) (B time initial) time :=
  intervalIntegral.integral_hasDerivAt_right ((continuousB initial).intervalIntegrable start time)
    (continuousB initial).aestronglyMeasurable.stronglyMeasurableAtFilter (continuousB initial).continuousAt

omit [CompleteSpace E] in
theorem insertionIntegral_bound (B : ℝ → E →L[ℂ] E) (bound : ℝ → ℝ) (continuousBound : Continuous bound)
    (bounded : ∀ t v, ‖B t v‖≤bound t*‖v‖) (start time : ℝ) (initial : E) :
    ‖insertionIntegral B start time initial‖≤|∫ r in start..time, bound r| * ‖initial‖ := by
  have majorant : ∀ᵐ r ∂volume.restrict (Set.uIoc start time), ‖B r initial‖≤bound r*‖initial‖ :=
    ae_of_all _ (fun r => bounded r initial)
  have estimate := intervalIntegral.norm_integral_le_abs_of_norm_le majorant
    ((continuousBound.mul_const ‖initial‖).intervalIntegrable (μ := volume) start time)
  simpa only [insertionIntegral,intervalIntegral.integral_mul_const,abs_mul,
    abs_of_nonneg (norm_nonneg initial)] using estimate

def insertionLinear (B : ℝ → E →L[ℂ] E) (continuousB : ∀ v, Continuous (fun t => B t v))
    (start time : ℝ) : E →ₗ[ℂ] E where
  toFun := insertionIntegral B start time
  map_add' u v := by
    simp only [insertionIntegral,map_add]
    exact intervalIntegral.integral_add ((continuousB u).intervalIntegrable start time)
      ((continuousB v).intervalIntegrable start time)
  map_smul' c u := by simp only [insertionIntegral,map_smul,intervalIntegral.integral_smul,RingHom.id_apply]

def insertionOperator (B : ℝ → E →L[ℂ] E) (continuousB : ∀ v, Continuous (fun t => B t v))
    (bound : ℝ → ℝ) (continuousBound : Continuous bound) (bounded : ∀ t v, ‖B t v‖≤bound t*‖v‖)
    (start time : ℝ) : E →L[ℂ] E :=
  (insertionLinear B continuousB start time).mkContinuous |∫ r in start..time, bound r|
    (insertionIntegral_bound B bound continuousBound bounded start time)

theorem insertionIntegral_left_zero (B : ℝ → E →L[ℂ] E)
    (continuousB : ∀ v, Continuous (fun t => B t v)) (nilpotent : ∀ s t v, B s (B t v)=0)
    (s start time : ℝ) (initial : E) : B s (insertionIntegral B start time initial)=0 := by
  have exchanged := (B s).intervalIntegral_comp_comm ((continuousB initial).intervalIntegrable (μ := volume) start time)
  change (∫ r in start..time, B s (B r initial))=B s (insertionIntegral B start time initial) at exchanged
  rw [← exchanged]
  simp only [nilpotent,intervalIntegral.integral_zero]

theorem insertionIntegral_twice_zero (B : ℝ → E →L[ℂ] E)
    (continuousB : ∀ v, Continuous (fun t => B t v)) (nilpotent : ∀ s t v, B s (B t v)=0)
    (start first middle second : ℝ) (initial : E) :
    insertionIntegral B start first (insertionIntegral B middle second initial)=0 := by
  change (∫ r in start..first, B r (insertionIntegral B middle second initial))=0
  simp only [insertionIntegral_left_zero B continuousB nilpotent,intervalIntegral.integral_zero]

def triangularCurve (B : ℝ → E →L[ℂ] E) (start : ℝ) (initial : E) (time : ℝ) : E :=
  initial+insertionIntegral B start time initial

omit [CompleteSpace E] in
theorem triangularCurve_starts (B : ℝ → E →L[ℂ] E) (start : ℝ) (initial : E) :
    triangularCurve B start initial start=initial := by simp [triangularCurve,insertionIntegral]

theorem triangularCurve_equation (B : ℝ → E →L[ℂ] E)
    (continuousB : ∀ v, Continuous (fun t => B t v)) (nilpotent : ∀ s t v, B s (B t v)=0)
    (start time : ℝ) (initial : E) :
    HasDerivAt (triangularCurve B start initial) (B time (triangularCurve B start initial time)) time := by
  have derivative := (insertionIntegral_derivative B continuousB start time initial).const_add initial
  simpa only [triangularCurve,map_add,insertionIntegral_left_zero B continuousB nilpotent,add_zero] using! derivative

theorem triangularCurve_inverse (B : ℝ → E →L[ℂ] E)
    (continuousB : ∀ v, Continuous (fun t => B t v)) (nilpotent : ∀ s t v, B s (B t v)=0)
    (start time : ℝ) (initial : E) :
    triangularCurve B time (triangularCurve B start initial time) start=initial := by
  have additive := (insertionLinear B continuousB time start).map_add initial (insertionIntegral B start time initial)
  change insertionIntegral B time start (initial+insertionIntegral B start time initial)=
    insertionIntegral B time start initial+insertionIntegral B time start (insertionIntegral B start time initial) at additive
  simp only [triangularCurve,additive,insertionIntegral_twice_zero B continuousB nilpotent,add_zero]
  unfold insertionIntegral
  rw [intervalIntegral.integral_symm]
  abel

theorem triangularCurve_compose (B : ℝ → E →L[ℂ] E)
    (continuousB : ∀ v, Continuous (fun t => B t v)) (nilpotent : ∀ s t v, B s (B t v)=0)
    (start middle time : ℝ) (initial : E) :
    triangularCurve B middle (triangularCurve B start initial middle) time=
      triangularCurve B start initial time := by
  have additive := (insertionLinear B continuousB middle time).map_add initial (insertionIntegral B start middle initial)
  change insertionIntegral B middle time (initial+insertionIntegral B start middle initial)=
    insertionIntegral B middle time initial+insertionIntegral B middle time (insertionIntegral B start middle initial) at additive
  simp only [triangularCurve,additive,insertionIntegral_twice_zero B continuousB nilpotent,add_zero]
  have chained := intervalIntegral.integral_add_adjacent_intervals
    ((continuousB initial).intervalIntegrable (μ := volume) start middle) ((continuousB initial).intervalIntegrable (μ := volume) middle time)
  change insertionIntegral B start middle initial+insertionIntegral B middle time initial=
    insertionIntegral B start time initial at chained
  rw [add_assoc,chained]

omit [CompleteSpace E] in
theorem triangularCurve_norm_le (B : ℝ → E →L[ℂ] E) (bound : ℝ → ℝ) (continuousBound : Continuous bound)
    (bounded : ∀ t v, ‖B t v‖≤bound t*‖v‖) (start time : ℝ) (initial : E) :
    ‖triangularCurve B start initial time‖≤(1+|∫ r in start..time, bound r|)*‖initial‖ := by
  calc
    ‖triangularCurve B start initial time‖ ≤ ‖initial‖+‖insertionIntegral B start time initial‖ := norm_add_le _ _
    _ ≤ ‖initial‖+|∫ r in start..time, bound r| * ‖initial‖ :=
      add_le_add_right (insertionIntegral_bound B bound continuousBound bounded start time initial) _
    _ = (1+|∫ r in start..time, bound r|)*‖initial‖ := by ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
