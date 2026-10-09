import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Uniqueness

/-! Pairwise one-way interactions generate an exact globally forced solution by two genuine integrals. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
open GaugeHistory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def inputPrimitive (source : ℝ → E) (start : ℝ) (initial : E) (time : ℝ) : E :=
  initial+∫ r in start..time, source r

theorem inputPrimitive_derivative (source : ℝ → E) (continuousSource : Continuous source)
    (start time : ℝ) (initial : E) :
    HasDerivAt (inputPrimitive source start initial) (source time) time :=
  (intervalIntegral.integral_hasDerivAt_right (continuousSource.intervalIntegrable start time)
    continuousSource.aestronglyMeasurable.stronglyMeasurableAtFilter continuousSource.continuousAt).const_add initial

theorem inputPrimitive_continuous (source : ℝ → E) (continuousSource : Continuous source)
    (start : ℝ) (initial : E) : Continuous (inputPrimitive source start initial) :=
  continuous_iff_continuousAt.mpr (fun t => (inputPrimitive_derivative source continuousSource start t initial).continuousAt)

def forcedCurve (B : ℝ → E →L[ℂ] E) (source : ℝ → E) (start : ℝ) (initial : E) (time : ℝ) : E :=
  inputPrimitive source start initial time+∫ r in start..time, B r (inputPrimitive source start initial r)

theorem forcedIntegrand_continuous (B : ℝ → E →L[ℂ] E)
    (continuousB : Continuous (fun tv : ℝ × E => B tv.1 tv.2))
    (source : ℝ → E) (continuousSource : Continuous source) (start : ℝ) (initial : E) :
    Continuous (fun t => B t (inputPrimitive source start initial t)) :=
  continuousB.comp (continuous_id.prodMk (inputPrimitive_continuous source continuousSource start initial))

theorem forcedCurve_image (B : ℝ → E →L[ℂ] E)
    (continuousB : Continuous (fun tv : ℝ × E => B tv.1 tv.2))
    (nilpotent : ∀ s t v, B s (B t v)=0)
    (source : ℝ → E) (continuousSource : Continuous source)
    (start time s : ℝ) (initial : E) :
    B s (forcedCurve B source start initial time)=B s (inputPrimitive source start initial time) := by
  have pull := (B s).intervalIntegral_comp_comm
    ((forcedIntegrand_continuous B continuousB source continuousSource start initial).intervalIntegrable (μ := volume) start time)
  rw [forcedCurve,map_add,← pull]
  simp only [nilpotent,intervalIntegral.integral_zero,add_zero]

theorem forcedCurve_equation (B : ℝ → E →L[ℂ] E)
    (continuousB : Continuous (fun tv : ℝ × E => B tv.1 tv.2))
    (nilpotent : ∀ s t v, B s (B t v)=0)
    (source : ℝ → E) (continuousSource : Continuous source)
    (start time : ℝ) (initial : E) :
    HasDerivAt (forcedCurve B source start initial)
      (B time (forcedCurve B source start initial time)+source time) time := by
  have continuousIntegrand := forcedIntegrand_continuous B continuousB source continuousSource start initial
  have integral := intervalIntegral.integral_hasDerivAt_right
    (continuousIntegrand.intervalIntegrable (μ := volume) start time)
    continuousIntegrand.aestronglyMeasurable.stronglyMeasurableAtFilter continuousIntegrand.continuousAt
  have generated := (inputPrimitive_derivative source continuousSource start time initial).add integral
  rw [forcedCurve_image B continuousB nilpotent source continuousSource]
  simpa only [forcedCurve,add_comm] using! generated

omit [CompleteSpace E] in
theorem forcedCurve_starts (B : ℝ → E →L[ℂ] E) (source : ℝ → E) (start : ℝ) (initial : E) :
    forcedCurve B source start initial start=initial := by simp [forcedCurve,inputPrimitive]

theorem forcedCurve_unique (B : ℝ → E →L[ℂ] E)
    (continuousB : Continuous (fun tv : ℝ × E => B tv.1 tv.2))
    (nilpotent : ∀ s t v, B s (B t v)=0)
    (source : ℝ → E) (continuousSource : Continuous source)
    (start : ℝ) (initial : E) (curve : ℝ → E) (starts : curve start=initial)
    (evolves : ∀ t, HasDerivAt curve (B t (curve t)+source t) t) :
    curve=forcedCurve B source start initial := by
  have continuousFixed (v : E) : Continuous (fun t => B t v) :=
    continuousB.comp (continuous_id.prodMk continuous_const)
  have difference (t : ℝ) : HasDerivAt (fun r => curve r-forcedCurve B source start initial r)
      (B t (curve t-forcedCurve B source start initial t)) t := by
    have generated := (evolves t).sub (forcedCurve_equation B continuousB nilpotent source continuousSource start t initial)
    simpa only [map_sub,add_sub_add_right_eq_sub] using! generated
  have determined := triangularCurve_unique B continuousFixed nilpotent start 0
    (fun t => curve t-forcedCurve B source start initial t)
    (by rw [starts,forcedCurve_starts,sub_self]) difference
  funext t
  have same := congrFun determined t
  simpa only [triangularCurve,insertionIntegral,map_zero,intervalIntegral.integral_zero,add_zero,sub_eq_zero] using same

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
