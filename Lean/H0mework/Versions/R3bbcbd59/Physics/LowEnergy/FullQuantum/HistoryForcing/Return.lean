import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.IntegralOperator

/-! The inverse of the same one-way flow returns the forced solution to its genuine source integral. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
open GaugeHistory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (B : ℝ → E →L[ℂ] E) (continuousB : ∀ v, Continuous (fun t => B t v))
    (jointB : Continuous (fun tv : ℝ × E => B tv.1 tv.2))
    (nilpotent : ∀ s t v, B s (B t v)=0)
    (bound : ℝ → ℝ) (continuousBound : Continuous bound) (bounded : ∀ t v, ‖B t v‖≤bound t*‖v‖)
    (source : ℝ → E) (continuousSource : Continuous source)

include continuousB jointB nilpotent bound continuousBound bounded continuousSource in
theorem forced_return_derivative (start time : ℝ) (initial : E) :
    HasDerivAt (fun t => triangularCurve B t (forcedCurve B source start initial t) start)
      (triangularCurve B time (source time) start) time := by
  let A := insertionOperator B continuousB bound continuousBound bounded start
  let curve := forcedCurve B source start initial
  have continuousA : Continuous A := insertionOperator_continuous B continuousB bound continuousBound bounded start
  have jointA : Continuous (fun tv : ℝ × E => A tv.1 tv.2) :=
    (continuousA.comp continuous_fst).clm_apply continuous_snd
  have curveDerivative := forcedCurve_equation B jointB nilpotent source continuousSource start time initial
  have fixed : HasDerivAt (fun t => A t (curve time)) (B time (curve time)) time :=
    insertionIntegral_derivative B continuousB start time (curve time)
  have product := strong_operator_product A jointA curve _ _ time fixed curveDerivative
  have killed : A time (B time (curve time))=0 := by
    change (∫ r in start..time, B r (B time (curve time)))=0
    simp only [nilpotent,intervalIntegral.integral_zero]
  rw [map_add,killed,zero_add] at product
  have generated := curveDerivative.sub product
  have reversed (t : ℝ) (v : E) : triangularCurve B t v start=v-A t v := by
    change v+(∫ r in t..start, B r v)=v-(∫ r in start..t, B r v)
    rw [intervalIntegral.integral_symm]
    simp only [sub_eq_add_neg]
  simp only [reversed]
  convert! generated using 1
  module

include continuousB jointB nilpotent bound continuousBound bounded continuousSource in
theorem forced_return_integral (start time : ℝ) (initial : E) :
    triangularCurve B time (forcedCurve B source start initial time) start=
      initial+∫ r in start..time, triangularCurve B r (source r) start := by
  let A := insertionOperator B continuousB bound continuousBound bounded start
  have continuousA : Continuous A := insertionOperator_continuous B continuousB bound continuousBound bounded start
  have reversed (t : ℝ) : triangularCurve B t (source t) start=source t-A t (source t) := by
    change source t+(∫ r in t..start, B r (source t))=source t-(∫ r in start..t, B r (source t))
    rw [intervalIntegral.integral_symm]
    simp only [sub_eq_add_neg]
  have continuousInput : Continuous (fun t => triangularCurve B t (source t) start) := by
    simpa only [reversed] using! continuousSource.sub (continuousA.clm_apply continuousSource)
  have integrated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => forced_return_derivative B continuousB jointB nilpotent bound continuousBound bounded source continuousSource start t initial)
    (continuousInput.intervalIntegrable (μ := volume) start time)
  rw [forcedCurve_starts,triangularCurve_starts] at integrated
  exact (eq_add_of_sub_eq integrated.symm).trans (add_comm _ _)

include continuousB jointB nilpotent bound continuousBound bounded continuousSource in
theorem forcedCurve_retarded (start time : ℝ) (initial : E) :
    forcedCurve B source start initial time=
      triangularCurve B start initial time+∫ r in start..time, triangularCurve B r (source r) time := by
  let A := insertionOperator B continuousB bound continuousBound bounded start
  let T : E →L[ℂ] E := 1+A time
  have T_apply (v : E) : T v=triangularCurve B start v time := rfl
  have generated := congrArg T
    (forced_return_integral B continuousB jointB nilpotent bound continuousBound bounded source continuousSource start time initial)
  rw [T_apply,triangularCurve_inverse B continuousB nilpotent time start,map_add,T_apply] at generated
  have reversed (t : ℝ) : triangularCurve B t (source t) start=source t-A t (source t) := by
    change source t+(∫ r in t..start, B r (source t))=source t-(∫ r in start..t, B r (source t))
    rw [intervalIntegral.integral_symm]
    simp only [sub_eq_add_neg]
  have continuousInput : Continuous (fun t => triangularCurve B t (source t) start) := by
    simpa only [reversed] using! continuousSource.sub
      ((insertionOperator_continuous B continuousB bound continuousBound bounded start).clm_apply continuousSource)
  have pull := T.intervalIntegral_comp_comm (continuousInput.intervalIntegrable (μ := volume) start time)
  rw [← pull] at generated
  simp only [T_apply,triangularCurve_compose B continuousB nilpotent] at generated
  exact generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
