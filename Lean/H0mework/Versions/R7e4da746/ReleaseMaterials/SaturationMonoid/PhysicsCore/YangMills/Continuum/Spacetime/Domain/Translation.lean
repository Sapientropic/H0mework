import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Terminal.Recognition.Fields
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal

namespace SaturationMonoid.PhysicsCore.YangMills.Spacetime.Domain.Translation
open Terminal
noncomputable section

abbrev L1 := Lp ℂ 1 (volume : Measure Terminal.Spacetime)
def translated (f : Test) (t : ℝ) : L1 := (translateTest (timeLine t) f).toLp 1 volume

theorem translated_ae (f : Test) (t : ℝ) :
    translated f t =ᵐ[volume] fun p => f (p + timeLine t) :=
  ((translateTest (timeLine t) f).coeFn_toLp 1 volume).trans
    (Eventually.of_forall (fun p => translateTest_apply (timeLine t) p f))

theorem translated_zero (f : Test) : translated f 0 = f.toLp 1 volume := by
  apply Lp.ext
  filter_upwards [translated_ae f 0, f.coeFn_toLp 1 volume] with p ht hf
  simp only [timeLine.map_zero, add_zero] at ht
  exact ht.trans hf.symm

private def shift : C(ℝ, C(Terminal.Spacetime, Terminal.Spacetime)) :=
  (⟨fun p : ℝ × Terminal.Spacetime => p.2 + timeLine p.1,
    continuous_snd.add (timeLine.toContinuousLinearMap.continuous.comp continuous_fst)⟩ :
      C(ℝ × Terminal.Spacetime, Terminal.Spacetime)).curry
private theorem shift_preserving (t : ℝ) : MeasurePreserving (shift t) volume volume :=
  measurePreserving_add_right volume (timeLine t)

theorem translated_continuous (f : Test) : Continuous (translated f) := by
  have same (t : ℝ) : translated f t =
      Lp.compMeasurePreserving (shift t) (shift_preserving t) (f.toLp 1 volume) := by
    change ((translateTest (timeLine t) f).memLp 1 volume).toLp _ =
      ((f.memLp 1 volume).comp_measurePreserving (shift_preserving t)).toLp _
    exact MemLp.toLp_congr _ _ (Eventually.of_forall (fun p => translateTest_apply _ _ _))
  have generated := (continuous_const (y := f.toLp 1 volume)).compMeasurePreservingLp
    shift.continuous shift_preserving (by simp)
  simpa only [← same] using generated

theorem pointwise_derivative (f : Test) (p : Terminal.Spacetime) (t : ℝ) :
    HasDerivAt (fun s => f (p + timeLine s)) (testDerivative 0 f (p + timeLine t)) t := by
  have line : HasDerivAt (fun s => p + timeLine s) (axis 0) t := by
    convert! (timeLine.toContinuousLinearMap.hasDerivAt.const_add p) using 1
    ext i
    simp [timeLine, axis, StageNineHolonomicField.coordinateDirection, EuclideanSpace.single]
  exact (f.hasFDerivAt _).comp_hasDerivAt t line

theorem pointwise_integral (f : Test) (a b : ℝ) (p : Terminal.Spacetime) :
    ∫ t in a..b, testDerivative 0 f (p + timeLine t) = f (p + timeLine b) - f (p + timeLine a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => pointwise_derivative f p t)
    (((testDerivative 0 f).continuous.comp
      ((continuous_const (y := p)).add timeLine.toContinuousLinearMap.continuous)).intervalIntegrable a b)

theorem product_integrable (f : Test) (a b : ℝ) :
    Integrable (fun p : ℝ × Terminal.Spacetime => f (p.2 + timeLine p.1))
      ((volume.restrict (Set.uIoc a b)).prod volume) := by
  let : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) := ⟨by simp⟩
  have measurable : AEStronglyMeasurable
      (fun p : ℝ × Terminal.Spacetime => f (p.2 + timeLine p.1))
      ((volume.restrict (Set.uIoc a b)).prod volume) :=
    (f.continuous.comp
      (continuous_snd.add (timeLine.toContinuousLinearMap.continuous.comp continuous_fst))).aestronglyMeasurable
  apply (integrable_prod_iff measurable).mpr
  refine ⟨Eventually.of_forall (fun t => ?_), ?_⟩
  · exact (memLp_one_iff_integrable.mp ((f.memLp 1 volume).comp_measurePreserving (shift_preserving t)))
  · have same : (fun t : ℝ => ∫ p : Terminal.Spacetime, ‖f (p + timeLine t)‖) =
        fun _ => ∫ p : Terminal.Spacetime, ‖f p‖ :=
      funext (fun t => integral_add_right_eq_self (fun p => ‖f p‖) (timeLine t))
    rw [same]
    exact integrable_const _

end
end SaturationMonoid.PhysicsCore.YangMills.Spacetime.Domain.Translation
