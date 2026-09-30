import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Sum
import Mathlib.Analysis.Normed.Module.Multilinear.Basic


set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadSum

open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter

noncomputable section
variable (kernel : IntegerWavevector → IntegerWavevector → IntegerWavevector → ℂ)
  (cap : ℝ) (bounded : ∀ a b c, ‖kernel a b c‖ ≤ cap * NativeCompleteStressCarrier.weight c)
  (wave : IntegerWavevector) (i j l : Coordinate)

include bounded

theorem inner_smul_left (scalar : ℝ) (left middle : E) (c : IntegerWavevector) :
    innerValue kernel wave i j (scalar • left) middle c = scalar • innerValue kernel wave i j left middle c := by
  simp only [innerValue, innerTerm, lp.coeFn_smul, Pi.smul_apply, smul_mul_assoc, mul_smul_comm]
  exact Summable.tsum_const_smul scalar (inner_summable kernel cap bounded wave i j left middle c)

theorem inner_smul_middle (scalar : ℝ) (left middle : E) (c : IntegerWavevector) :
    innerValue kernel wave i j left (scalar • middle) c = scalar • innerValue kernel wave i j left middle c := by
  simp only [innerValue, innerTerm, lp.coeFn_smul, Pi.smul_apply, mul_smul_comm]
  exact Summable.tsum_const_smul scalar (inner_summable kernel cap bounded wave i j left middle c)

theorem smul_left (scalar : ℝ) (left middle right : E) :
    value kernel wave i j l (scalar • left) middle right = scalar • value kernel wave i j l left middle right := by
  simp only [value, inner_smul_left kernel cap bounded, smul_mul_assoc]
  exact Summable.tsum_const_smul scalar (outer_summable kernel cap bounded wave i j l left middle right)

theorem smul_middle (scalar : ℝ) (left middle right : E) :
    value kernel wave i j l left (scalar • middle) right = scalar • value kernel wave i j l left middle right := by
  simp only [value, inner_smul_middle kernel cap bounded, smul_mul_assoc]
  exact Summable.tsum_const_smul scalar (outer_summable kernel cap bounded wave i j l left middle right)

theorem smul_right (scalar : ℝ) (left middle right : E) :
    value kernel wave i j l left middle (scalar • right) = scalar • value kernel wave i j l left middle right := by
  simp only [value, lp.coeFn_smul, Pi.smul_apply, mul_smul_comm]
  exact Summable.tsum_const_smul scalar (outer_summable kernel cap bounded wave i j l left middle right)

def multilinear : MultilinearMap ℝ (fun _ : Fin 3 => E) ℂ :=
  MultilinearMap.mk' (fun values => value kernel wave i j l (values 0) (values 1) (values 2))
    (by
      intro values index x y
      fin_cases index
      · simpa [Function.update] using add_left kernel cap bounded wave i j l x y (values 1) (values 2)
      · simpa [Function.update] using add_middle kernel cap bounded wave i j l (values 0) x y (values 2)
      · simpa [Function.update] using add_right kernel cap bounded wave i j l (values 0) (values 1) x y)
    (by
      intro values index scalar x
      fin_cases index
      · simpa [Function.update] using smul_left kernel cap bounded wave i j l scalar x (values 1) (values 2)
      · simpa [Function.update] using smul_middle kernel cap bounded wave i j l scalar (values 0) x (values 2)
      · simpa [Function.update] using smul_right kernel cap bounded wave i j l scalar (values 0) (values 1) x)

def continuousMultilinear : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℂ :=
  (multilinear kernel cap bounded wave i j l).mkContinuous (3 * cap * ‖weights‖) (fun values => by
    simpa only [Fin.prod_univ_three, multilinear, MultilinearMap.mk', MultilinearMap.coe_mk, mul_assoc] using
      norm_bound kernel cap bounded wave i j l (values 0) (values 1) (values 2))

theorem continuousMultilinear_apply (left middle right : E) :
    continuousMultilinear kernel cap bounded wave i j l ![left,middle,right] =
      value kernel wave i j l left middle right := rfl

theorem aestronglyMeasurable {f g h : ℝ → E} {μ : Measure ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ) :
    AEStronglyMeasurable (fun time => value kernel wave i j l (f time) (g time) (h time)) μ := by
  have cont : Continuous (fun values : E × (E × E) =>
      ![values.1, values.2.1, values.2.2]) := by
    apply continuous_pi
    intro coordinate
    fin_cases coordinate
    · exact continuous_fst
    · exact continuous_fst.comp continuous_snd
    · exact continuous_snd.comp continuous_snd
  have paid := ((continuousMultilinear kernel cap bounded wave i j l).cont.comp cont).comp_aestronglyMeasurable
    (hf.prodMk (hg.prodMk hh))
  simpa only [Function.comp_apply, continuousMultilinear_apply] using! paid

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadSum
