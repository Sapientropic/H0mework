import H0mework.NavierStokes.SourceGeometry.VectorWorkPointwise
import H0mework.NavierStokes.Fourier.UnitCellDivergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicUnitCellDivergence

noncomputable section

theorem physicalUnitCell_transport_abs_le
    (u omega : PhysicalSpace → PhysicalSpace)
    (hu : Continuous u) (homega : ContDiff ℝ 1 omega)
    (U : ℝ) (uBound : ∀ x, ‖u x‖ ≤ U) :
    |∫ x in physicalUnitCell, inner ℝ (u x) (fderiv ℝ omega x (omega x))| ≤
      U * (Real.sqrt (∫ x in physicalUnitCell, ‖omega x‖ ^ 2) *
        Real.sqrt (∫ x in physicalUnitCell, gradientDissipation omega x)) := by
  let f : PhysicalSpace → ℝ := fun x => ‖omega x‖
  let g : PhysicalSpace → ℝ := fun x => Real.sqrt (gradientDissipation omega x)
  let mu := volume.restrict physicalUnitCell
  have df : Continuous (fderiv ℝ omega) := homega.continuous_fderiv (by norm_num)
  have cg0 : Continuous (fun x => gradientDissipation omega x) := by
    unfold gradientDissipation
    fun_prop
  have cf : Continuous f := homega.continuous.norm
  have cg : Continuous g := Real.continuous_sqrt.comp cg0
  have if2 : Integrable (fun x => f x ^ 2) mu :=
    (cf.pow 2).continuousOn.integrableOn_compact physicalUnitCell_isCompact
  have ig2 : Integrable (fun x => g x ^ 2) mu :=
    (cg.pow 2).continuousOn.integrableOn_compact physicalUnitCell_isCompact
  have mf : MemLp f (ENNReal.ofReal (2 : ℝ)) mu := by
    simpa using (memLp_two_iff_integrable_sq cf.aestronglyMeasurable).mpr if2
  have mg : MemLp g (ENNReal.ofReal (2 : ℝ)) mu := by
    simpa using (memLp_two_iff_integrable_sq cg.aestronglyMeasurable).mpr ig2
  have cauchy := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two (μ := mu) (f := f) (g := g)
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _) mf mg
  have cauchySqrt : (∫ x in physicalUnitCell, f x * g x) ≤
      Real.sqrt (∫ x in physicalUnitCell, f x ^ 2) *
        Real.sqrt (∫ x in physicalUnitCell, g x ^ 2) := by
    change (∫ x, f x * g x ∂mu) ≤ _
    norm_num [Real.sqrt_eq_rpow] at cauchy ⊢
    exact cauchy
  have cwork : Continuous (fun x => inner ℝ (u x) (fderiv ℝ omega x (omega x))) :=
    hu.inner (df.clm_apply homega.continuous)
  have iwork : IntegrableOn
      (fun x => |inner ℝ (u x) (fderiv ℝ omega x (omega x))|) physicalUnitCell :=
    cwork.abs.continuousOn.integrableOn_compact physicalUnitCell_isCompact
  have iprod : IntegrableOn (fun x => U * (f x * g x)) physicalUnitCell :=
    ((cf.mul cg).const_mul U).continuousOn.integrableOn_compact physicalUnitCell_isCompact
  have integralBound :
      (∫ x in physicalUnitCell, |inner ℝ (u x) (fderiv ℝ omega x (omega x))|) ≤
        ∫ x in physicalUnitCell, U * (f x * g x) :=
    setIntegral_mono_on iwork iprod physicalUnitCell_isCompact.measurableSet
      (fun x _ => source_transport_pointwise u omega U uBound x)
  have U0 : 0 ≤ U := (norm_nonneg _).trans (uBound 0)
  have gIntegral : (∫ x in physicalUnitCell, g x ^ 2) =
      ∫ x in physicalUnitCell, gradientDissipation omega x := by
    apply setIntegral_congr_fun physicalUnitCell_isCompact.measurableSet
    intro x _
    dsimp only [g]
    rw [Real.sq_sqrt]
    unfold gradientDissipation
    positivity
  calc
    |∫ x in physicalUnitCell, inner ℝ (u x) (fderiv ℝ omega x (omega x))| ≤
        ∫ x in physicalUnitCell, |inner ℝ (u x) (fderiv ℝ omega x (omega x))| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x in physicalUnitCell, U * (f x * g x) := integralBound
    _ = U * ∫ x in physicalUnitCell, f x * g x := integral_const_mul _ _
    _ ≤ U * (Real.sqrt (∫ x in physicalUnitCell, f x ^ 2) *
        Real.sqrt (∫ x in physicalUnitCell, g x ^ 2)) :=
      mul_le_mul_of_nonneg_left cauchySqrt U0
    _ = _ := by rw [gIntegral]

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
