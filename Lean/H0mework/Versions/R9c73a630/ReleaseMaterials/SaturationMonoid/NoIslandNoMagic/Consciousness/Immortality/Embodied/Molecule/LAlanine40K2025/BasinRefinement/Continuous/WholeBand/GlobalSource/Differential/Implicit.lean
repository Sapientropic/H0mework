import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Recognition
import Mathlib.Analysis.Calculus.Implicit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource.Differential
open SourceGaussianModel Filter
open _root_.LAlanineTrueFlowDifferential
open scoped Topology
noncomputable section

def residual (p : Space × Path) : Path := p.2-pathConst p.1-volterra (fieldOnPath p.2)
def residualDerivative (x : Point) : Space × Path →L[ℝ] Path :=
  (-pathConst).coprod (1-volterra.comp (derivativeOnPath x))

theorem residual_strictDerivative (x : Point) :
    HasStrictFDerivAt residual (residualDerivative x) (x,actualPath x) := by
  have gradient := hasStrictFDerivAt_pathComp field field_contDiff (actualPath x)
  have first := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (x,actualPath x))).sub
    (pathConst.hasStrictFDerivAt.comp _ (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (x,actualPath x))))
  have second := volterra.hasStrictFDerivAt.comp (x,actualPath x)
    (gradient.comp (x,actualPath x) (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (x,actualPath x))))
  have equal : residualDerivative x = ContinuousLinearMap.snd ℝ Space Path -
      pathConst.comp (.fst ℝ Space Path) - volterra.comp ((derivativeOnPath x).comp (.snd ℝ Space Path)) := by
    apply ContinuousLinearMap.ext
    intro p
    change -pathConst p.1 + (p.2-volterra (derivativeOnPath x p.2)) =
      p.2-pathConst p.1-volterra (derivativeOnPath x p.2)
    abel
  rw [equal]
  exact first.sub second

theorem residual_right_invertible (x : Point) :
    ((residualDerivative x).comp (.inr ℝ Space Path)).IsInvertible := by
  have bound : ‖volterra.comp (derivativeOnPath x)‖ < 1 :=
    (norm_volterra_comp_le _ (derivativeOnPath_bound x)).trans_lt (by norm_num)
  have inverse : (1-volterra.comp (derivativeOnPath x)).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofUnit (Units.oneSub (volterra.comp (derivativeOnPath x)) bound),rfl⟩
  simpa only [residualDerivative,ContinuousLinearMap.coprod_comp_inr] using inverse

def nearby (x : Point) : Space → Path :=
  (residual_strictDerivative x).implicitFunctionOfProdDomain (residual_right_invertible x)

theorem residual_zero (x : Point) : residual (x,actualPath x) = 0 := by
  change actualPath x-pathConst x-volterra (fieldOnPath (actualPath x)) = 0
  linear_combination path_integral_equation x

theorem nearby_actual (x : Point) : nearby x =ᶠ[𝓝 x] actualPath := by
  filter_upwards [(residual_strictDerivative x).eventually_apply_implicitFunctionOfProdDomain
    (residual_right_invertible x)] with y solved
  rw [residual_zero] at solved
  apply solvedPath_eq_actual
  change nearby x y-pathConst y-volterra (fieldOnPath (nearby x y)) = 0 at solved
  linear_combination solved

def response (x : Point) : Space →L[ℝ] Path :=
  (1-volterra.comp (derivativeOnPath x)).inverse.comp pathConst

theorem actualPath_strictDerivative (x : Point) : HasStrictFDerivAt actualPath (response x) x := by
  have generated : HasStrictFDerivAt (nearby x) (response x) x := by
    simpa only [nearby,response,residualDerivative,ContinuousLinearMap.coprod_comp_inr,
      ContinuousLinearMap.coprod_comp_inl,ContinuousLinearMap.comp_neg,neg_neg] using
      (residual_strictDerivative x).hasStrictFDerivAt_implicitFunctionOfProdDomain (residual_right_invertible x)
  exact generated.congr_of_eventuallyEq (nearby_actual x)

end
end LAlanine40K2025.BasinRefinement.GlobalSource.Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
