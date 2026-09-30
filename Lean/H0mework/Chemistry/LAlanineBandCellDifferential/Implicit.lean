import H0mework.Chemistry.LAlanineBandCellDifferential.Equation
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceImplicit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandGeometry WholeBandActual TrueFlowDifferential
open scoped Topology
noncomputable section

theorem pathResidual_hasStrictFDerivAt_on_path (x : Space) (γ : Path) :
    HasStrictFDerivAt pathResidual
      ((-pathConst).coprod (1 - volterra.comp (pathCompDeriv sourceGradient (sourceGradient_contDiff 1) γ)))
      (x, γ) := by
  let M := pathCompDeriv sourceGradient (sourceGradient_contDiff 1) γ
  have gradient : HasStrictFDerivAt pathGradient M γ :=
    hasStrictFDerivAt_pathComp sourceGradient (sourceGradient_contDiff 1) γ
  have first := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (x, γ))).sub
    (pathConst.hasStrictFDerivAt.comp _ (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (x, γ))))
  have second := volterra.hasStrictFDerivAt.comp (x, γ)
    (gradient.comp (x, γ) (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (x, γ))))
  have derivative_eq : (-pathConst).coprod (1 - volterra.comp M) =
      ContinuousLinearMap.snd ℝ Space Path - pathConst.comp (.fst ℝ Space Path) -
        volterra.comp (M.comp (.snd ℝ Space Path)) := by
    apply ContinuousLinearMap.ext
    intro state
    change -pathConst state.1 + (state.2 - volterra (M state.2)) =
      state.2 - pathConst state.1 - volterra (M state.2)
    abel
  change HasStrictFDerivAt pathResidual ((-pathConst).coprod (1 - volterra.comp M)) (x, γ)
  rw [derivative_eq]
  exact first.sub second

def cell0_residualDerivative (p : Cell0Point) : Space × Path →L[ℝ] Path :=
  (-pathConst).coprod (1 - cell0_volterraHessian p)

theorem cell0_pathResidual_hasStrictFDerivAt (p : Cell0Point) :
    HasStrictFDerivAt pathResidual (cell0_residualDerivative p)
      (cellSeed 0 p.val, rawPath (cellSeed 0 p.val)) :=
  pathResidual_hasStrictFDerivAt_on_path _ _

theorem cell0_pathResidual_right_invertible (p : Cell0Point) :
    ((cell0_residualDerivative p).comp (.inr ℝ Space Path)).IsInvertible := by
  have inverse : (1 - cell0_volterraHessian p).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofUnit
      (Units.oneSub (cell0_volterraHessian p) (cell0_volterraHessian_norm_lt_one p)), rfl⟩
  simpa only [cell0_residualDerivative, ContinuousLinearMap.coprod_comp_inr] using inverse

def cell0_nearbySolution (p : Cell0Point) : Space → Path :=
  (cell0_pathResidual_hasStrictFDerivAt p).implicitFunctionOfProdDomain
    (cell0_pathResidual_right_invertible p)

theorem cell0_nearbySolution_hasStrictFDerivAt (p : Cell0Point) :
    HasStrictFDerivAt (cell0_nearbySolution p)
      (-((cell0_residualDerivative p).comp (.inr ℝ Space Path)).inverse.comp
        ((cell0_residualDerivative p).comp (.inl ℝ Space Path))) (cellSeed 0 p.val) :=
  (cell0_pathResidual_hasStrictFDerivAt p).hasStrictFDerivAt_implicitFunctionOfProdDomain
    (cell0_pathResidual_right_invertible p)

theorem cell0_rawPath_residual_zero (p : Cell0Point) :
    pathResidual (cellSeed 0 p.val, rawPath (cellSeed 0 p.val)) = 0 := by
  change rawPath (cellSeed 0 p.val) - pathConst (cellSeed 0 p.val) -
    volterra (pathGradient (rawPath (cellSeed 0 p.val))) = 0
  linear_combination cell0_rawPath_integral_equation p

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
