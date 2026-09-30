import H0mework.Versions.X.NavierStokes.CartanAction.Stress

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativePauliPairing

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open Stage9C.Material.SpinPair Stage9CU.Fluid
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativeCartanClifford

noncomputable section

def blockPair (first second : Block) : ℂ :=
  ∑ row : Fin 2, ∑ column : Fin 2, star (first row column) * second row column

theorem dual_gamma_block (velocity : PhysicalSpace) (direction : Fin 4) (block : Block) :
    NativeCanonicalFluidCoframe.dual velocity
      (diracMatrixMatterAction (diracGamma direction) (lowerMatter block)) =
        blockPair (hermitianBlock (normalizedVelocity velocity)) (spinAction block direction) := by
  rw [NativeCanonicalFluidCoframe.dual, InitialLift.dual, lowerMatter_apply]
  change (∑ spin, ∑ color, InitialLift.dualCoefficients (fun index => velocity index) spin color *
    sourceColorDoubletDual color
      (diracMatrixMatterAction (diracGamma direction) (sourceColorDiracMatter (lowerCoefficients block)) spin)) = _
  simp only [sourceColorDoubletDual_diracMatrix]
  fin_cases direction <;>
    simp [InitialLift.dualCoefficients, lowerCoefficients, blockPair, hermitianBlock, spinAction,
      spinPrincipal, normalizedVelocity, pauli, diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
      map_ofNat] <;> ring

theorem kinetic_block (velocity : PhysicalSpace) (direction : Fin 4) (block : Block) :
    (NativeCanonicalFluidCoframe.dual velocity
      (Complex.I • diracMatrixMatterAction (diracGamma direction) (lowerMatter block))).re =
        -(blockPair (hermitianBlock (normalizedVelocity velocity)) (spinAction block direction)).im := by
  rw [map_smul, dual_gamma_block]
  simp [smul_eq_mul, Complex.mul_re]

theorem triple_block (velocity : PhysicalSpace) (direction : Fin 4) (pair : Fin 6) :
    NativeCartanSpinSupport.tripleCurrent velocity direction
      (lorentzBivectorFirst pair) (lorentzBivectorSecond pair) =
        -(blockPair (hermitianBlock (normalizedVelocity velocity))
          (spinAction (blockAction (bivectorBlock pair) (hermitianBlock (normalizedVelocity velocity))) direction)).im := by
  rw [NativeCartanSpinSupport.tripleCurrent, source_matter,
    SU7ExteriorBreakingYukawa.diracMatrixMatterAction_mul, LinearMap.comp_apply, bivector_action,
    kinetic_block]

end
end SaturationMonoid.NavierStokes.NativePauliPairing
