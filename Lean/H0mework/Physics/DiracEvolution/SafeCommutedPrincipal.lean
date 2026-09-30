import H0mework.Physics.DiracEvolution.MatterCoordinateFirstOrderCommutator
import H0mework.Physics.DiracEvolution.SafeWeakEnergyRate

/-!
# Fixed P506/L0 commuted matter principal

The same Hermitian coefficient used by the source-owned Cauchy-safe energy
law acts continuously on the canonical finite matter coordinates.  Its
spatial derivative exposes the exact action-coefficient changed-read needed
by the commuted-energy estimate; no solution, residual, or target is an input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineDiracMatterCoordinateCalculus
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open StageNineHolonomicField
open StageNineMatterCoordinateFirstOrderCommutator

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-- The actual finite Dirac-matrix action, as a real continuous-linear
operator on the canonical matter coordinate carrier. -/
def diracMatrixMatterCoordinateCLMLinear :
    DiracMatrix →ₗ[ℝ] MatterRealEnd where
  toFun matrix :=
    ⟨diracMatrixMatterCoordinateRealBilinear matrix,
      (diracMatrixMatterCoordinateRealBilinear matrix
        ).continuous_of_finiteDimensional⟩
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro coordinates
    exact LinearMap.congr_fun
      (diracMatrixMatterCoordinateRealBilinear.map_add first second)
      coordinates
  map_smul' parameter matrix := by
    apply ContinuousLinearMap.ext
    intro coordinates
    exact LinearMap.congr_fun
      (diracMatrixMatterCoordinateRealBilinear.map_smul parameter matrix)
      coordinates

def diracMatrixMatterCoordinateCLM :
    DiracMatrix →L[ℝ] MatterRealEnd :=
  ⟨diracMatrixMatterCoordinateCLMLinear,
    diracMatrixMatterCoordinateCLMLinear.continuous_of_finiteDimensional⟩

@[simp] theorem diracMatrixMatterCoordinateCLM_apply
    (matrix : DiracMatrix)
    (coordinates : MatterCoordinateCarrier) :
    diracMatrixMatterCoordinateCLM matrix coordinates =
      matterCoordinateEquiv
        (diracMatrixMatterAction matrix
          (matterCoordinateEquiv.symm coordinates)) :=
  rfl

/-- The source-owned Hermitian principal coefficient of the fixed Cauchy-safe
matter action, acting directly on finite real coordinates. -/
def fixedEvolutionPrincipalCoordinateCLM
    (direction : LorentzianIndex)
    (point : BasePoint) : MatterRealEnd :=
  diracMatrixMatterCoordinateCLM
    (fixedEvolutionPrincipal direction point)

theorem fixedEvolutionPrincipalCoordinateCLM_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ 1 (fixedEvolutionPrincipalCoordinateCLM direction) := by
  have matrixSmooth : ContDiff ℝ ∞
      (fixedEvolutionPrincipal direction) := by
    apply contDiff_pi'
    intro row
    apply contDiff_pi'
    intro column
    exact fixedEvolutionPrincipal_entry_contDiff direction row column
  exact (diracMatrixMatterCoordinateCLM.contDiff.comp matrixSmooth).of_le
    (by norm_num)

/-- Fixed source-owned principal changed-read.  This is the exact coefficient
commutator that enters a spatially commuted energy law. -/
theorem fixedEvolutionPrincipalCoordinateSum_directionalDerivative
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ 2 field)
    (point : BasePoint)
    (commutedDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => ∑ direction : LorentzianIndex,
          fixedEvolutionPrincipalCoordinateCLM direction candidate
            (fieldDirectionalDerivative field candidate direction))
        point commutedDirection =
      (∑ direction : LorentzianIndex,
        fixedEvolutionPrincipalCoordinateCLM direction point
          (fieldDirectionalDerivative
            (fun candidate =>
              fieldDirectionalDerivative field candidate commutedDirection)
            point direction)) +
        ∑ direction : LorentzianIndex,
          (fieldDirectionalDerivative
              (fixedEvolutionPrincipalCoordinateCLM direction) point
              commutedDirection)
            (fieldDirectionalDerivative field point direction) := by
  exact matterCoordinatePrincipalSum_directionalDerivative
    fixedEvolutionPrincipalCoordinateCLM field
    fixedEvolutionPrincipalCoordinateCLM_contDiff fieldSmooth point
    commutedDirection

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
