import H0mework.NavierStokes.MaterialAction.PauliControl
import H0mework.Versions.X.NavierStokes.PhysicalReadout.CanonicalCoframe

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativePauliMotherAction

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair StageNineHolonomicField
open StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7MotherGaugeConnection
open SU7ExteriorMatterGaugeCovariantJet
open NativePauliControl

noncomputable section

def lowerCoefficients (block : Block) : DiracSpinorIndex → Fin 2 → ℂ :=
  !![0, 0; 0, 0; block 0 0, block 0 1; block 1 0, block 1 1]

private def lowerLinear : Block →ₗ[ℂ] (DiracSpinorIndex → Fin 2 → ℂ) where
  toFun := lowerCoefficients
  map_add' := by
    intro first second
    funext spin color
    change lowerCoefficients (first + second) spin color =
      lowerCoefficients first spin color + lowerCoefficients second spin color
    fin_cases spin <;> fin_cases color <;> simp [lowerCoefficients]
  map_smul' := by
    intro scalar block
    funext spin color
    change lowerCoefficients (scalar • block) spin color = scalar * lowerCoefficients block spin color
    fin_cases spin <;> fin_cases color <;> simp [lowerCoefficients]

def lowerMatter : Block →ₗ[ℂ] DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm.toLinearMap.comp (sourceColorMatterCoordinateLinear.comp lowerLinear)

theorem lowerMatter_apply (block : Block) :
    lowerMatter block = sourceColorDiracMatter (lowerCoefficients block) := by
  change matterCoordinateEquiv.symm (matterCoordinateEquiv _) = _
  rw [matterCoordinateEquiv.symm_apply_apply]
  rfl

def generatorScale : Fin 3 → ℝ := ![2, -2, 2]
def generator (direction : Fin 3) : P286LieBlockData :=
  generatorScale direction • sourceColorP286Generator direction

def colorAction (block : Block) (direction : Fin 3) : Block :=
  fun row column => ∑ middle : Fin 2, block row middle * (Complex.I * pauli direction middle column)

/-- Normalization of the existing source generators is proved on the whole exterior-matter carrier. -/
theorem generator_action (block : Block) (direction : Fin 3) :
    diracExteriorMotherLieAction (p286LieBlockEmbed (generator direction)) (lowerMatter block) =
      lowerMatter (colorAction block direction) := by
  rw [generator, p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul,
    LinearMap.smul_apply, lowerMatter_apply, sourceColorDiracMatter_generator, lowerMatter_apply]
  rw [← sourceColorDiracMatter_smul]
  apply congrArg sourceColorDiracMatter
  funext spin color
  fin_cases direction <;> fin_cases spin <;> fin_cases color <;>
    simp [generatorScale, lowerCoefficients, colorAction, sourceColorPauli, pauli,
      Fin.sum_univ_two] <;> ring

def spinActionMatrix : Fin 4 → DiracMatrix :=
  ![1, -(diracGamma 0 * diracGamma 1), -(diracGamma 0 * diracGamma 2), -(diracGamma 0 * diracGamma 3)]

def spinAction (block : Block) (direction : Fin 4) : Block :=
  fun row column => ∑ middle : Fin 2, spinPrincipal direction row middle * block middle column

theorem spin_action (block : Block) (direction : Fin 4) :
    diracMatrixMatterAction (spinActionMatrix direction) (lowerMatter block) =
      lowerMatter (spinAction block direction) := by
  rw [lowerMatter_apply, sourceColorDiracMatter_matrix, lowerMatter_apply]
  apply congrArg sourceColorDiracMatter
  funext spin color
  fin_cases direction <;> fin_cases spin <;> fin_cases color <;>
    simp [lowerCoefficients, spinActionMatrix, spinAction, spinPrincipal, pauli,
      diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four, Fin.sum_univ_two]

private def motherActionLinear (matter : DiracExteriorMatterCarrier) : P286LieBlockData →ₗ[ℝ] DiracExteriorMatterCarrier where
  toFun data := diracExteriorMotherLieAction (p286LieBlockEmbed data) matter
  map_add' := by
    intro first second
    rw [p286LieBlockEmbed_add, diracExteriorMotherLieAction_add, LinearMap.add_apply]
  map_smul' := by
    intro scalar data
    rw [p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul, LinearMap.smul_apply]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) scalar _).symm

def gaugePotential (control : Fin 4 → Fin 3 → ℝ) (spacetime : Fin 4) : P286LieBlockData :=
  ∑ color, control spacetime color • generator color

theorem gaugePotential_vacuum_zero (control : Fin 4 → Fin 3 → ℝ) (spacetime : Fin 4) :
    scalarMotherLieAction (p286LieBlockEmbed (gaugePotential control spacetime))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  simp [gaugePotential, generator, Fin.sum_univ_three, p286LieBlockEmbed_add,
    p286LieBlockEmbed_real_smul, scalarMotherLieAction_add, scalarMotherLieAction_real_smul,
    sourceColorP286Generator_vacuum_zero]

theorem gaugePotential_action (block : Block) (control : Fin 4 → Fin 3 → ℝ) (spacetime : Fin 4) :
    diracExteriorMotherLieAction (p286LieBlockEmbed (gaugePotential control spacetime)) (lowerMatter block) =
      ∑ color, (control spacetime color : ℂ) • lowerMatter (colorAction block color) := by
  change motherActionLinear (lowerMatter block) (gaugePotential control spacetime) = _
  rw [gaugePotential, map_sum]
  apply Finset.sum_congr rfl
  intro color _
  rw [map_smul]
  change control spacetime color •
    diracExteriorMotherLieAction (p286LieBlockEmbed (generator color)) (lowerMatter block) = _
  rw [generator_action]
  rfl

def wholeAction (velocity : Vector) (control : Fin 4 → Fin 3 → ℝ) : DiracExteriorMatterCarrier :=
  ∑ spacetime, diracMatrixMatterAction (spinActionMatrix spacetime)
    (diracExteriorMotherLieAction (p286LieBlockEmbed (gaugePotential control spacetime))
      (lowerMatter (hermitianBlock velocity)))

/-- All twelve original mother-action directions assemble the same complete matrix response. -/
theorem wholeAction_eq (velocity : Vector) (control : Fin 4 → Fin 3 → ℝ) :
    wholeAction velocity control = lowerMatter (action velocity control) := by
  simp only [wholeAction, gaugePotential_action, map_sum, map_smul, spin_action]
  simp only [← map_smul, ← map_sum]
  congr 1
  ext row column
  simp only [action, spinAction, colorAction, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem controlled_wholeAction (velocity : Vector) (target : Block) :
    wholeAction velocity (control velocity target) =
      lowerMatter target - (phaseResidual velocity target : ℂ) • lowerMatter 1 := by
  rw [wholeAction_eq, control_action, map_sub, map_smul]

end
end SaturationMonoid.NavierStokes.NativePauliMotherAction
