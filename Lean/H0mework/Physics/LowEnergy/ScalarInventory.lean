import H0mework.Physics.Matter.SU7ExteriorMatterAnomalyRunning
import H0mework.Physics.Matter.SU7ExteriorBreakingYukawa

/-! Subordinate scalar-inventory readout of the existing exterior representation.
The factory counts degree-four basis fibers, not a supplied multiplet table.
The beta table consumes the Stage-7 left-Weyl convention plus ONE complex
Lambda-four scalar. It is not a quantum-loop derivation or a threshold match. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.LowEnergy.ScalarInventory

open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorMatterAnomalyRunning SU7ExteriorBreakingYukawa
open OneLoopGaugeTraceCore

noncomputable section

def multiplicity (label : ResidualExteriorIrrepLabel) : ℕ :=
  exteriorBranchComponentCount 4 label / label.componentDimension

theorem component_factorization : ∀ label : ResidualExteriorIrrepLabel,
    exteriorBranchComponentCount 4 label = multiplicity label * label.componentDimension := by
  decide

/-- Normal form, downstream of the actual basis-fiber count. -/
def readout : ResidualExteriorIrrepLabel → ℕ
  | ⟨.singlet, .singlet, .negative⟩ => 1
  | ⟨.singlet, .singlet, .neutral⟩ => 1
  | ⟨.singlet, .singlet, .positive⟩ => 1
  | ⟨.singlet, .doublet, .negative⟩ => 0
  | ⟨.singlet, .doublet, .neutral⟩ => 1
  | ⟨.singlet, .doublet, .positive⟩ => 0
  | ⟨.fundamental, .singlet, .negative⟩ => 1
  | ⟨.fundamental, .singlet, .neutral⟩ => 0
  | ⟨.fundamental, .singlet, .positive⟩ => 1
  | ⟨.fundamental, .doublet, .negative⟩ => 0
  | ⟨.fundamental, .doublet, .neutral⟩ => 1
  | ⟨.fundamental, .doublet, .positive⟩ => 0
  | ⟨.antifundamental, .singlet, .negative⟩ => 0
  | ⟨.antifundamental, .singlet, .neutral⟩ => 2
  | ⟨.antifundamental, .singlet, .positive⟩ => 0
  | ⟨.antifundamental, .doublet, .negative⟩ => 1
  | ⟨.antifundamental, .doublet, .neutral⟩ => 0
  | ⟨.antifundamental, .doublet, .positive⟩ => 1

theorem multiplicity_eq_readout (label : ResidualExteriorIrrepLabel) :
    multiplicity label = readout label := by
  rcases label with ⟨color, weak, charge⟩
  cases color <;> cases weak <;> cases charge <;> decide

theorem component_total :
    (∑ label : ResidualExteriorIrrepLabel, multiplicity label * label.componentDimension) = 35 := by
  decide

theorem actual_scalar_dimension : Module.finrank ℂ ExteriorBreakingScalarCarrier = 35 :=
  exteriorBreakingScalarCarrier_finrank

def irrepTrace (trace : ResidualExteriorIrrepLabel → ℚ) : ℚ :=
  residualColorSum fun color => residualWeakSum fun weak =>
    residualHyperchargeSum fun charge =>
      let label : ResidualExteriorIrrepLabel := ⟨color, weak, charge⟩
      (multiplicity label : ℚ) * trace label

def colorTrace : ℚ := irrepTrace fun l => residualColorDynkinIndex l.color * l.weak.dimension
def weakTrace : ℚ := irrepTrace fun l => residualWeakDynkinIndex l.weak * l.color.dimension
def chargeTrace : ℚ := irrepTrace fun l => l.componentDimension * residualExteriorCharge l ^ 2

theorem residual_traces : colorTrace = 5 ∧ weakTrace = 5 ∧ chargeTrace = 20 := by
  norm_num [colorTrace, weakTrace, chargeTrace, irrepTrace, residualColorSum,
    residualWeakSum, residualHyperchargeSum, multiplicity_eq_readout, readout,
    residualColorDynkinIndex, residualWeakDynkinIndex, residualExteriorCharge,
    ResidualColorType.dimension, ResidualWeakType.dimension,
    ResidualExteriorIrrepLabel.componentDimension, ResidualHypercharge.toInt]

def motherTrace : ℚ := su7ExteriorDynkinIndex 4

theorem mother_trace : motherTrace = 5 := by
  norm_num [motherTrace, su7ExteriorDynkinIndex, Nat.choose]

def scalarTrace : ExteriorMatterGaugeFactor → ℚ
  | .motherSU7 => motherTrace
  | .colorSU3 => colorTrace
  | .weakSU2 => weakTrace
  | .p286HyperchargeU1 => chargeTrace

def input (factor : ExteriorMatterGaugeFactor) : GaugeTraceOneLoopInput where
  adjointCasimir := exteriorMatterAdjointCasimir factor
  weylDynkinTrace := exteriorMatterWeylDynkinTrace factor
  scalarDynkinTrace := scalarTrace factor

def b0 (factor : ExteriorMatterGaugeFactor) : ℚ := (input factor).asymptoticB0

theorem b0_table : b0 .motherSU7 = 56 / 3 ∧ b0 .colorSU3 = 4 ∧
    b0 .weakSU2 = 1 / 3 ∧ b0 .p286HyperchargeU1 = -28 := by
  norm_num [b0, input, GaugeTraceOneLoopInput.asymptoticB0,
    exteriorMatterAdjointCasimir, exteriorMatterWeylDynkinTrace, scalarTrace,
    mother_trace, residual_traces, exteriorSpinor_motherSU7WeylDynkinTrace,
    exteriorSpinor_residualWeylDynkinTraces]

theorem correction (factor : ExteriorMatterGaugeFactor) :
    b0 factor = exteriorMatterAsymptoticB0 factor - scalarTrace factor / 3 := by
  simp only [b0, input, exteriorMatterAsymptoticB0, exteriorMatterOneLoopInput,
    GaugeTraceOneLoopInput.asymptoticB0, exteriorMatterScalarDynkinTrace_zero]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.ScalarInventory
