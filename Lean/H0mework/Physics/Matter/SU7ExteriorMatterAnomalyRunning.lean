import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.Matter.SU7ExteriorMatterRestriction
import H0mework.Physics.Gauge.OneLoopGaugeTraceCore

/-!
# Anomaly and one-loop readouts of the actual SU(7) exterior matter

Every finite sum in this module consumes the branching multiplicity computed
from the actual exterior-basis fibers in `SU7ExteriorMatterRestriction`.
There is no P458/P508/P523 import and no anomaly or running Boolean in the
matter representation.

The selected matter carrier contains left-handed Weyl fermions only.  No
Stage-7 scalar representation has been generated, so the scalar carrier is
explicitly `Fin 0` and its trace is proved zero.  Consequently the resulting
`b₀` values describe this exotic 63-component matter checkpoint in primitive
P286 charge normalization; they are not Standard-Model running receipts and
do not manufacture an empirical coupling boundary.
-/

namespace SaturationMonoid.PhysicsCore.SU7ExteriorMatterAnomalyRunning

open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open OneLoopGaugeTraceCore

noncomputable section

/-- Cubic SU(3) anomaly index with `A(3)=1`. -/
def residualColorCubicAnomalyIndex : ResidualColorType → ℚ
  | .singlet => 0
  | .fundamental => 1
  | .antifundamental => -1

/-- Quadratic SU(3) index with `T(3)=T(3̅)=1/2`. -/
def residualColorDynkinIndex : ResidualColorType → ℚ
  | .singlet => 0
  | .fundamental => 1 / 2
  | .antifundamental => 1 / 2

/-- Quadratic SU(2) index with `T(2)=1/2`. -/
def residualWeakDynkinIndex : ResidualWeakType → ℚ
  | .singlet => 0
  | .doublet => 1 / 2

def residualExteriorCharge
    (label : ResidualExteriorIrrepLabel) : ℚ :=
  label.hypercharge.toInt

def residualHyperchargeSum (value : ResidualHypercharge → ℚ) : ℚ :=
  value .negative + value .neutral + value .positive

def residualWeakSum (value : ResidualWeakType → ℚ) : ℚ :=
  value .singlet + value .doublet

def residualColorSum (value : ResidualColorType → ℚ) : ℚ :=
  value .singlet + value .fundamental + value .antifundamental

/-- Explicit finite sum over all `3 × 2 × 3` residual irrep labels. -/
def exteriorSpinorIrrepTrace
    (trace : ResidualExteriorIrrepLabel → ℚ) : ℚ :=
  residualColorSum fun color =>
    residualWeakSum fun weak =>
      residualHyperchargeSum fun hypercharge =>
        let label : ResidualExteriorIrrepLabel :=
          ⟨color, weak, hypercharge⟩
        (exteriorSpinorBranchingMultiplicity label : ℚ) * trace label

/-! ## Perturbative and global anomaly traces -/

def colorCubicAnomalyTrace : ℚ :=
  exteriorSpinorIrrepTrace fun label =>
    residualColorCubicAnomalyIndex label.color * label.weak.dimension

def colorColorHyperchargeAnomalyTrace : ℚ :=
  exteriorSpinorIrrepTrace fun label =>
    residualColorDynkinIndex label.color * label.weak.dimension *
      residualExteriorCharge label

def weakWeakHyperchargeAnomalyTrace : ℚ :=
  exteriorSpinorIrrepTrace fun label =>
    residualWeakDynkinIndex label.weak * label.color.dimension *
      residualExteriorCharge label

def gravitationalHyperchargeAnomalyTrace : ℚ :=
  exteriorSpinorIrrepTrace fun label =>
    label.componentDimension * residualExteriorCharge label

def cubicHyperchargeAnomalyTrace : ℚ :=
  exteriorSpinorIrrepTrace fun label =>
    label.componentDimension * residualExteriorCharge label ^ 3

theorem exteriorSpinor_residualAnomalyTraces_cancel :
    colorCubicAnomalyTrace = 0 ∧
      colorColorHyperchargeAnomalyTrace = 0 ∧
      weakWeakHyperchargeAnomalyTrace = 0 ∧
      gravitationalHyperchargeAnomalyTrace = 0 ∧
      cubicHyperchargeAnomalyTrace = 0 := by
  norm_num [colorCubicAnomalyTrace,
    colorColorHyperchargeAnomalyTrace,
    weakWeakHyperchargeAnomalyTrace,
    gravitationalHyperchargeAnomalyTrace,
    cubicHyperchargeAnomalyTrace, exteriorSpinorIrrepTrace,
    residualColorSum, residualWeakSum, residualHyperchargeSum,
    exteriorSpinorBranchingMultiplicity_eq_readout,
    exteriorSpinorBranchingReadout,
    residualColorCubicAnomalyIndex, residualColorDynkinIndex,
    residualWeakDynkinIndex, residualExteriorCharge,
    ResidualColorType.dimension, ResidualWeakType.dimension,
    ResidualExteriorIrrepLabel.componentDimension,
    ResidualHypercharge.toInt]

/-- Number of residual SU(2) doublets, including color multiplicity. -/
def weakDoubletCount : ℕ :=
  ∑ label : ResidualExteriorIrrepLabel,
    exteriorSpinorBranchingMultiplicity label *
      match label.weak with
      | .singlet => 0
      | .doublet => label.color.dimension

theorem exteriorSpinor_weakDoubletCount :
    weakDoubletCount = 16 := by
  decide

/-- The SU(2) Witten parity obstruction vanishes because the number of
doublets is even. -/
theorem exteriorSpinor_wittenParity_even :
    weakDoubletCount % 2 = 0 := by
  decide

/-- The full SU(7) cubic index is the degree-derived exterior index already
selected before restriction; it cancels for degrees `(6,2,4)`. -/
theorem exteriorSpinor_fullSU7CubicAnomalyIndex_cancel :
    exteriorSpinorCandidateAnomalyIndex = 0 :=
  exteriorSpinorCandidateAnomalyIndex_eq_zero

/-- Final Stage-7 name for the degree-derived full-SU(7) anomaly index. -/
abbrev exteriorSpinorFullSU7CubicAnomalyIndex :=
  exteriorSpinorCandidateAnomalyIndex

/-! ## Actual matter traces -/

def colorWeylDynkinTrace : ℚ :=
  exteriorSpinorIrrepTrace fun label =>
    residualColorDynkinIndex label.color * label.weak.dimension

def weakWeylDynkinTrace : ℚ :=
  exteriorSpinorIrrepTrace fun label =>
    residualWeakDynkinIndex label.weak * label.color.dimension

/-- U(1) trace in the primitive P286 normalization
`diag(0₃,0₂,+1,-1)`. -/
def p286HyperchargeSquareWeylTrace : ℚ :=
  exteriorSpinorIrrepTrace fun label =>
    label.componentDimension * residualExteriorCharge label ^ 2

theorem exteriorSpinor_residualWeylDynkinTraces :
    colorWeylDynkinTrace = 8 ∧
      weakWeylDynkinTrace = 8 ∧
      p286HyperchargeSquareWeylTrace = 32 := by
  norm_num [colorWeylDynkinTrace, weakWeylDynkinTrace,
    p286HyperchargeSquareWeylTrace, exteriorSpinorIrrepTrace,
    residualColorSum, residualWeakSum, residualHyperchargeSum,
    exteriorSpinorBranchingMultiplicity_eq_readout,
    exteriorSpinorBranchingReadout, residualColorDynkinIndex,
    residualWeakDynkinIndex, residualExteriorCharge,
    ResidualColorType.dimension, ResidualWeakType.dimension,
    ResidualExteriorIrrepLabel.componentDimension,
    ResidualHypercharge.toInt]

/-- Standard exterior-power SU(7) Dynkin-index formula in the normalization
`T(7)=1/2`, specialized to rank seven. -/
def su7ExteriorDynkinIndex (degree : ℕ) : ℚ :=
  (Nat.choose 5 (degree - 1) : ℚ) / 2

def motherSU7WeylDynkinTrace : ℚ :=
  ∑ degreeIndex : Fin 3,
    su7ExteriorDynkinIndex (exteriorSpinorDegree degreeIndex)

theorem exteriorSpinor_motherSU7WeylDynkinTrace :
    motherSU7WeylDynkinTrace = 8 := by
  norm_num [motherSU7WeylDynkinTrace, su7ExteriorDynkinIndex,
    exteriorSpinorDegree, Fin.sum_univ_three, Nat.choose]

/-! ## One-loop coefficient readout -/

inductive ExteriorMatterGaugeFactor where
  | motherSU7
  | colorSU3
  | weakSU2
  | p286HyperchargeU1
  deriving DecidableEq, Repr, FintypeViaProxy

def exteriorMatterAdjointCasimir : ExteriorMatterGaugeFactor → ℚ
  | .motherSU7 => 7
  | .colorSU3 => 3
  | .weakSU2 => 2
  | .p286HyperchargeU1 => 0

def exteriorMatterWeylDynkinTrace : ExteriorMatterGaugeFactor → ℚ
  | .motherSU7 => motherSU7WeylDynkinTrace
  | .colorSU3 => colorWeylDynkinTrace
  | .weakSU2 => weakWeylDynkinTrace
  | .p286HyperchargeU1 => p286HyperchargeSquareWeylTrace

/-- No scalar representation has been produced at this Stage-7 checkpoint. -/
abbrev ExteriorMatterScalarCarrier := Fin 0

def exteriorMatterScalarDynkinTrace
    (_factor : ExteriorMatterGaugeFactor) : ℚ :=
  ∑ _scalar : ExteriorMatterScalarCarrier, (0 : ℚ)

theorem exteriorMatterScalarDynkinTrace_zero
    (factor : ExteriorMatterGaugeFactor) :
    exteriorMatterScalarDynkinTrace factor = 0 := by
  simp [exteriorMatterScalarDynkinTrace]

def exteriorMatterOneLoopInput
    (factor : ExteriorMatterGaugeFactor) : GaugeTraceOneLoopInput where
  adjointCasimir := exteriorMatterAdjointCasimir factor
  weylDynkinTrace := exteriorMatterWeylDynkinTrace factor
  scalarDynkinTrace := exteriorMatterScalarDynkinTrace factor

def exteriorMatterAsymptoticB0
    (factor : ExteriorMatterGaugeFactor) : ℚ :=
  (exteriorMatterOneLoopInput factor).asymptoticB0

def exteriorMatterStandardBetaCoefficient
    (factor : ExteriorMatterGaugeFactor) : ℚ :=
  (exteriorMatterOneLoopInput factor).standardBetaCoefficient

theorem exteriorMatterAsymptoticB0_table :
    exteriorMatterAsymptoticB0 .motherSU7 = 61 / 3 ∧
      exteriorMatterAsymptoticB0 .colorSU3 = 17 / 3 ∧
      exteriorMatterAsymptoticB0 .weakSU2 = 2 ∧
      exteriorMatterAsymptoticB0 .p286HyperchargeU1 = -(64 / 3) := by
  norm_num [exteriorMatterAsymptoticB0, exteriorMatterOneLoopInput,
    exteriorMatterAdjointCasimir, exteriorMatterWeylDynkinTrace,
    exteriorMatterScalarDynkinTrace,
    GaugeTraceOneLoopInput.asymptoticB0,
    exteriorSpinor_motherSU7WeylDynkinTrace,
    exteriorSpinor_residualWeylDynkinTraces]

theorem exteriorMatterStandardBetaCoefficient_table :
    exteriorMatterStandardBetaCoefficient .motherSU7 = -(61 / 3) ∧
      exteriorMatterStandardBetaCoefficient .colorSU3 = -(17 / 3) ∧
      exteriorMatterStandardBetaCoefficient .weakSU2 = -2 ∧
      exteriorMatterStandardBetaCoefficient .p286HyperchargeU1 = 64 / 3 := by
  rcases exteriorMatterAsymptoticB0_table with
    ⟨hmother, hcolor, hweak, hu1⟩
  change
    -exteriorMatterAsymptoticB0 .motherSU7 = -(61 / 3) ∧
      -exteriorMatterAsymptoticB0 .colorSU3 = -(17 / 3) ∧
      -exteriorMatterAsymptoticB0 .weakSU2 = -2 ∧
      -exteriorMatterAsymptoticB0 .p286HyperchargeU1 = 64 / 3
  rw [hmother, hcolor, hweak, hu1]
  norm_num

/-! ## Bundled computation receipt, not a physical-admission credential -/

/-- Proof-only Stage-7 receipt.  It records what the actual representation and
restriction compute; it carries no source admission, empirical coupling,
P523 running receipt, or stored anomaly/chirality Boolean. -/
structure SU7ExteriorMatterStageSevenComputationReceipt where
  carrier_dimension :
    Module.finrank ℂ SU7ExteriorSpinorMatterCarrier = 63
  restricted_hypercharge_character :
    ∀ (z : Circle) (degree : ℕ) (index : ExteriorBasisIndex degree),
      p286RestrictedExteriorRepresentation degree (p286HyperchargeElement z)
          (su7ExteriorBasis degree index) =
        ((z ^ exteriorHyperchargeWeight index : Circle) : ℂ) •
          su7ExteriorBasis degree index
  weight_multiplicities :
    exteriorSpinorHyperchargeMultiplicity (-1) = 16 ∧
      exteriorSpinorHyperchargeMultiplicity 0 = 31 ∧
      exteriorSpinorHyperchargeMultiplicity 1 = 16
  branch_component_factorization :
    ∀ label : ResidualExteriorIrrepLabel,
      exteriorSpinorBranchComponentCount label =
        exteriorSpinorBranchingMultiplicity label *
          label.componentDimension
  residual_chirality :
    exteriorSpinorNetChirality
        ⟨.fundamental, .singlet, .negative⟩ = 2
  full_su7_cubic_anomaly :
    exteriorSpinorFullSU7CubicAnomalyIndex = 0
  residual_anomaly_traces :
    colorCubicAnomalyTrace = 0 ∧
      colorColorHyperchargeAnomalyTrace = 0 ∧
      weakWeakHyperchargeAnomalyTrace = 0 ∧
      gravitationalHyperchargeAnomalyTrace = 0 ∧
      cubicHyperchargeAnomalyTrace = 0
  witten_parity : weakDoubletCount = 16 ∧ weakDoubletCount % 2 = 0
  residual_dynkin_traces :
    colorWeylDynkinTrace = 8 ∧
      weakWeylDynkinTrace = 8 ∧
      p286HyperchargeSquareWeylTrace = 32
  empty_scalar_trace :
    ∀ factor : ExteriorMatterGaugeFactor,
      exteriorMatterScalarDynkinTrace factor = 0
  asymptotic_b0 :
    exteriorMatterAsymptoticB0 .motherSU7 = 61 / 3 ∧
      exteriorMatterAsymptoticB0 .colorSU3 = 17 / 3 ∧
      exteriorMatterAsymptoticB0 .weakSU2 = 2 ∧
      exteriorMatterAsymptoticB0 .p286HyperchargeU1 = -(64 / 3)
  canonical_seventeen_mismatch :
    (∑ label : ResidualExteriorIrrepLabel,
      exteriorSpinorBranchingMultiplicity label *
        label.componentDimension) ≠ 17

theorem su7ExteriorMatterStageSevenComputationReceipt :
    SU7ExteriorMatterStageSevenComputationReceipt where
  carrier_dimension := su7ExteriorSpinorMatterCarrier_finrank
  restricted_hypercharge_character :=
    p286RestrictedHypercharge_exterior_basis_weight
  weight_multiplicities := exteriorSpinorHyperchargeMultiplicity_table
  branch_component_factorization :=
    exteriorSpinorBranchComponentCount_factorizes
  residual_chirality := exteriorSpinor_actualResidualChirality.1
  full_su7_cubic_anomaly :=
    exteriorSpinor_fullSU7CubicAnomalyIndex_cancel
  residual_anomaly_traces := exteriorSpinor_residualAnomalyTraces_cancel
  witten_parity :=
    ⟨exteriorSpinor_weakDoubletCount, exteriorSpinor_wittenParity_even⟩
  residual_dynkin_traces := exteriorSpinor_residualWeylDynkinTraces
  empty_scalar_trace := exteriorMatterScalarDynkinTrace_zero
  asymptotic_b0 := exteriorMatterAsymptoticB0_table
  canonical_seventeen_mismatch :=
    exteriorSpinorBranching_component_total_ne_seventeen

end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterAnomalyRunning
