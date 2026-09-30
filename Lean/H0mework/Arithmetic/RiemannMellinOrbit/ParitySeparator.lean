import H0mework.Arithmetic.Mellin.TateFiniteJump
import H0mework.Arithmetic.RiemannInverseFibre.QRichSeparator

/-!
# Clozel parity cross and the q-rich separator

The centered parameters on the selected/reversal branches are
`λ = s - 1/2` and `λᵣ = -conj λ`.  An unnormalized J-even/J-odd
change of coordinates exposes cross coefficient
`λ - λᵣ = s - (1 - conj s)`.  This module identifies that coefficient
with the existing branch-normalized full-row C separator.

It proves an identity only; no Fourier relation, separator-zero, fixedness,
or critical-line equation is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace QRich

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open InverseZeroFibre
open scoped ComplexConjugate

noncomputable section

abbrev ClozelJPair := ℂ × ℂ

def clozelCenteredParameter (s : ℂ) : ℂ :=
  s - 1 / 2

def clozelReversedCenteredParameter (s : ℂ) : ℂ :=
  coordinateReversal s - 1 / 2

theorem clozelReversedCenteredParameter_eq_neg_conj (s : ℂ) :
    clozelReversedCenteredParameter s =
      -conj (clozelCenteredParameter s) := by
  change (1 - conj s) - 1 / 2 = -conj (s - 1 / 2)
  rw [map_sub]
  have halfConj : conj (1 / 2 : ℂ) = 1 / 2 := by
    simp [map_ofNat]
  rw [halfConj]
  ring

/-- Synthesis and analysis use the integral Hadamard matrix; neither map
contains the inverse scalar `1/2`. -/
def clozelJParitySynthesis : ClozelJPair →ₗ[ℂ] ClozelJPair where
  toFun value := (value.1 + value.2, value.1 - value.2)
  map_add' left right := by
    ext <;> simp <;> ring
  map_smul' scalar value := by
    ext <;> simp <;> ring

def clozelJParityAnalysis : ClozelJPair →ₗ[ℂ] ClozelJPair :=
  clozelJParitySynthesis

theorem clozelJParityAnalysis_comp_synthesis :
    clozelJParityAnalysis.comp clozelJParitySynthesis =
      (2 : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro value
  ext <;> simp [clozelJParityAnalysis, clozelJParitySynthesis] <;> ring

def clozelCenteredParameterDiagonal (s : ℂ) :
    ClozelJPair →ₗ[ℂ] ClozelJPair where
  toFun value :=
    (clozelCenteredParameter s * value.1,
      clozelReversedCenteredParameter s * value.2)
  map_add' left right := by
    ext <;> simp <;> ring
  map_smul' scalar value := by
    ext <;> simp <;> ring

def clozelJCrossCoefficient (s : ℂ) : ℂ :=
  clozelCenteredParameter s - clozelReversedCenteredParameter s

def clozelJDiagonalCoefficient (s : ℂ) : ℂ :=
  clozelCenteredParameter s + clozelReversedCenteredParameter s

theorem clozelJParity_cross_matrix (s : ℂ) (value : ClozelJPair) :
    clozelJParityAnalysis
        (clozelCenteredParameterDiagonal s
          (clozelJParitySynthesis value)) =
      (clozelJDiagonalCoefficient s * value.1 +
          clozelJCrossCoefficient s * value.2,
        clozelJCrossCoefficient s * value.1 +
          clozelJDiagonalCoefficient s * value.2) := by
  ext <;>
    simp [clozelJParityAnalysis, clozelJParitySynthesis,
      clozelCenteredParameterDiagonal, clozelJDiagonalCoefficient,
      clozelJCrossCoefficient] <;>
    ring

theorem clozelJCrossCoefficient_eq_lambda_add_conj (s : ℂ) :
    clozelJCrossCoefficient s =
      clozelCenteredParameter s + conj (clozelCenteredParameter s) := by
  rw [clozelJCrossCoefficient,
    clozelReversedCenteredParameter_eq_neg_conj]
  ring

theorem clozelJCrossCoefficient_eq_coordinateResidual (s : ℂ) :
    clozelJCrossCoefficient s = s - coordinateReversal s := by
  rw [clozelJCrossCoefficient_eq_lambda_add_conj]
  unfold clozelCenteredParameter coordinateReversal
  rw [map_sub]
  have halfConj : conj (1 / 2 : ℂ) = 1 / 2 := by
    simp [map_ofNat]
  rw [halfConj]
  ring

/-- Direct C splice on the existing Mathlib regression component. -/
theorem mathlibLeft_branchNormalizedSeparator_eq_clozelCross
    (observation : GeneratedRiemannZeroObservation)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    branchNormalizedQRichSeparator
        (mathlibLeftRegressionComponent observation) stage row =
      -(quotientCoefficient row : ℂ) *
        clozelJCrossCoefficient observation.coordinate := by
  rw [branchNormalizedQRichSeparator_eq,
    mathlibLeftRegressionComponent_partnerResidual]
  unfold mathlibReversalPartner
  rw [clozelJCrossCoefficient_eq_coordinateResidual]

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
