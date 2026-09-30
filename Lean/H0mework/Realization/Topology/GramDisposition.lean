import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Source-generated centered Gram disposition

Two actual nonzero states under isometric actions give normalized
autocorrelations of norm at most one.  If a paired conserved target is read
exactly by both autocorrelations, both channels are neutral.  Otherwise the
constructor retains the first exact nonzero hidden-channel coordinate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedCenteredGram

open scoped InnerProductSpace

noncomputable section

universe h

variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Centered matrix coefficient of one actual state. -/
def normalizedAutocorrelation
    (state : H) (action : H ≃ₗᵢ[ℂ] H) : ℂ :=
  inner ℂ state (action state) / (((‖state‖ ^ 2 : ℝ) : ℂ))

/-- Exact mismatch between a target amplitude and its same-state readout. -/
def centeredGramResidual
    (target : ℂ) (state : H) (action : H ≃ₗᵢ[ℂ] H) : ℂ :=
  target - normalizedAutocorrelation state action

theorem normalizedAutocorrelation_norm_le_one
    (state : H) (stateNe : state ≠ 0)
    (action : H ≃ₗᵢ[ℂ] H) :
    ‖normalizedAutocorrelation state action‖ ≤ 1 := by
  have stateNormPos : 0 < ‖state‖ := norm_pos_iff.mpr stateNe
  have stateNormSqPos : 0 < ‖state‖ ^ 2 := sq_pos_of_pos stateNormPos
  have numeratorLe :
      ‖inner ℂ state (action state)‖ ≤ ‖state‖ ^ 2 := by
    calc
      ‖inner ℂ state (action state)‖ ≤ ‖state‖ * ‖action state‖ :=
        norm_inner_le_norm _ _
      _ = ‖state‖ ^ 2 := by
        rw [LinearIsometryEquiv.norm_map]
        ring
  unfold normalizedAutocorrelation
  rw [norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_norm]
  exact (div_le_one stateNormSqPos).2 numeratorLe

theorem target_eq_autocorrelation_of_residual_eq_zero
    (target : ℂ) (state : H) (action : H ≃ₗᵢ[ℂ] H)
    (residualZero : centeredGramResidual target state action = 0) :
    target = normalizedAutocorrelation state action :=
  sub_eq_zero.mp residualZero

/-- Both target channels are actual neutral centered-Gram readouts. -/
structure BothCenteredGramRealized
    (selected reversal : ℂ)
    (selectedState reversalState : H)
    (selectedAction reversalAction : H ≃ₗᵢ[ℂ] H) : Type where
  selected_residual_zero :
    centeredGramResidual selected selectedState selectedAction = 0
  reversal_residual_zero :
    centeredGramResidual reversal reversalState reversalAction = 0
  selected_norm_one : ‖selected‖ = 1
  reversal_norm_one : ‖reversal‖ = 1
  target_norms_eq : ‖selected‖ = ‖reversal‖

inductive CenteredGramResidualChannel where
  | selected
  | reversal
  deriving DecidableEq

def centeredGramResidualAt
    (selectedResidual reversalResidual : ℂ) :
    CenteredGramResidualChannel → ℂ
  | .selected => selectedResidual
  | .reversal => reversalResidual

/-- Labelled nonzero hidden-channel coordinate. -/
structure ExplicitCenteredGramResidualCoordinate
    (selectedResidual reversalResidual : ℂ) : Type where
  channel : CenteredGramResidualChannel
  coordinate : ℂ
  coordinate_eq :
    coordinate = centeredGramResidualAt
      selectedResidual reversalResidual channel
  coordinate_ne_zero : coordinate ≠ 0

inductive CenteredGramDisposition
    (selected reversal : ℂ)
    (selectedState reversalState : H)
    (selectedAction reversalAction : H ≃ₗᵢ[ℂ] H) : Type where
  | realized :
      BothCenteredGramRealized selected reversal selectedState reversalState
        selectedAction reversalAction →
      CenteredGramDisposition selected reversal selectedState reversalState
        selectedAction reversalAction
  | residual :
      ExplicitCenteredGramResidualCoordinate
        (centeredGramResidual selected selectedState selectedAction)
        (centeredGramResidual reversal reversalState reversalAction) →
      CenteredGramDisposition selected reversal selectedState reversalState
        selectedAction reversalAction

theorem target_norms_eq_one_of_residuals_zero
    (selected reversal : ℂ)
    (selectedState reversalState : H)
    (selectedStateNe : selectedState ≠ 0)
    (reversalStateNe : reversalState ≠ 0)
    (selectedAction reversalAction : H ≃ₗᵢ[ℂ] H)
    (selectedResidualZero :
      centeredGramResidual selected selectedState selectedAction = 0)
    (reversalResidualZero :
      centeredGramResidual reversal reversalState reversalAction = 0)
    (pairedConservation : selected * star reversal = 1) :
    ‖selected‖ = 1 ∧ ‖reversal‖ = 1 := by
  have selectedEq := target_eq_autocorrelation_of_residual_eq_zero
    selected selectedState selectedAction selectedResidualZero
  have reversalEq := target_eq_autocorrelation_of_residual_eq_zero
    reversal reversalState reversalAction reversalResidualZero
  have selectedLe : ‖selected‖ ≤ 1 := by
    rw [selectedEq]
    exact normalizedAutocorrelation_norm_le_one
      selectedState selectedStateNe selectedAction
  have reversalLe : ‖reversal‖ ≤ 1 := by
    rw [reversalEq]
    exact normalizedAutocorrelation_norm_le_one
      reversalState reversalStateNe reversalAction
  have productNormOne : ‖selected‖ * ‖reversal‖ = 1 := by
    have conservedNorm := congrArg norm pairedConservation
    simpa only [norm_mul, norm_star, norm_one] using conservedNorm
  constructor <;> nlinarith [norm_nonneg selected, norm_nonneg reversal]

/-- Total neutral-or-hidden-channel disposition. -/
def settleCenteredGram
    (selected reversal : ℂ)
    (selectedState reversalState : H)
    (selectedStateNe : selectedState ≠ 0)
    (reversalStateNe : reversalState ≠ 0)
    (selectedAction reversalAction : H ≃ₗᵢ[ℂ] H)
    (pairedConservation : selected * star reversal = 1) :
    CenteredGramDisposition selected reversal selectedState reversalState
      selectedAction reversalAction := by
  by_cases selectedResidualZero :
      centeredGramResidual selected selectedState selectedAction = 0
  · by_cases reversalResidualZero :
        centeredGramResidual reversal reversalState reversalAction = 0
    · have norms := target_norms_eq_one_of_residuals_zero
        selected reversal selectedState reversalState
        selectedStateNe reversalStateNe selectedAction reversalAction
        selectedResidualZero reversalResidualZero pairedConservation
      exact .realized {
        selected_residual_zero := selectedResidualZero
        reversal_residual_zero := reversalResidualZero
        selected_norm_one := norms.1
        reversal_norm_one := norms.2
        target_norms_eq := norms.1.trans norms.2.symm
      }
    · exact .residual {
        channel := .reversal
        coordinate := centeredGramResidual reversal reversalState reversalAction
        coordinate_eq := rfl
        coordinate_ne_zero := reversalResidualZero
      }
  · exact .residual {
      channel := .selected
      coordinate := centeredGramResidual selected selectedState selectedAction
      coordinate_eq := rfl
      coordinate_ne_zero := selectedResidualZero
    }

def settleCenteredGram_sameAction
    (selected reversal : ℂ)
    (selectedState reversalState : H)
    (selectedStateNe : selectedState ≠ 0)
    (reversalStateNe : reversalState ≠ 0)
    (action : H ≃ₗᵢ[ℂ] H)
    (pairedConservation : selected * star reversal = 1) :
    CenteredGramDisposition selected reversal selectedState reversalState
      action action :=
  settleCenteredGram selected reversal selectedState reversalState
    selectedStateNe reversalStateNe action action pairedConservation

end

end SourceGeneratedCenteredGram
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
