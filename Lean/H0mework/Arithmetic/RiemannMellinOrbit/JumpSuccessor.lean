import H0mework.Arithmetic.Mellin.TateFiniteJump
import H0mework.Arithmetic.RiemannInverseFibre.QRichSeparator
/-!
# Clozel jump on the q-rich successor edge

The finite Clozel jump at index `stage + 2` cancels the actual q-rich source
scale on one complex edge.  This gives a legitimate relative-edge
transporter after complexification.  It does not construct an integral
global descent: making every transition unscaled forces the cumulative
coefficient `2 / (stage + 2)!`, already `1 / 3` at stage one.
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
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open InverseZeroFibre
noncomputable section
theorem blockQRichSuccessorScale_eq_stage_add_three (stage : Nat) :
    blockQRichSuccessorScale stage = stage + 3 := by
  unfold blockQRichSuccessorScale
  have historyEquality :
      StageHistory seedOccurrence.root stage =
        CanonicalUnitArithmeticFactorizationOccurrence.runtimeWholeHistory stage := by
    cases stage <;> rfl
  rw [historyEquality,
    CanonicalUnitArithmeticFactorizationOccurrence.runtimeWholeHistory_cardinalShadow]

/-- Exact cancellation on one complexified successor edge. -/
theorem actualClozelWeightedJump_qRich_edge
    (owner : GlobalGermOwner) (s : ℂ) (stage : Nat) :
    (blockQRichSuccessorScale stage : ℂ) *
        actualClozelWeightedJump owner s (stage + 2) = 1 := by
  have edge := actualClozel_scaledJump_eq_one owner s (stage + 2)
  rw [generatedRiemannThetaShell_magnitude] at edge
  rw [blockQRichSuccessorScale_eq_stage_add_three]
  convert edge using 1

/-- The existing branch-normalized separator retains exactly the q-rich
source scale on every lifted row. -/
theorem branchNormalizedQRichSeparator_successor
    {observation : GeneratedRiemannZeroObservation}
    (fibre : InverseZeroFibre observation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    branchNormalizedQRichSeparator fibre (stage + 1)
        (liftFactorRow seedOccurrence.root stage row) =
      (blockQRichSuccessorScale stage : ℂ) *
        branchNormalizedQRichSeparator fibre stage row := by
  rw [branchNormalizedQRichSeparator_eq,
    branchNormalizedQRichSeparator_eq,
    blockQRichQuotientCoefficient_lift]
  push_cast
  ring

/-- The source-owned jump transports the lifted-row separator across one
complex relative edge without claiming a global descent. -/
theorem actualClozelWeightedJump_branchSeparator_edge
    {observation : GeneratedRiemannZeroObservation}
    (owner : GlobalGermOwner) (s : ℂ)
    (fibre : InverseZeroFibre observation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    actualClozelWeightedJump owner s (stage + 2) *
        branchNormalizedQRichSeparator fibre (stage + 1)
          (liftFactorRow seedOccurrence.root stage row) =
      branchNormalizedQRichSeparator fibre stage row := by
  rw [branchNormalizedQRichSeparator_successor, ← mul_assoc]
  rw [mul_comm (actualClozelWeightedJump owner s (stage + 2))]
  rw [actualClozelWeightedJump_qRich_edge, one_mul]

def clozelFactorialNormalizer (stage : Nat) : ℂ :=
  2 / (Nat.factorial (stage + 2) : ℂ)

@[simp] theorem clozelFactorialNormalizer_zero :
    clozelFactorialNormalizer 0 = 1 := by
  norm_num [clozelFactorialNormalizer]

theorem clozelFactorialNormalizer_edge (stage : Nat) :
    ((stage + 3 : Nat) : ℂ) * clozelFactorialNormalizer (stage + 1) =
      clozelFactorialNormalizer stage := by
  unfold clozelFactorialNormalizer
  rw [show stage + 1 + 2 = (stage + 2) + 1 by omega,
    Nat.factorial_succ]
  push_cast
  have factorialNe : (Nat.factorial (stage + 2) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (stage + 2)
  field_simp
  apply div_self
  exact_mod_cast (show stage + 2 + 1 ≠ 0 by omega)

/-- Necessity: any coefficient line that removes every source scale and
starts at `1` is the factorially normalized line. -/
theorem clozelNormalizer_eq_two_div_factorial
    (coefficient : Nat → ℂ)
    (initial : coefficient 0 = 1)
    (edge : ∀ stage,
      ((stage + 3 : Nat) : ℂ) * coefficient (stage + 1) =
        coefficient stage) :
    ∀ stage, coefficient stage = clozelFactorialNormalizer stage := by
  intro stage
  induction stage with
  | zero => rw [initial, clozelFactorialNormalizer_zero]
  | succ stage inductionHypothesis =>
      have scaleNe : ((stage + 3 : Nat) : ℂ) ≠ 0 := by
        exact_mod_cast (show stage + 3 ≠ 0 by omega)
      apply mul_left_cancel₀ scaleNe
      calc
        ((stage + 3 : Nat) : ℂ) * coefficient (stage + 1) =
            coefficient stage := edge stage
        _ = clozelFactorialNormalizer stage := inductionHypothesis
        _ = ((stage + 3 : Nat) : ℂ) *
            clozelFactorialNormalizer (stage + 1) :=
          (clozelFactorialNormalizer_edge stage).symm

def actualClozelJumpNormalizer
    (owner : GlobalGermOwner) (s : ℂ) : Nat → ℂ
  | 0 => 1
  | stage + 1 =>
      actualClozelWeightedJump owner s (stage + 2) *
        actualClozelJumpNormalizer owner s stage

theorem actualClozelJumpNormalizer_edge
    (owner : GlobalGermOwner) (s : ℂ) (stage : Nat) :
    ((stage + 3 : Nat) : ℂ) *
        actualClozelJumpNormalizer owner s (stage + 1) =
      actualClozelJumpNormalizer owner s stage := by
  rw [actualClozelJumpNormalizer]
  rw [← mul_assoc, ← blockQRichSuccessorScale_eq_stage_add_three]
  rw [actualClozelWeightedJump_qRich_edge, one_mul]

theorem actualClozelJumpNormalizer_eq_two_div_factorial
    (owner : GlobalGermOwner) (s : ℂ) (stage : Nat) :
    actualClozelJumpNormalizer owner s stage =
      2 / (Nat.factorial (stage + 2) : ℂ) := by
  exact clozelNormalizer_eq_two_div_factorial
    (actualClozelJumpNormalizer owner s)
    rfl
    (actualClozelJumpNormalizer_edge owner s) stage

theorem actualClozelJumpNormalizer_stageOne
    (owner : GlobalGermOwner) (s : ℂ) :
    actualClozelJumpNormalizer owner s 1 = (3 : ℂ)⁻¹ := by
  rw [actualClozelJumpNormalizer_eq_two_div_factorial]
  norm_num

theorem actualClozelJumpNormalizer_stageOne_not_integral
    (owner : GlobalGermOwner) (s : ℂ) :
    ¬ ∃ integer : ℤ,
      (integer : ℂ) = actualClozelJumpNormalizer owner s 1 := by
  rw [actualClozelJumpNormalizer_stageOne]
  rintro ⟨integer, equality⟩
  have multiplied := congrArg (fun value : ℂ => 3 * value) equality
  norm_num at multiplied
  have integerEquation : 3 * integer = 1 := by exact_mod_cast multiplied
  omega

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
