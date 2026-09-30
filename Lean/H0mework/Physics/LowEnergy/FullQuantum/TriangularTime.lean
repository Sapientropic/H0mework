import H0mework.Physics.LowEnergy.FullQuantum.TriangularSource
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact single-insertion Duhamel formula, obtained by differentiating a
true exponential flow and applying the fundamental theorem of calculus. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular
open ProofFreeRicherAnholonomicSource StageNineHolonomicField YangMills.FullPairing
open MeasureTheory
noncomputable section
local instance : NormedAlgebra ℚ (Hilbert →L[ℂ] Hilbert) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (Hilbert →L[ℂ] Hilbert) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

theorem operator_add (A B : Mother) : operator (A+B) = operator A + operator B := by
  ext v
  simp [operator]

theorem operator_mul (A B : Mother) : operator (A*B) = operator A * operator B := by
  ext v
  simp [operator, Module.End.mul_apply]

theorem operator_zero : operator (0 : Mother) = 0 := by ext v; simp [operator]

theorem operator_smul (c : ℂ) (A : Mother) : operator (c • A) = c • operator A := by
  ext v
  simp [operator]

theorem operator_commute (A B : Mother) (commutes : Commute A B) :
    Commute (operator A) (operator B) := by
  have generated := congrArg operator commutes.eq
  rw [operator_mul, operator_mul] at generated
  exact generated

abbrev Operators := Hilbert →L[ℂ] Hilbert

def flow (A : Operators) (t : ℝ) : Operators := NormedSpace.exp ((t : ℂ) • A)

theorem flow_zero (A : Operators) : flow A 0 = 1 := by
  have zero : (0 : ℂ) • A = 0 := by ext v i; simp
  rw [flow, Complex.ofReal_zero, zero, NormedSpace.exp_zero]

theorem flow_add (A : Operators) (t s : ℝ) : flow A (t+s) = flow A t * flow A s := by
  have scalarAdd : ((t+s : ℝ) : ℂ) • A = (t : ℂ) • A + (s : ℂ) • A := by
    ext v i
    simp
    ring
  simp only [flow, scalarAdd]
  exact NormedSpace.exp_add_of_commute (((Commute.refl A).smul_left (t : ℂ)).smul_right (s : ℂ))

theorem flow_inverse (A : Operators) (t : ℝ) : flow A (-t) * flow A t = 1 := by
  rw [← flow_add, neg_add_cancel, flow_zero]

theorem flow_derivative (A : Operators) (t : ℝ) :
    HasDerivAt (flow A) (flow A t * A) t := by
  convert! hasDerivAt_exp_smul_const A t using 1

theorem flow_commute (A : Operators) (t : ℝ) : Commute (flow A t) A :=
  ((Commute.refl A).smul_left (t : ℂ)).exp_left

theorem flow_continuous (A : Operators) : Continuous (flow A) :=
  continuous_iff_continuousAt.mpr (fun t => (flow_derivative A t).continuousAt)

theorem commutes_flow (P A : Operators) (commutes : Commute P A) (t : ℝ) :
    Commute P (flow A t) :=
  (commutes.smul_right (t : ℂ)).exp_right

theorem single_insertion_left (P A N : Operators) (commutes : Commute P A)
    (output : P*N=N) (input : N*P=0) (t : ℝ) :
    N * flow (A+N) t = N * flow A t := by
  have semi : SemiconjBy (1-P) (A+N) A := by
    change (1-P)*(A+N)=A*(1-P)
    apply ContinuousLinearMap.ext
    intro v
    have ca : P (A v)=A (P v) := congrArg (fun M : Operators => M v) commutes.eq
    have pn : P (N v)=N v := congrArg (fun M : Operators => M v) output
    change A v+N v-P (A v+N v)=A (v-P v)
    rw [map_add, map_sub, ca, pn]
    module
  have transported := (semi.smul_right (t : ℂ)).exp_right
  change (1-P)*flow (A+N) t=flow A t*(1-P) at transported
  have noInput : N*(1-P)=N := by rw [mul_sub, mul_one, input, sub_zero]
  have freeCommute := (commutes_flow P A commutes t).eq
  calc
    _ = N*((1-P)*flow (A+N) t) := by rw [← mul_assoc, noInput]
    _ = N*(flow A t*(1-P)) := by rw [transported]
    _ = N*((1-P)*flow A t) := by
      congr 1
      rw [mul_sub, sub_mul, mul_one, one_mul, freeCommute]
    _ = N*flow A t := by rw [← mul_assoc, noInput]

def interactionPicture (A N : Operators) (t : ℝ) : Operators :=
  flow A (-t) * flow (A+N) t

theorem interactionPicture_derivative (P A N : Operators) (commutes : Commute P A)
    (output : P*N=N) (input : N*P=0) (t : ℝ) :
    HasDerivAt (interactionPicture A N)
      (flow A (-t) * N * flow A t) t := by
  have inverse := (flow_derivative A (-t)).scomp t (hasDerivAt_neg t)
  have derivative := inverse.mul (flow_derivative (A+N) t)
  have commuteFull := (flow_commute (A+N) t).eq
  have source := single_insertion_left P A N commutes output input t
  convert! derivative using 1
  rw [mul_assoc, ← source, commuteFull]
  apply ContinuousLinearMap.ext
  intro v
  change flow A (-t) (N (flow (A+N) t v)) =
    (-1 : ℝ) • flow A (-t) (A (flow (A+N) t v)) +
      flow A (-t) (A (flow (A+N) t v) + N (flow (A+N) t v))
  rw [map_add]
  module

theorem flow_exact_single_integral (P A N : Operators) (commutes : Commute P A)
    (output : P*N=N) (input : N*P=0) (t : ℝ) :
    flow (A+N) t = flow A t +
      flow A t * (∫ s in (0 : ℝ)..t, flow A (-s) * N * flow A s) := by
  have continuousIntegrand : Continuous (fun s : ℝ => flow A (-s)*N*flow A s) :=
    (((flow_continuous A).comp continuous_neg).mul continuous_const).mul (flow_continuous A)
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => interactionPicture_derivative P A N commutes output input s)
    (continuousIntegrand.intervalIntegrable (0 : ℝ) t)
  have initial : interactionPicture A N 0 = 1 := by
    simp only [interactionPicture, neg_zero, flow_zero, one_mul]
  have inverse : flow A t * flow A (-t) = 1 := by
    simpa only [neg_neg] using flow_inverse A (-t)
  rw [integral, initial, interactionPicture]
  apply ContinuousLinearMap.ext
  intro v
  have returned := congrArg (fun M : Operators => M (flow (A+N) t v)) inverse
  change flow A t (flow A (-t) (flow (A+N) t v)) = flow (A+N) t v at returned
  change flow (A+N) t v = flow A t v + flow A t (flow A (-t) (flow (A+N) t v)-v)
  rw [map_sub, returned]
  abel

theorem flow_exact_duhamel (P A N : Operators) (commutes : Commute P A)
    (output : P*N=N) (input : N*P=0) (t : ℝ) :
    flow (A+N) t = flow A t +
      ∫ s in (0 : ℝ)..t, flow A (t-s) * N * flow A s := by
  rw [flow_exact_single_integral P A N commutes output input]
  congr 1
  have continuousIntegrand : Continuous (fun s : ℝ => flow A (-s)*N*flow A s) :=
    (((flow_continuous A).comp continuous_neg).mul continuous_const).mul (flow_continuous A)
  have pull := (ContinuousLinearMap.mul ℂ Operators (flow A t)).intervalIntegral_comp_comm (μ := volume)
    (continuousIntegrand.intervalIntegrable (0 : ℝ) t)
  change (∫ s in (0 : ℝ)..t, flow A t*(flow A (-s)*N*flow A s)) =
    flow A t*(∫ s in (0 : ℝ)..t, flow A (-s)*N*flow A s) at pull
  rw [← pull]
  apply intervalIntegral.integral_congr
  intro s _
  have group : flow A t*flow A (-s)=flow A (t-s) := by rw [← flow_add, sub_eq_add_neg]
  calc
    _ = (flow A t*flow A (-s))*N*flow A s := by simp only [mul_assoc]
    _ = _ := by rw [group]

def freeEvolution (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) : Operators := flow (operator (freeDrift C p k)) t

theorem source_exact_duhamel (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    evolution C p k t = freeEvolution C p k t +
      ∫ s in (0 : ℝ)..t, freeEvolution C p k (t-s) *
        operator (interaction C p) * freeEvolution C p k s := by
  have preserves : Commute (operator MixedSymbol.degreeSix) (operator (freeDrift C p k)) :=
    operator_commute _ _ (grade_freeDrift 0 C p k)
  have output : operator MixedSymbol.degreeSix * operator (interaction C p) =
      operator (interaction C p) := by rw [← operator_mul, six_interaction]
  have input : operator (interaction C p) * operator MixedSymbol.degreeSix = 0 := by
    rw [← operator_mul, interaction_six, operator_zero]
  have generated := flow_exact_duhamel _ _ _ preserves output input t
  change flow (operator (freeDrift C p k)+operator (interaction C p)) t = _ at generated
  have full : evolution C p k t =
      flow (operator (freeDrift C p k)+operator (interaction C p)) t := by
    rw [evolution, source_split, operator_add]
    rfl
  rw [full]
  exact generated

theorem source_exact_duhamel_hamiltonian (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    evolution C p k t = freeEvolution C p k t + (-Complex.I) •
      ∫ s in (0 : ℝ)..t, freeEvolution C p k (t-s) *
        operator (interactionHamiltonian C p) * freeEvolution C p k s := by
  rw [source_exact_duhamel, ← intervalIntegral.integral_smul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  rw [← interaction_hamiltonian_drift C p, operator_smul]
  change freeEvolution C p k (t-s) * ((-Complex.I) • operator (interactionHamiltonian C p)) *
    freeEvolution C p k s = (-Complex.I) •
      (freeEvolution C p k (t-s) * operator (interactionHamiltonian C p) * freeEvolution C p k s)
  rw [mul_smul_comm, smul_mul_assoc]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular
