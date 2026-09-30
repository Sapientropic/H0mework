import H0mework.Physics.DiracEvolution.GalerkinEvolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Stage-nine weak Dirac matter Galerkin evolution

This module solves the finite weak action equation
`M(t) c'(t) + L(t) c(t) = 0` through the action-owned operator
`-M(t)⁻¹ L(t)`.  The generated curve retains the original weak equation,
the actual local operator bound, and the corresponding forward exponential
estimate.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracMatterWeakGalerkinEvolution

open StageNineDiracMatterGalerkinEvolution
open scoped NNReal

noncomputable section

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- The weak Galerkin evolution operator obtained by solving its mass leg. -/
def galerkinWeakActionOperator
    (mass stiffness : ℝ → E →L[ℝ] E)
    (time : ℝ) : E →L[ℝ] E :=
  -((mass time).inverse.comp (stiffness time))

omit [CompleteSpace E] in
/-- The weak operator is the mass inverse applied to the stiffness leg. -/
@[simp] theorem galerkinWeakActionOperator_apply
    (mass stiffness : ℝ → E →L[ℝ] E)
    (time : ℝ)
    (coefficient : E) :
    galerkinWeakActionOperator mass stiffness time coefficient =
      -(mass time).inverse (stiffness time coefficient) :=
  rfl

omit [CompleteSpace E] in
/-- The generated velocity solves the original finite weak equation. -/
theorem galerkinWeakActionOperator_mass_equation
    (mass stiffness : ℝ → E →L[ℝ] E)
    (time : ℝ)
    (coefficient : E)
    (massInvertible : (mass time).IsInvertible) :
    mass time (galerkinWeakActionOperator mass stiffness time coefficient) +
        stiffness time coefficient = 0 := by
  rw [galerkinWeakActionOperator_apply, map_neg,
    massInvertible.self_apply_inverse]
  simp

private theorem continuous_mass_inverse
    (mass : ℝ → E →L[ℝ] E)
    (massContinuous : Continuous mass)
    (massInvertible : ∀ time, (mass time).IsInvertible) :
    Continuous fun time ↦ (mass time).inverse := by
  rw [continuous_iff_continuousAt]
  intro time
  have inverseContinuousAt :
      ContinuousAt ContinuousLinearMap.inverse (mass time) :=
    ((massInvertible time).contDiffAt_map_inverse (n := 1)).continuousAt
  exact inverseContinuousAt.comp massContinuous.continuousAt

/-- Invertibility and continuity of the mass leg make the generated weak
operator continuous. -/
theorem galerkinWeakActionOperator_continuous
    (mass stiffness : ℝ → E →L[ℝ] E)
    (massContinuous : Continuous mass)
    (stiffnessContinuous : Continuous stiffness)
    (massInvertible : ∀ time, (mass time).IsInvertible) :
    Continuous (galerkinWeakActionOperator mass stiffness) := by
  exact ((continuous_mass_inverse mass massContinuous massInvertible).clm_comp
    stiffnessContinuous).neg

/-- An invertible continuous weak mass leg generates a local coefficient curve
that solves the original finite weak equation and carries its actual forward
operator-norm estimate. -/
theorem exists_galerkinWeakCoefficientCurve
    (mass stiffness : ℝ → E →L[ℝ] E)
    (massContinuous : Continuous mass)
    (stiffnessContinuous : Continuous stiffness)
    (massInvertible : ∀ time, (mass time).IsInvertible)
    (initial : E)
    (initialTime : ℝ) :
    ∃ bound : ℝ≥0, ∃ coefficient : ℝ → E,
      coefficient initialTime = initial ∧
        ((∀ time ∈
            Set.Icc
              (initialTime - galerkinLinearLocalTimeRadius bound initial)
              (initialTime + galerkinLinearLocalTimeRadius bound initial),
            ‖galerkinWeakActionOperator mass stiffness time‖₊ ≤ bound) ∧
          ((∀ time ∈
              Set.Icc
                (initialTime - galerkinLinearLocalTimeRadius bound initial)
                (initialTime + galerkinLinearLocalTimeRadius bound initial),
              HasDerivWithinAt coefficient
                (galerkinWeakActionOperator mass stiffness time
                  (coefficient time))
                (Set.Icc
                  (initialTime - galerkinLinearLocalTimeRadius bound initial)
                  (initialTime + galerkinLinearLocalTimeRadius bound initial))
                time ∧
              mass time
                    (galerkinWeakActionOperator mass stiffness time
                      (coefficient time)) +
                  stiffness time (coefficient time) = 0) ∧
            ∀ time ∈
              Set.Icc initialTime
                (initialTime + galerkinLinearLocalTimeRadius bound initial),
              ‖coefficient time‖ ≤
                ‖initial‖ * Real.exp ((bound : ℝ) * (time - initialTime)))) := by
  obtain ⟨bound, coefficient, initialValue, operatorBound, evolution,
      coefficientBound⟩ :=
    exists_galerkinLinearCoefficientCurve_of_continuous_with_norm_bound
      (galerkinWeakActionOperator mass stiffness)
      (galerkinWeakActionOperator_continuous mass stiffness massContinuous
        stiffnessContinuous massInvertible)
      initial initialTime
  refine ⟨bound, coefficient, initialValue, operatorBound, ?_, coefficientBound⟩
  intro time timeMem
  exact ⟨evolution time timeMem,
    galerkinWeakActionOperator_mass_equation mass stiffness time
      (coefficient time) (massInvertible time)⟩

/-- An invertible continuous weak mass leg generates the exact finite weak
evolution on any compact forward interval.  The interval is supplied by the
source chronology; neither an endpoint state nor an operator bound is part of
the producer mouth. -/
theorem exists_galerkinWeakCoefficientCurve_on_Icc
    (mass stiffness : ℝ → E →L[ℝ] E)
    (massContinuous : Continuous mass)
    (stiffnessContinuous : Continuous stiffness)
    (massInvertible : ∀ time, (mass time).IsInvertible)
    (initial : E)
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd) :
    ∃ coefficient : ℝ → E,
      coefficient timeStart = initial ∧
        ∀ time ∈ Set.Icc timeStart timeEnd,
          HasDerivWithinAt coefficient
              (galerkinWeakActionOperator mass stiffness time
                (coefficient time))
              (Set.Icc timeStart timeEnd) time ∧
            mass time
                  (galerkinWeakActionOperator mass stiffness time
                    (coefficient time)) +
                stiffness time (coefficient time) = 0 := by
  obtain ⟨coefficient, initialValue, evolution⟩ :=
    exists_galerkinLinearCoefficientCurve_on_Icc
      (galerkinWeakActionOperator mass stiffness)
      (galerkinWeakActionOperator_continuous mass stiffness massContinuous
        stiffnessContinuous massInvertible)
      initial timeStart timeEnd timeOrder
  refine ⟨coefficient, initialValue, ?_⟩
  intro time timeMem
  exact ⟨by
      simpa [galerkinLinearVelocity] using evolution time timeMem,
    galerkinWeakActionOperator_mass_equation mass stiffness time
      (coefficient time) (massInvertible time)⟩

section RieszMass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The coefficient-space mass operator represented by a bounded real weak
mass form. -/
def galerkinWeakMassOperator
    (massForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (time : ℝ) : H →L[ℝ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (massForm time)

@[simp] theorem real_inner_galerkinWeakMassOperator
    (massForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (time : ℝ)
    (first second : H) :
    inner ℝ (galerkinWeakMassOperator massForm time first) second =
      massForm time first second := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply
    (massForm time) first second

/-- A continuous weak mass form has a continuous Riesz mass operator. -/
theorem galerkinWeakMassOperator_continuous
    (massForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (massFormContinuous : Continuous massForm) :
    Continuous (galerkinWeakMassOperator massForm) := by
  unfold galerkinWeakMassOperator
  exact continuous_const.clm_comp massFormContinuous

/-- Strict positivity of the weak mass form makes its Riesz operator
injective. -/
theorem galerkinWeakMassOperator_injective
    (massForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (time : ℝ)
    (positive : ∀ coefficient ≠ 0,
      0 < massForm time coefficient coefficient) :
    Function.Injective (galerkinWeakMassOperator massForm time) := by
  intro first second equality
  by_contra distinct
  have differenceNonzero : first - second ≠ 0 := sub_ne_zero.mpr distinct
  have imageZero :
      galerkinWeakMassOperator massForm time (first - second) = 0 := by
    rw [map_sub, equality, sub_self]
  have pairingZero :
      massForm time (first - second) (first - second) = 0 := by
    rw [← real_inner_galerkinWeakMassOperator, imageZero]
    simp
  exact (positive (first - second) differenceNonzero).ne' pairingZero

/-- In finite dimension, strict weak-mass positivity supplies the exact
continuous inverse required by the generated evolution operator. -/
theorem galerkinWeakMassOperator_isInvertible
    [FiniteDimensional ℝ H]
    (massForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (time : ℝ)
    (positive : ∀ coefficient ≠ 0,
      0 < massForm time coefficient coefficient) :
    (galerkinWeakMassOperator massForm time).IsInvertible := by
  let equivalence : H ≃L[ℝ] H :=
    (LinearEquiv.ofInjectiveEndo
      (galerkinWeakMassOperator massForm time).toLinearMap
      (galerkinWeakMassOperator_injective massForm time positive)
    ).toContinuousLinearEquiv
  exact ⟨equivalence, by rfl⟩

/-- A continuous strictly positive weak mass form and continuous stiffness
form generate the finite weak evolution without taking mass invertibility as
an external certificate. -/
theorem exists_galerkinWeakCoefficientCurve_of_positiveMassForm
    [FiniteDimensional ℝ H]
    (massForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (stiffness : ℝ → H →L[ℝ] H)
    (massFormContinuous : Continuous massForm)
    (stiffnessContinuous : Continuous stiffness)
    (positive : ∀ time (coefficient : H), coefficient ≠ 0 →
      0 < massForm time coefficient coefficient)
    (initial : H)
    (initialTime : ℝ) :
    ∃ bound : ℝ≥0, ∃ coefficient : ℝ → H,
      coefficient initialTime = initial ∧
        ((∀ time ∈
            Set.Icc
              (initialTime - galerkinLinearLocalTimeRadius bound initial)
              (initialTime + galerkinLinearLocalTimeRadius bound initial),
            ‖galerkinWeakActionOperator
                (galerkinWeakMassOperator massForm) stiffness time‖₊ ≤ bound) ∧
          ((∀ time ∈
              Set.Icc
                (initialTime - galerkinLinearLocalTimeRadius bound initial)
                (initialTime + galerkinLinearLocalTimeRadius bound initial),
              HasDerivWithinAt coefficient
                (galerkinWeakActionOperator
                  (galerkinWeakMassOperator massForm) stiffness time
                  (coefficient time))
                (Set.Icc
                  (initialTime - galerkinLinearLocalTimeRadius bound initial)
                  (initialTime + galerkinLinearLocalTimeRadius bound initial))
                time ∧
              galerkinWeakMassOperator massForm time
                    (galerkinWeakActionOperator
                      (galerkinWeakMassOperator massForm) stiffness time
                      (coefficient time)) +
                  stiffness time (coefficient time) = 0) ∧
            ∀ time ∈
              Set.Icc initialTime
                (initialTime + galerkinLinearLocalTimeRadius bound initial),
              ‖coefficient time‖ ≤
                ‖initial‖ * Real.exp ((bound : ℝ) * (time - initialTime)))) := by
  exact exists_galerkinWeakCoefficientCurve
    (galerkinWeakMassOperator massForm) stiffness
    (galerkinWeakMassOperator_continuous massForm massFormContinuous)
    stiffnessContinuous
    (fun time ↦ galerkinWeakMassOperator_isInvertible massForm time
      (positive time))
    initial initialTime

end RieszMass

end

end SaturationMonoid.PhysicsCore.StageNineDiracMatterWeakGalerkinEvolution
