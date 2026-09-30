import H0mework.NavierStokes.InitialData.PhysicalCompiler
import H0mework.NavierStokes.InitialData.StretchingPhysicalBridge

/-!
# Source-generated three-dimensional vorticity nonlinear pair generator

The raw vorticity source already generates a complete signed support, its
Biot--Savart velocity coefficients, and the complete ordered pair table.  On
that same table this module generates the advection row

```text
(u_p dot nabla) omega_q = I * 2 pi * (q dot u_p) omega_q
```

and the full vorticity nonlinear row

```text
(omega_p dot nabla) u_q - (u_p dot nabla) omega_q.
```

A single row need not be transverse.  Transversality is generated only after
the complete output fiber is summed: swapping `(p,q)` with `(q,p)` preserves
the output and reverses the longitudinal coefficient.  Thus no divergence-
free nonlinear coefficient, selected output, nonvanishing row, or target is
accepted at the source mouth.

This module stops at the complete coefficient producer.  The physical-field
compiler, source update, and PDE consumer are downstream obligations; none is
claimed here.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientNonlinearPairGenerator

open scoped BigOperators Matrix

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientStretchingPhysicalBridge

noncomputable section

/-! ## Complete coefficient generator -/

/-- Coefficient of the vorticity-advection row `(u_p dot nabla) omega_q`. -/
def generatedVorticityAdvectionPairContribution
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) : ComplexCoordinateVector :=
  (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (complexWavevector pair.2 ⬝ᵥ
        generatedVelocityCoefficient source pair.1)) •
    generatedVorticityCoefficient source pair.2

/-- Full vorticity nonlinear row: stretching minus vorticity advection. -/
def generatedVorticityNonlinearPairContribution
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) : ComplexCoordinateVector :=
  generatedStretchingPairContribution source pair -
    generatedVorticityAdvectionPairContribution source pair

/-- Pair negation preserves physical reality of the advection row. -/
theorem generatedVorticityAdvectionPairContribution_pairNeg
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    generatedVorticityAdvectionPairContribution source
        (stretchingPairNeg pair) =
      vectorConj
        (generatedVorticityAdvectionPairContribution source pair) := by
  rw [generatedVorticityAdvectionPairContribution,
    generatedVorticityAdvectionPairContribution]
  simp only [stretchingPairNeg,
    generatedVelocityCoefficient_waveNeg,
    generatedVorticityCoefficient_waveNeg,
    complexWavevector_waveNeg_dot_vectorConj,
    vectorConj_smul]
  funext coordinate
  simp [vectorConj]

/-- Pair negation preserves physical reality of the full nonlinear row. -/
theorem generatedVorticityNonlinearPairContribution_pairNeg
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    generatedVorticityNonlinearPairContribution source
        (stretchingPairNeg pair) =
      vectorConj
        (generatedVorticityNonlinearPairContribution source pair) := by
  rw [generatedVorticityNonlinearPairContribution,
    generatedVorticityNonlinearPairContribution,
    generatedStretchingPairContribution_pairNeg,
    generatedVorticityAdvectionPairContribution_pairNeg,
    vectorConj_sub]

/-- Complete output-fiber aggregation of the generated nonlinear rows. -/
def generatedVorticityNonlinearCoefficientAt
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  ∑ pair ∈ generatedStretchingPairFiber source output,
    generatedVorticityNonlinearPairContribution source pair

/-- The aggregate output coefficient is the complete pair table with the
output condition internal to the summand. -/
theorem generatedVorticityNonlinearCoefficientAt_eq_fullPairTableSum
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    generatedVorticityNonlinearCoefficientAt source output =
      ∑ pair ∈ generatedStretchingPairTable source,
        if stretchingPairOutput pair = output then
          generatedVorticityNonlinearPairContribution source pair
        else 0 := by
  rw [generatedVorticityNonlinearCoefficientAt,
    generatedStretchingPairFiber,
    Finset.sum_filter]

/-- Complete output aggregation retains source-generated Fourier reality. -/
theorem generatedVorticityNonlinearCoefficientAt_waveNeg
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    generatedVorticityNonlinearCoefficientAt source (waveNeg output) =
      vectorConj
        (generatedVorticityNonlinearCoefficientAt source output) := by
  rw [generatedVorticityNonlinearCoefficientAt,
    generatedVorticityNonlinearCoefficientAt,
    vectorConj_finset_sum]
  symm
  refine Finset.sum_equiv stretchingPairNegEquiv ?_ ?_
  · intro pair
    exact
      (mem_generatedStretchingPairFiber_pairNeg_iff
        source output pair).symm
  · intro pair membership
    exact
      (generatedVorticityNonlinearPairContribution_pairNeg
        source pair).symm

/-! ## Pair-swap generation of aggregate transversality -/

/-- Swap the advecting/stretching and transported/velocity frequencies. -/
def stretchingPairSwap (pair : StretchingPair) : StretchingPair :=
  (pair.2, pair.1)

@[simp] theorem stretchingPairSwap_involutive
    (pair : StretchingPair) :
    stretchingPairSwap (stretchingPairSwap pair) = pair := by
  rcases pair with ⟨first, second⟩
  rfl

/-- Pair swap as an involution of the ambient ordered-pair carrier. -/
def stretchingPairSwapEquiv : StretchingPair ≃ StretchingPair where
  toFun := stretchingPairSwap
  invFun := stretchingPairSwap
  left_inv := stretchingPairSwap_involutive
  right_inv := stretchingPairSwap_involutive

@[simp] theorem stretchingPairOutput_swap
    (pair : StretchingPair) :
    stretchingPairOutput (stretchingPairSwap pair) =
      stretchingPairOutput pair := by
  simp [stretchingPairOutput, stretchingPairSwap, add_comm]

@[simp] theorem mem_generatedStretchingPairTable_swap_iff
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    stretchingPairSwap pair ∈ generatedStretchingPairTable source ↔
      pair ∈ generatedStretchingPairTable source := by
  simp [stretchingPairSwap, and_comm]

@[simp] theorem mem_generatedStretchingPairFiber_swap_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector)
    (pair : StretchingPair) :
    stretchingPairSwap pair ∈
        generatedStretchingPairFiber source output ↔
      pair ∈ generatedStretchingPairFiber source output := by
  rw [mem_generatedStretchingPairFiber_iff,
    mem_generatedStretchingPairFiber_iff,
    mem_generatedStretchingPairTable_swap_iff,
    stretchingPairOutput_swap]

private theorem complexWavevector_stretchingPairOutput
    (pair : StretchingPair) :
    complexWavevector (stretchingPairOutput pair) =
      complexWavevector pair.1 + complexWavevector pair.2 := by
  funext coordinate
  simp [complexWavevector, stretchingPairOutput]

private theorem stretchingPairOutput_dot_generatedVelocityCoefficient_second
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    complexWavevector (stretchingPairOutput pair) ⬝ᵥ
        generatedVelocityCoefficient source pair.2 =
      complexWavevector pair.1 ⬝ᵥ
        generatedVelocityCoefficient source pair.2 := by
  rw [complexWavevector_stretchingPairOutput,
    add_dotProduct,
    generatedVelocityCoefficient_transverse,
    add_zero]

private theorem stretchingPairOutput_dot_generatedVorticityCoefficient_second
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    complexWavevector (stretchingPairOutput pair) ⬝ᵥ
        generatedVorticityCoefficient source pair.2 =
      complexWavevector pair.1 ⬝ᵥ
        generatedVorticityCoefficient source pair.2 := by
  rw [complexWavevector_stretchingPairOutput,
    add_dotProduct,
    generatedVorticityCoefficient_transverse,
    add_zero]

/-- Exact longitudinal coefficient of one generated nonlinear pair row.
This row is not asserted to vanish. -/
theorem complexWavevector_output_dot_generatedVorticityNonlinearPairContribution
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    complexWavevector (stretchingPairOutput pair) ⬝ᵥ
        generatedVorticityNonlinearPairContribution source pair =
      (Complex.I * (((2 * Real.pi : ℝ) : ℂ))) *
        ((complexWavevector pair.2 ⬝ᵥ
            generatedVorticityCoefficient source pair.1) *
          (complexWavevector pair.1 ⬝ᵥ
            generatedVelocityCoefficient source pair.2) -
        (complexWavevector pair.2 ⬝ᵥ
            generatedVelocityCoefficient source pair.1) *
          (complexWavevector pair.1 ⬝ᵥ
            generatedVorticityCoefficient source pair.2)) := by
  rw [generatedVorticityNonlinearPairContribution,
    generatedStretchingPairContribution,
    generatedVorticityAdvectionPairContribution,
    dotProduct_sub,
    dotProduct_smul,
    dotProduct_smul,
    stretchingPairOutput_dot_generatedVelocityCoefficient_second,
    stretchingPairOutput_dot_generatedVorticityCoefficient_second]
  simp only [smul_eq_mul]
  ring

/-- Swapping the two source frequencies reverses the longitudinal nonlinear
coefficient while preserving the output frequency. -/
theorem generatedVorticityNonlinearPairDivergence_swap
    (source : RawVorticityFourierSource)
    (pair : StretchingPair) :
    complexWavevector
          (stretchingPairOutput (stretchingPairSwap pair)) ⬝ᵥ
        generatedVorticityNonlinearPairContribution source
          (stretchingPairSwap pair) =
      -(complexWavevector (stretchingPairOutput pair) ⬝ᵥ
        generatedVorticityNonlinearPairContribution source pair) := by
  rw [complexWavevector_output_dot_generatedVorticityNonlinearPairContribution,
    complexWavevector_output_dot_generatedVorticityNonlinearPairContribution]
  simp only [stretchingPairSwap]
  ring

private theorem generatedVorticityNonlinearPairDivergence_fiber_sum_eq_zero
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    (∑ pair ∈ generatedStretchingPairFiber source output,
      complexWavevector (stretchingPairOutput pair) ⬝ᵥ
        generatedVorticityNonlinearPairContribution source pair) = 0 := by
  have swappedSum :
      (∑ pair ∈ generatedStretchingPairFiber source output,
        complexWavevector
              (stretchingPairOutput (stretchingPairSwap pair)) ⬝ᵥ
          generatedVorticityNonlinearPairContribution source
            (stretchingPairSwap pair)) =
        ∑ pair ∈ generatedStretchingPairFiber source output,
          complexWavevector (stretchingPairOutput pair) ⬝ᵥ
            generatedVorticityNonlinearPairContribution source pair := by
    refine Finset.sum_equiv stretchingPairSwapEquiv ?_ ?_
    · intro pair
      exact
        (mem_generatedStretchingPairFiber_swap_iff
          source output pair).symm
    · intro pair membership
      rfl
  have sumEqNeg :
      (∑ pair ∈ generatedStretchingPairFiber source output,
        complexWavevector (stretchingPairOutput pair) ⬝ᵥ
          generatedVorticityNonlinearPairContribution source pair) =
        -(∑ pair ∈ generatedStretchingPairFiber source output,
          complexWavevector (stretchingPairOutput pair) ⬝ᵥ
            generatedVorticityNonlinearPairContribution source pair) := by
    calc
      (∑ pair ∈ generatedStretchingPairFiber source output,
          complexWavevector (stretchingPairOutput pair) ⬝ᵥ
            generatedVorticityNonlinearPairContribution source pair) =
          ∑ pair ∈ generatedStretchingPairFiber source output,
            complexWavevector
                (stretchingPairOutput (stretchingPairSwap pair)) ⬝ᵥ
              generatedVorticityNonlinearPairContribution source
                (stretchingPairSwap pair) := swappedSum.symm
      _ = ∑ pair ∈ generatedStretchingPairFiber source output,
            -(complexWavevector (stretchingPairOutput pair) ⬝ᵥ
              generatedVorticityNonlinearPairContribution source pair) := by
          apply Finset.sum_congr rfl
          intro pair pairMembership
          exact generatedVorticityNonlinearPairDivergence_swap source pair
      _ = -(∑ pair ∈ generatedStretchingPairFiber source output,
            complexWavevector (stretchingPairOutput pair) ⬝ᵥ
              generatedVorticityNonlinearPairContribution source pair) := by
          rw [Finset.sum_neg_distrib]
  have twiceSumZero :
      (2 : ℂ) *
          (∑ pair ∈ generatedStretchingPairFiber source output,
            complexWavevector (stretchingPairOutput pair) ⬝ᵥ
              generatedVorticityNonlinearPairContribution source pair) = 0 := by
    calc
      (2 : ℂ) *
          (∑ pair ∈ generatedStretchingPairFiber source output,
            complexWavevector (stretchingPairOutput pair) ⬝ᵥ
              generatedVorticityNonlinearPairContribution source pair) =
          (∑ pair ∈ generatedStretchingPairFiber source output,
            complexWavevector (stretchingPairOutput pair) ⬝ᵥ
              generatedVorticityNonlinearPairContribution source pair) +
          (∑ pair ∈ generatedStretchingPairFiber source output,
            complexWavevector (stretchingPairOutput pair) ⬝ᵥ
              generatedVorticityNonlinearPairContribution source pair) := by ring
      _ = -(∑ pair ∈ generatedStretchingPairFiber source output,
              complexWavevector (stretchingPairOutput pair) ⬝ᵥ
                generatedVorticityNonlinearPairContribution source pair) +
            (∑ pair ∈ generatedStretchingPairFiber source output,
              complexWavevector (stretchingPairOutput pair) ⬝ᵥ
                generatedVorticityNonlinearPairContribution source pair) := by
          exact congrArg
            (fun value : ℂ => value +
              (∑ pair ∈ generatedStretchingPairFiber source output,
                complexWavevector (stretchingPairOutput pair) ⬝ᵥ
                  generatedVorticityNonlinearPairContribution source pair))
            sumEqNeg
      _ = 0 := neg_add_cancel _
  exact
    (mul_eq_zero.mp twiceSumZero).resolve_left (by norm_num)

/-- The complete nonlinear output coefficient is transverse.  This is
generated by pair-swap cancellation on the actual output fiber. -/
theorem generatedVorticityNonlinearCoefficientAt_transverse
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    complexWavevector output ⬝ᵥ
        generatedVorticityNonlinearCoefficientAt source output = 0 := by
  rw [generatedVorticityNonlinearCoefficientAt,
    dotProduct_sum]
  calc
    (∑ pair ∈ generatedStretchingPairFiber source output,
        complexWavevector output ⬝ᵥ
          generatedVorticityNonlinearPairContribution source pair) =
        ∑ pair ∈ generatedStretchingPairFiber source output,
          complexWavevector (stretchingPairOutput pair) ⬝ᵥ
            generatedVorticityNonlinearPairContribution source pair := by
      apply Finset.sum_congr rfl
      intro pair pairMembership
      have outputEquality :=
        (mem_generatedStretchingPairFiber_iff
          source output pair).mp pairMembership |>.2
      rw [outputEquality]
    _ = 0 :=
      generatedVorticityNonlinearPairDivergence_fiber_sum_eq_zero
        source output

/-! ## Empty-source coefficient controls -/

@[simp] theorem zeroRawVorticitySource_generatedVorticityNonlinearCoefficientAt
    (output : IntegerWavevector) :
    generatedVorticityNonlinearCoefficientAt
        zeroRawVorticitySource output = 0 := by
  simp [generatedVorticityNonlinearCoefficientAt,
    generatedStretchingPairFiber]

end

end ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
end NavierStokes
end SaturationMonoid
