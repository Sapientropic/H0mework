import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussCoframeCore

/-! Complete six-coordinate coframe kinetic action in the original weighted core. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussCoframeKinetic
open GaussNativeEnergy GaussHistoryHilbert GaussCoreDifferential GaussCoreHilbert GaussFockPair
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open scoped ContDiff Matrix

def polynomial (q : Coframe) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-q 0^2, q 0*q 1, q 0*q 2, q 0*q 3, q 0*q 4, q 0*q 5;
    q 0*q 1, -4*q 0^2-q 1^2, -q 1*q 2, q 1*q 3, q 1*q 4, q 1*q 5;
    q 0*q 2, -q 1*q 2, -q 2^2, q 2*q 3, q 2*q 4, q 2*q 5;
    q 0*q 3, q 1*q 3, q 2*q 3, -4*q 0^2-4*q 1^2-q 3^2, -4*q 1*q 2-q 3*q 4, -q 3*q 5;
    q 0*q 4, q 1*q 4, q 2*q 4, -4*q 1*q 2-q 3*q 4, -4*q 2^2-q 4^2, -q 4*q 5;
    q 0*q 5, q 1*q 5, q 2*q 5, -q 3*q 5, -q 4*q 5, -q 5^2]

def coefficient (i j : Fin 6) (z : SourceCoordinateSlice) : ℝ :=
  sourceTime 0/(4*volume z)*polynomial z.1 i j

theorem coefficient_symmetric (i j : Fin 6) (z : SourceCoordinateSlice) :
    coefficient i j z = coefficient j i z := by
  unfold coefficient
  congr 1
  fin_cases i <;> fin_cases j <;> rfl

theorem coefficient_smooth (i j : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (coefficient i j) z.val := by
  have hp : ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => polynomial w.1 i j) z.val := by
    fin_cases i
    · fin_cases j
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -w.1 0^2) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0*w.1 1) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0*w.1 2) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0*w.1 3) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0*w.1 4) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0*w.1 5) z.val
        fun_prop
    · fin_cases j
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0*w.1 1) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -4*w.1 0^2-w.1 1^2) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -w.1 1*w.1 2) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 1*w.1 3) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 1*w.1 4) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 1*w.1 5) z.val
        fun_prop
    · fin_cases j
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0*w.1 2) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -w.1 1*w.1 2) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -w.1 2^2) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 2*w.1 3) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 2*w.1 4) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 2*w.1 5) z.val
        fun_prop
    · fin_cases j
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0*w.1 3) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 1*w.1 3) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 2*w.1 3) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -4*w.1 0^2-4*w.1 1^2-w.1 3^2) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -4*w.1 1*w.1 2-w.1 3*w.1 4) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -w.1 3*w.1 5) z.val
        fun_prop
    · fin_cases j
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0*w.1 4) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 1*w.1 4) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 2*w.1 4) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -4*w.1 1*w.1 2-w.1 3*w.1 4) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -4*w.1 2^2-w.1 4^2) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -w.1 4*w.1 5) z.val
        fun_prop
    · fin_cases j
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0*w.1 5) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 1*w.1 5) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 2*w.1 5) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -w.1 3*w.1 5) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -w.1 4*w.1 5) z.val
        fun_prop
      · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -w.1 5^2) z.val
        fun_prop
  exact (contDiffAt_const.div (contDiffAt_const.mul volume_smooth.contDiffAt)
    (mul_ne_zero (by norm_num) (volume_pos z).ne')).mul hp

def term (i j : Fin 6) : QuantumTest →ₗ[ℂ] QuantumTest :=
  (GaussCoframeCore.adjoint i).comp ((GaussNativeForm.multiply (coefficient i j)
    (coefficient_smooth i j)).comp (GaussCoframeCore.momentum j))

theorem adjoint_pair (i : Fin 6) (f g : QuantumTest) :
    sourcePair f (GaussCoframeCore.adjoint i g) = sourcePair (GaussCoframeCore.momentum i f) g := by
  have h := congrArg (starRingEnd ℂ) (GaussCoframeCore.momentum_pair i g f)
  rw [GaussNativeForm.pair_conjugate, GaussNativeForm.pair_conjugate] at h
  exact h.symm

theorem term_pair (i j : Fin 6) (f g : QuantumTest) :
    sourcePair f (term i j g) = sourcePair (term j i f) g := by
  change sourcePair f (GaussCoframeCore.adjoint i
    (GaussNativeForm.multiply (coefficient i j) (coefficient_smooth i j) (GaussCoframeCore.momentum j g))) = _
  rw [adjoint_pair, GaussNativeForm.multiply_pair, GaussCoframeCore.momentum_pair]
  have hc : coefficient i j = coefficient j i := funext (coefficient_symmetric i j)
  unfold term
  simp only [LinearMap.comp_apply, hc]

def kinetic : QuantumTest →ₗ[ℂ] QuantumTest := ∑ i : Fin 6, ∑ j : Fin 6, term i j

theorem kinetic_pair (f g : QuantumTest) :
    sourcePair f (kinetic g) = sourcePair (kinetic f) g := by
  simp only [kinetic, LinearMap.sum_apply, sourcePair, map_sum, inner_sum, sum_inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact term_pair _ _ f g

#print axioms coefficient_smooth
#print axioms kinetic_pair
end LowEnergy.GaussCoframeKinetic
