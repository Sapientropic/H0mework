import Mathlib.Algebra.Module.ZLattice.Summable
import H0mework.NavierStokes.InitialData.RawSourceCore

/-!
# Three-dimensional integer-lattice critical kernel

This module identifies the repository frequency carrier
`IntegerWavevector = Fin 3 → ℤ` with the standard integer lattice inside
three-dimensional Euclidean space.  Mathlib's lattice `p`-series theorem then
gives summability of

```text
(integerWaveNormSq wave)⁻² = ‖wave‖₂⁻⁴.
```

The zero frequency contributes `0` under Lean's total inverse.  Consequently
the finite-sum bound below needs no cutoff, cardinality, shell-coverage, or
zero-exclusion certificate.  This is a lattice-kernel estimate; it does not
generate a Navier--Stokes trajectory or a continuation bound.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalIntegerLatticeCriticalKernel

open scoped BigOperators

open Module
open Submodule
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore

noncomputable section

/-! ## Standard integer lattice in Euclidean three-space -/

/-- Euclidean realization of the three integer frequency coordinates. -/
abbrev IntegerWaveEuclideanSpace := EuclideanSpace ℝ Coordinate

/-- The standard coordinate basis of the Euclidean frequency realization. -/
noncomputable def integerWaveEuclideanBasis :
    Basis Coordinate ℝ IntegerWaveEuclideanSpace :=
  (EuclideanSpace.basisFun Coordinate ℝ).toBasis

/-- The standard integer lattice spanned by the Euclidean coordinate basis. -/
noncomputable def integerWaveZLattice :
    Submodule ℤ IntegerWaveEuclideanSpace :=
  Submodule.span ℤ (Set.range integerWaveEuclideanBasis)

noncomputable instance : DiscreteTopology integerWaveZLattice := by
  unfold integerWaveZLattice
  infer_instance

/-- The coordinate basis, now regarded as a `ℤ`-basis of the integer lattice. -/
noncomputable def integerWaveZLatticeBasis :
    Basis Coordinate ℤ integerWaveZLattice :=
  integerWaveEuclideanBasis.restrictScalars ℤ

/-- Coordinatewise identification of repository frequencies with the standard lattice. -/
noncomputable def integerWaveToZLattice :
    IntegerWavevector ≃ₗ[ℤ] integerWaveZLattice :=
  integerWaveZLatticeBasis.equivFun.symm

@[simp] theorem integerWaveToZLattice_coe_apply
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    ((integerWaveToZLattice wave : integerWaveZLattice) :
        IntegerWaveEuclideanSpace) coordinate =
      (wave coordinate : ℝ) := by
  have latticeCoordinate :
      (integerWaveEuclideanBasis.restrictScalars ℤ).repr
          (integerWaveToZLattice wave) coordinate =
        wave coordinate := by
    change
      (integerWaveZLatticeBasis.equivFun
        (integerWaveZLatticeBasis.equivFun.symm wave)) coordinate =
      wave coordinate
    exact congrFun
      (integerWaveZLatticeBasis.equivFun.apply_symm_apply wave) coordinate
  have castCoordinate :=
    integerWaveEuclideanBasis.restrictScalars_repr_apply ℤ
      (integerWaveToZLattice wave) coordinate
  calc
    ((integerWaveToZLattice wave : integerWaveZLattice) :
        IntegerWaveEuclideanSpace) coordinate =
        integerWaveEuclideanBasis.repr
          (integerWaveToZLattice wave : integerWaveZLattice) coordinate := by
            simp [integerWaveEuclideanBasis, EuclideanSpace.basisFun_repr]
    _ = algebraMap ℤ ℝ
          ((integerWaveEuclideanBasis.restrictScalars ℤ).repr
            (integerWaveToZLattice wave) coordinate) := by
          exact castCoordinate.symm
    _ = (wave coordinate : ℝ) := by
          rw [latticeCoordinate]
          rfl

/-- The lattice norm is exactly the repository squared Euclidean frequency norm. -/
theorem integerWaveToZLattice_norm_sq
    (wave : IntegerWavevector) :
    ‖integerWaveToZLattice wave‖ ^ 2 =
      integerWaveNormSq wave := by
  change
    ‖((integerWaveToZLattice wave : integerWaveZLattice) :
        IntegerWaveEuclideanSpace)‖ ^ 2 =
      integerWaveNormSq wave
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [integerWaveNormSq]

/-- The standard integer frequency lattice has rank three. -/
@[simp] theorem integerWaveZLattice_finrank :
    Module.finrank ℤ integerWaveZLattice = 3 := by
  rw [Module.finrank_eq_card_basis integerWaveZLatticeBasis]
  rfl

/-! ## Critical kernel and global summability -/

/--
The three-dimensional critical lattice kernel.  At a nonzero frequency this
is `‖wave‖₂⁻⁴`; at zero it is definitionally `0`.
-/
def integerWaveCriticalKernel (wave : IntegerWavevector) : ℝ :=
  (integerWaveNormSq wave)⁻¹ ^ 2

theorem integerWaveCriticalKernel_nonneg
    (wave : IntegerWavevector) :
    0 ≤ integerWaveCriticalKernel wave := by
  exact sq_nonneg _

@[simp] theorem integerWaveCriticalKernel_zero :
    integerWaveCriticalKernel 0 = 0 := by
  simp [integerWaveCriticalKernel]

theorem integerWaveCriticalKernel_eq_lattice_inv_pow
    (wave : IntegerWavevector) :
    integerWaveCriticalKernel wave =
      ‖integerWaveToZLattice wave‖⁻¹ ^ 4 := by
  unfold integerWaveCriticalKernel
  rw [← integerWaveToZLattice_norm_sq, ← inv_pow, ← pow_mul]

/--
The critical kernel is summable over every integer frequency in three
dimensions.  The strict exponent inequality `3 < 4` is discharged internally.
-/
theorem summable_integerWaveCriticalKernel :
    Summable integerWaveCriticalKernel := by
  have latticeSummable :
      Summable (fun point : integerWaveZLattice => ‖point‖⁻¹ ^ 4) :=
    ZLattice.summable_norm_pow_inv integerWaveZLattice 4 (by
      rw [integerWaveZLattice_finrank]
      norm_num)
  rw [← integerWaveToZLattice.toEquiv.summable_iff] at latticeSummable
  exact latticeSummable.congr fun wave =>
    (integerWaveCriticalKernel_eq_lattice_inv_pow wave).symm

/--
Every finite collection of integer frequencies is bounded by the global
critical lattice sum.  The result is stronger than the zero-excluded form:
the zero term vanishes, so no exclusion premise is required.
-/
theorem finite_sum_integerWaveCriticalKernel_le_tsum
    (waves : Finset IntegerWavevector) :
    ∑ wave ∈ waves, integerWaveCriticalKernel wave ≤
      ∑' wave : IntegerWavevector, integerWaveCriticalKernel wave := by
  exact Summable.sum_le_tsum waves
    (fun wave _ => integerWaveCriticalKernel_nonneg wave)
    summable_integerWaveCriticalKernel

end

end ThreeDimensionalIntegerLatticeCriticalKernel
end NavierStokes
end SaturationMonoid
