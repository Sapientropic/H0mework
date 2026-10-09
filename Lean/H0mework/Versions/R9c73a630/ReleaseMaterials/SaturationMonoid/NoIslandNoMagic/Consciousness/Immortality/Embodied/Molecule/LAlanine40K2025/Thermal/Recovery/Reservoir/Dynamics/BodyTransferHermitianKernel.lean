import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.BodyTransferDiagonalKernel
import H0mework.Chemistry.LAlanineEntropy.PartialTraceCovariance
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel

open Collision Quantum
open scoped Matrix
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem systemNext_covariance (U : Matrix.unitaryGroup ι ℂ) (rho tau : SystemMatrix ι) (c s : ℝ) :
    conjugation U (systemNext rho tau c s) = systemNext (conjugation U rho) (conjugation U tau) c s := by
  let F := Unitary.conjStarAlgAut ℂ (SystemMatrix ι) U
  change F (systemNext rho tau c s) = systemNext (F rho) (F tau) c s
  have trace (M : SystemMatrix ι) : (F M).trace = M.trace := conjugation_trace U M
  rw [systemNext_full, systemNext_full]
  simp only [map_add, map_smul, map_sub, map_mul, trace]

theorem systemNext_hermitian_injective (tau : SystemMatrix ι) (hermitian : tau.IsHermitian) (normalized : tau.trace = 1)
    (c s : ℝ) (circle : c ^ 2 + s ^ 2 = 1) (nonzero : c ≠ 0) :
    Function.Injective (fun rho : SystemMatrix ι => systemNext rho tau c s) := by
  let U := star hermitian.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut ℂ (SystemMatrix ι) U
  have diagonal : F tau = Matrix.diagonal (fun i => (hermitian.eigenvalues i : ℂ)) :=
    hermitian.conjStarAlgAut_star_eigenvectorUnitary
  have trace : (Matrix.diagonal (fun i => (hermitian.eigenvalues i : ℂ))).trace = 1 := by
    rw [← diagonal]
    exact (conjugation_trace U tau).trans normalized
  intro left right same
  apply F.injective
  apply systemNext_diagonal_injective hermitian.eigenvalues c s trace circle nonzero
  have read := congrArg F same
  have covariance (rho : SystemMatrix ι) :
      F (systemNext rho tau c s) = systemNext (F rho) (F tau) c s := systemNext_covariance U rho tau c s
  rw [covariance, covariance, diagonal] at read
  exact read

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
