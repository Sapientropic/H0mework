import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Consumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix BigOperators ComplexOrder
noncomputable section

def gamma : Matrix Basis Basis ℂ :=
  registeredState Reentry.Source.targetRealized

theorem gamma_hermitian : gamma.IsHermitian := by
  have source := Matrix.isHermitian_conjTranspose_mul_mul
    (star registeredComplexCoordinates) Reentry.Producer.targetRealized_hermitian
  simpa only [gamma,registeredState,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose] using source

def occupied (i : Basis) : Prop := 1 < gamma_hermitian.eigenvalues i
def mask (i : Basis) : ℂ := by
  classical
  exact if occupied i then 1 else 0
def diagonal : Matrix Basis Basis ℂ := Matrix.diagonal mask
def projector : Matrix Basis Basis ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix Basis Basis ℂ) gamma_hermitian.eigenvectorUnitary) diagonal

theorem diagonal_idempotent : diagonal * diagonal = diagonal := by
  ext i j
  simp only [diagonal,Matrix.diagonal_mul]
  by_cases h : occupied i
  · simp [mask,h,Matrix.diagonal_apply]
  · simp [mask,h,Matrix.diagonal_apply]

theorem projector_idempotent : projector * projector = projector := by
  unfold projector
  rw [← map_mul]
  rw [diagonal_idempotent]

theorem diagonal_positive : diagonal.PosSemidef := by
  classical
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  by_cases h : occupied i <;> simp [mask,h]

theorem projector_positive : projector.PosSemidef := by
  have positive := diagonal_positive.mul_mul_conjTranspose_same
    (gamma_hermitian.eigenvectorUnitary : Matrix Basis Basis ℂ)
  simpa only [projector,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using positive

def occupiedCount : ℕ := by
  classical
  exact (Finset.univ.filter occupied).card

theorem projector_trace : projector.trace = (occupiedCount : ℂ) := by
  classical
  let U : Matrix Basis Basis ℂ := gamma_hermitian.eigenvectorUnitary
  have unit : star U * U = 1 := (Unitary.mem_iff.mp gamma_hermitian.eigenvectorUnitary.property).1
  have cyclic : (U * diagonal * star U).trace = diagonal.trace := by
    calc
      _ = (star U * (U * diagonal)).trace := Matrix.trace_mul_comm _ _
      _ = diagonal.trace := by rw [← Matrix.mul_assoc,unit,Matrix.one_mul]
  rw [projector,Unitary.conjStarAlgAut_apply]
  change (U * diagonal * star U).trace = _
  rw [cyclic,diagonal,Matrix.trace_diagonal]
  simp [occupiedCount,mask]

def residual : Matrix Basis Basis ℂ := gamma - (2 : ℂ) • projector

def residualDiagonal : Matrix Basis Basis ℂ :=
  Matrix.diagonal (fun i => (gamma_hermitian.eigenvalues i : ℂ) - 2 * mask i)

theorem residual_spectral :
    residual =
      (Unitary.conjStarAlgAut ℂ (Matrix Basis Basis ℂ) gamma_hermitian.eigenvectorUnitary)
        residualDiagonal := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix Basis Basis ℂ) gamma_hermitian.eigenvectorUnitary
  have diagonal_difference :
      Matrix.diagonal (RCLike.ofReal ∘ gamma_hermitian.eigenvalues) -
        (2 : ℂ) • diagonal = residualDiagonal := by
    ext i j
    by_cases same : i = j <;> simp [diagonal,residualDiagonal,same]
  calc
    residual =
        e (Matrix.diagonal (RCLike.ofReal ∘ gamma_hermitian.eigenvalues)) -
          (2 : ℂ) • e diagonal := by
      have same := congrArg
        (fun M : Matrix Basis Basis ℂ => M - (2 : ℂ) • projector)
        gamma_hermitian.spectral_theorem
      simpa only [residual,projector] using same
    _ = e (Matrix.diagonal (RCLike.ofReal ∘ gamma_hermitian.eigenvalues) -
          (2 : ℂ) • diagonal) := by rw [map_sub,map_smul]
    _ = e residualDiagonal := by rw [diagonal_difference]

theorem gamma_projector_residual : gamma = (2 : ℂ) • projector + residual := by
  simp [residual]

theorem gamma_trace_account :
    gamma.trace = (2 : ℂ) * (occupiedCount : ℂ) + residual.trace := by
  have same := congrArg Matrix.trace gamma_projector_residual
  simpa only [Matrix.trace_add,Matrix.trace_smul,projector_trace,smul_eq_mul] using same

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
