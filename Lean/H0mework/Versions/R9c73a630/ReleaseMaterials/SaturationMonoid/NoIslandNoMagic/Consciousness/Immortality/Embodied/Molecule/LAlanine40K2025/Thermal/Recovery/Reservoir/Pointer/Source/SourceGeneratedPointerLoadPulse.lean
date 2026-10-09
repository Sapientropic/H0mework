import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Source.SourceGeneratedPointerEffect
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerFreeContinuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.SourceGeneratedReservoirHamiltonians

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open scoped Matrix ComplexOrder Matrix.Norms.Operator
noncomputable section

section Incidence
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem tensor_hermitian (A : Matrix ι ι ℂ) (D : Matrix κ κ ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) : (Matrix.kronecker A D).IsHermitian := by
  change (Matrix.kronecker A D)ᴴ = _
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, hA.eq, hD.eq]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem bodyObservable_hermitian (O : Matrix (ι × κ) (ι × κ) ℂ) (hermitian : O.IsHermitian) :
    (Incidence.bodyObservable O).IsHermitian :=
  (tensor_hermitian O 1 hermitian Matrix.isHermitian_one).submatrix _

omit [Fintype ι] [Fintype κ] in
theorem donorObservable_hermitian (O : Matrix ι ι ℂ) (hermitian : O.IsHermitian) :
    (Incidence.donorObservable (κ := κ) O).IsHermitian :=
  tensor_hermitian _ 1 (tensor_hermitian 1 O Matrix.isHermitian_one hermitian) Matrix.isHermitian_one
end Incidence

theorem oldBaseline_hermitian : Physical.baselineHamiltonian.IsHermitian :=
  (bodyObservable_hermitian _ Load.Source.loadTotalHamiltonian_hermitian).add
    (donorObservable_hermitian _ Powered.Producer.poweredTotalHamiltonian_hermitian)

attribute [local irreducible] Physical.baselineHamiltonian Current.loadPulse

def freePhase (time : ℝ) : unitary ℂ :=
  ⟨NormedSpace.exp (-Complex.I * 2 * (time : ℂ)), by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp only [star_mul, star_neg, Complex.star_def, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring⟩

def loadPulse (time : ℝ) : Matrix.unitaryGroup (Current.FullIndex ⊕ Current.FullIndex) ℂ :=
  blockUnitary (Current.loadPulse time) (freePhase time • Current.loadPulse time)

def baselineHamiltonian : Matrix (Current.FullIndex ⊕ Current.FullIndex) (Current.FullIndex ⊕ Current.FullIndex) ℂ :=
  Matrix.fromBlocks Physical.baselineHamiltonian 0 0 (Physical.baselineHamiltonian + (2 : ℂ) • 1)

theorem baselineHamiltonian_hermitian : baselineHamiltonian.IsHermitian :=
  oldBaseline_hermitian.fromBlocks (by simp)
    (oldBaseline_hermitian.add (Matrix.isHermitian_one.smul (by simp)))

section Exponential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exp_scalar_shift (A : Matrix ι ι ℂ) (c : ℂ) :
    NormedSpace.exp (A + c • 1) = NormedSpace.exp c • NormedSpace.exp A := by
  have scalar : NormedSpace.exp (c • (1 : Matrix ι ι ℂ)) = NormedSpace.exp c • 1 := by
    have raw := NormedSpace.map_exp (algebraMap ℂ (Matrix ι ι ℂ)) (continuous_algebraMap _ _) c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at raw
    exact raw.symm
  rw [Matrix.exp_add_of_commute A (c • 1) ((Commute.one_right A).smul_right c),
    scalar, Matrix.mul_smul, Matrix.mul_one]

omit [Fintype ι] in
theorem shifted_generator (A : Matrix ι ι ℂ) (time : ℝ) :
    time • (-Complex.I • (A + (2 : ℂ) • 1)) =
      time • (-Complex.I • A) + (-Complex.I * 2 * (time : ℂ)) • 1 := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem shifted_exponential (A : Matrix ι ι ℂ) (time : ℝ) :
    NormedSpace.exp (time • (-Complex.I • (A + (2 : ℂ) • 1))) =
      (freePhase time : ℂ) • NormedSpace.exp (time • (-Complex.I • A)) := by
  rw [shifted_generator, exp_scalar_shift]
  rfl

theorem blockUnitary_preserves_zeroRead (U V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    zeroRead ((blockUnitary U V : Matrix _ _ ℂ) * joint * star (blockUnitary U V : Matrix _ _ ℂ)) =
      zeroRead joint := by
  have block := blockUnitary_conjugation_diagonal_left U V joint
  exact (congrArg (fun A : Matrix ι ι ℂ => A.trace.re) block).trans
    (congrArg Complex.re (Quantum.unitary_conjugate_trace joint.toBlocks₁₁ U))

theorem blockUnitary_preserves_oneRead (U V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    oneRead ((blockUnitary U V : Matrix _ _ ℂ) * joint * star (blockUnitary U V : Matrix _ _ ℂ)) =
      oneRead joint := by
  have block := blockUnitary_conjugation_diagonal_right U V joint
  exact (congrArg (fun A : Matrix ι ι ℂ => A.trace.re) block).trans
    (congrArg Complex.re (Quantum.unitary_conjugate_trace joint.toBlocks₂₂ V))
end Exponential

theorem loadPulse_baseline (time : ℝ) :
    (loadPulse time : Matrix (Current.FullIndex ⊕ Current.FullIndex) (Current.FullIndex ⊕ Current.FullIndex) ℂ) =
      NormedSpace.exp (time • (-Complex.I • baselineHamiltonian)) := by
  have generator : time • (-Complex.I • baselineHamiltonian) =
      Matrix.fromBlocks (time • (-Complex.I • Physical.baselineHamiltonian)) 0 0
        (time • (-Complex.I • (Physical.baselineHamiltonian + (2 : ℂ) • 1))) := by
    simp only [baselineHamiltonian, Matrix.fromBlocks_smul, smul_zero]
  rw [generator, exp_fromBlocks_diagonal, shifted_exponential, ← Physical.loadPulse_baseline]
  rfl

theorem loadPulse_bodyRead (time : ℝ)
    (joint : Matrix (Current.FullIndex ⊕ Current.FullIndex) (Current.FullIndex ⊕ Current.FullIndex) ℂ) :
    bodyRead ((loadPulse time : Matrix _ _ ℂ) * joint * star (loadPulse time : Matrix _ _ ℂ)) =
      (Current.loadPulse time : Current.FullJoint) * bodyRead joint * star (Current.loadPulse time : Current.FullJoint) :=
  blockUnitary_common_phase_body (Current.loadPulse time) (freePhase time) joint

theorem loadPulse_zeroRead (time : ℝ)
    (joint : Matrix (Current.FullIndex ⊕ Current.FullIndex) (Current.FullIndex ⊕ Current.FullIndex) ℂ) :
    zeroRead ((loadPulse time : Matrix _ _ ℂ) * joint * star (loadPulse time : Matrix _ _ ℂ)) = zeroRead joint :=
  blockUnitary_preserves_zeroRead (Current.loadPulse time) (freePhase time • Current.loadPulse time) joint

theorem loadPulse_oneRead (time : ℝ)
    (joint : Matrix (Current.FullIndex ⊕ Current.FullIndex) (Current.FullIndex ⊕ Current.FullIndex) ℂ) :
    oneRead ((loadPulse time : Matrix _ _ ℂ) * joint * star (loadPulse time : Matrix _ _ ℂ)) = oneRead joint :=
  blockUnitary_preserves_oneRead (Current.loadPulse time) (freePhase time • Current.loadPulse time) joint

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
