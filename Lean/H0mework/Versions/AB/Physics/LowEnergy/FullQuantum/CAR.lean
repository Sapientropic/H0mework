import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Evolution
import H0mework.Versions.AB.Physics.LowEnergyFermion.Source

/-! The original independent momentum gives a full, algebraic CAR evolution.
Its inverse creator is not relabelled as the Hilbert adjoint of the annihilator. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineHolonomicField
open YangMills.FullPairing StageNineCurrentCoframeMatterTemporalPrincipal
open QuantizationCheck.Fermion
open scoped Matrix
noncomputable section
attribute [local instance] Fermion.fullIndexOrder

def primalMatrix (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) : Matrix Quantum.Index Quantum.Index ℂ :=
  Quantum.operatorMatrix (primal C p k t)

theorem primalMatrix_inverse (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    primalMatrix C p k t * primalMatrix C p k (-t) = 1 := by
  rw [primalMatrix, primalMatrix, ← Quantum.matrix_composition]
  have inverse : (primal C p k t).comp (primal C p k (-t)) = 1 := by
    apply LinearMap.ext
    intro v
    change primal C p k t (primal C p k (-t) v) = v
    simpa only [neg_neg] using primal_inverse C p k (-t) v
  rw [inverse]
  exact Quantum.operatorMatrix.map_one

def annihilator (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (i : Quantum.Index) : Module.End ℂ (Fock Quantum.Index) :=
  Fermion.annihilationField (primalMatrix C p k t) i

def momentumCreator (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (i : Quantum.Index) : Module.End ℂ (Fock Quantum.Index) :=
  Fermion.creationField (primalMatrix C p k (-t)).conjTranspose i

theorem full_source_CAR (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (i j : Quantum.Index) :
    annihilator C p k t i * momentumCreator C p k t j +
      momentumCreator C p k t j * annihilator C p k t i =
      (if i=j then 1 else 0 : ℂ) • (1 : Module.End ℂ (Fock Quantum.Index)) := by
  rw [annihilator, momentumCreator, Fermion.field_car,
    Matrix.conjTranspose_conjTranspose, primalMatrix_inverse]
  rfl

def dualCreator (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (i : Quantum.Index) : Module.End ℂ (Fock Quantum.Index) :=
  (Complex.I / ((|(C.coframe p).det| : ℝ) : ℂ)) •
    Fermion.creationField ((primalMatrix C p k (-t) *
      Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse (C.coframe p))).conjTranspose) i

theorem original_dual_CAR (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (i j : Quantum.Index) :
    annihilator C p k t i * dualCreator C p k t j +
      dualCreator C p k t j * annihilator C p k t i =
      (Complex.I / ((|(C.coframe p).det| : ℝ) : ℂ) *
        Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse (C.coframe p)) i j) •
        (1 : Module.End ℂ (Fock Quantum.Index)) := by
  simp only [annihilator, dualCreator, mul_smul_comm, smul_mul_assoc, ← smul_add]
  rw [Fermion.field_car, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
    primalMatrix_inverse, Matrix.one_mul, smul_smul]

def quantumGenerator (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) : Module.End ℂ (Fock Quantum.Index) :=
  Fermion.quantize (Quantum.operatorMatrix (hamiltonian C p k))

theorem original_field_hamiltonian (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (i : Quantum.Index) :
    annihilator C p k t i * quantumGenerator C p k -
      quantumGenerator C p k * annihilator C p k t i =
      Fermion.annihilationField
        (primalMatrix C p k t * Quantum.operatorMatrix (hamiltonian C p k)) i :=
  Fermion.field_quantize _ _ i

theorem original_wave_derivative (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (v : DiracExteriorMatterCarrier) :
    HasDerivAt (fun time => Quantum.coordinates (primal C p k time v))
      ((-Complex.I) • (Quantum.operatorMatrix (hamiltonian C p k) *ᵥ
        Quantum.coordinates (primal C p k t v))) t := by
  let read : Hilbert →L[ℂ] (Quantum.Index → ℂ) :=
    (Quantum.coordinates.toLinearMap.comp naturalCoordinates.symm.toLinearMap).toContinuousLinearMap
  have generated := (read.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (primal_derivative C p k t v)
  have read_value (w : DiracExteriorMatterCarrier) :
      read (naturalCoordinates w) = Quantum.coordinates w := by simp [read]
  change HasDerivAt (fun time => read (naturalCoordinates (primal C p k time v)))
    (read (naturalCoordinates (drift C p k (primal C p k t v)))) t at generated
  have derivative := congrArg Quantum.coordinates
    (LinearMap.congr_fun (hamiltonian_drift C p k) (primal C p k t v))
  simp only [LinearMap.smul_apply, map_smul] at derivative
  rw [Quantum.matrix_action]
  rw [derivative]
  simpa only [read_value] using generated

theorem original_oneParticle_evolution (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (v : DiracExteriorMatterCarrier) :
    HasDerivAt (fun time => oneParticle (Quantum.coordinates (primal C p k time v)))
      ((-Complex.I) • secondQuantize (Quantum.operatorMatrix (hamiltonian C p k))
        (oneParticle (Quantum.coordinates (primal C p k t v)))) t :=
  Fermion.original_fock_schrodinger _ _ t (original_wave_derivative C p k t v)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum
