import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.InteractionSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Quantum.PartialTraceCovariance

/-! # Source-fixed reversal of the PC exchange and the unchanged environment phase -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Recovery.Control

open Powered.Dynamics Load.Source Load.Producer.StrictThermal
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sign reversal of the interaction leaves a forward bare phase beside the inverse full flow. -/
theorem reverseInteraction_exp (B V : Matrix ι ι ℂ) (resonance : Commute B V) (t : ℝ) :
    NormedSpace.exp (t • (-Complex.I • (B - V))) =
      NormedSpace.exp ((2 * t) • (-Complex.I • B)) *
        NormedSpace.exp ((-t) • (-Complex.I • (B + V))) := by
  have commuting : Commute ((2 * t) • (-Complex.I • B))
      ((-t) • (-Complex.I • (B + V))) :=
    ((((Commute.refl B).add_right resonance).smul_left (-Complex.I)).smul_right
      (-Complex.I)).smul_left (2 * t) |>.smul_right (-t)
  have split : t • (-Complex.I • (B - V)) =
      (2 * t) • (-Complex.I • B) + (-t) • (-Complex.I • (B + V)) := by
    simp only [smul_sub, smul_add]
    module
  rw [split, Matrix.exp_add_of_commute _ _ commuting]

theorem reverseInteraction_factorization (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian)
    (resonance : Commute (bareHamiltonian H gap) V) (t : ℝ) :
    flowUnitary H gap (-V) hH hV.neg t =
      flowUnitary H gap 0 hH Matrix.isHermitian_zero (2 * t) *
        flowUnitary H gap V hH hV (-t) := by
  apply Subtype.ext
  change (flowUnitary H gap (-V) hH hV.neg t : ControllerJoint ι) =
    (flowUnitary H gap 0 hH Matrix.isHermitian_zero (2 * t) : ControllerJoint ι) *
      (flowUnitary H gap V hH hV (-t) : ControllerJoint ι)
  simp only [flowUnitary_matrix_exp, totalHamiltonian, add_zero, ← sub_eq_add_neg]
  exact reverseInteraction_exp (bareHamiltonian H gap) V resonance t

theorem bare_controller_energy (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (t : ℝ) (current : ControllerJoint ι) :
    controllerEnergy 2 (coupledNext H 2 0 hH Matrix.isHermitian_zero t current) =
      controllerEnergy 2 current := by
  rw [← environmentObservable_energy, ← environmentObservable_energy]
  apply energy_of_commuting_observable
  change Matrix.kronecker 1 (controllerHamiltonian 2) * totalHamiltonian H 2 0 =
    totalHamiltonian H 2 0 * Matrix.kronecker 1 (controllerHamiltonian 2)
  simp only [totalHamiltonian, bareHamiltonian, add_zero, Matrix.mul_add, Matrix.add_mul,
    Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem reverseInteraction_controller_energy (H : Matrix ι ι ℂ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian)
    (resonance : Commute (bareHamiltonian H 2) V) (t : ℝ) (current : ControllerJoint ι) :
    controllerEnergy 2 (coupledNext H 2 (-V) hH hV.neg t current) =
      controllerEnergy 2 (coupledNext H 2 V hH hV (-t) current) := by
  unfold coupledNext
  rw [reverseInteraction_factorization H 2 V hH hV resonance t,
    Unitary.conjStarAlgAut_mul_apply]
  exact bare_controller_energy H hH (2 * t) _

theorem reverseInteraction_inclusive_energy (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian)
    (resonance : Commute (bareHamiltonian H gap) V) (t : ℝ) (current : ControllerJoint ι) :
    Collision.energy (totalHamiltonian H gap V) (coupledNext H gap (-V) hH hV.neg t current) =
      Collision.energy (totalHamiltonian H gap V) current := by
  apply energy_of_commuting_observable
  change Commute (bareHamiltonian H gap + V) (bareHamiltonian H gap + -V)
  exact ((Commute.refl _).add_left resonance.symm).add_right
    ((resonance.add_left (Commute.refl V)).neg_right)

theorem reverseInteraction_interaction_energy (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian)
    (resonance : Commute (bareHamiltonian H gap) V) (t : ℝ) (current : ControllerJoint ι) :
    Collision.energy V (coupledNext H gap (-V) hH hV.neg t current) = Collision.energy V current :=
  energy_of_commuting_observable _ _ _ _ _ _ _ _
    (resonance.symm.add_right (Commute.refl V).neg_right)

def minimalPCUnitary (elapsed : ℝ) : Matrix.unitaryGroup PairController ℂ :=
  flowUnitary Work.Drive.fieldBaseline 2 (-Powered.Source.sourceInteraction)
    Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian.neg elapsed

theorem minimalPCUnitary_phase (elapsed : ℝ) :
    minimalPCUnitary elapsed =
      flowUnitary Work.Drive.fieldBaseline 2 0 Work.Drive.fieldBaseline_hermitian
        Matrix.isHermitian_zero (2 * elapsed) *
      flowUnitary Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
        Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian (-elapsed) :=
  reverseInteraction_factorization _ _ _ _ _ Powered.Producer.sourceResonance elapsed

theorem minimalPCUnitary_controller_energy (elapsed : ℝ) (current : Matrix PairController PairController ℂ) :
    controllerEnergy 2 (Unitary.conjStarAlgAut ℂ _ (minimalPCUnitary elapsed) current) =
      controllerEnergy 2 (Powered.Producer.sourceAdvance (-elapsed) current) :=
  reverseInteraction_controller_energy _ _ _ _ Powered.Producer.sourceResonance elapsed current

theorem minimalPCUnitary_inclusive_energy (elapsed : ℝ) (current : Matrix PairController PairController ℂ) :
    Collision.energy Powered.Producer.poweredTotalHamiltonian
      (Unitary.conjStarAlgAut ℂ _ (minimalPCUnitary elapsed) current) =
        Collision.energy Powered.Producer.poweredTotalHamiltonian current :=
  reverseInteraction_inclusive_energy Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
    Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian
    Powered.Producer.sourceResonance elapsed current

theorem minimalPCUnitary_interaction_energy (elapsed : ℝ) (current : Matrix PairController PairController ℂ) :
    Collision.energy Powered.Source.sourceInteraction
      (Unitary.conjStarAlgAut ℂ _ (minimalPCUnitary elapsed) current) =
        Collision.energy Powered.Source.sourceInteraction current :=
  reverseInteraction_interaction_energy Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
    Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian
    Powered.Producer.sourceResonance elapsed current

theorem recovery_duration_positive : 0 < 3 * (Propagation.Producer.nativeClockStep : ℝ) := by
  exact mul_pos (by norm_num) nativeClock_small.1

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

local instance : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _

private def tensorLeftRing : Matrix ι ι ℂ →+* Matrix (ι × κ) (ι × κ) ℂ :=
  { NonUnitalRingHomClass.toNonUnitalRingHom (tensorLeft (ι := ι) (κ := κ)) with
    map_one' := by change Matrix.kronecker (1 : Matrix ι ι ℂ) (1 : Matrix κ κ ℂ) = 1; simp [Matrix.kronecker] }

private def tensorRightRing : Matrix κ κ ℂ →+* Matrix (ι × κ) (ι × κ) ℂ :=
  { NonUnitalRingHomClass.toNonUnitalRingHom (tensorRight (ι := ι) (κ := κ)) with
    map_one' := by change Matrix.kronecker (1 : Matrix ι ι ℂ) (1 : Matrix κ κ ℂ) = 1; simp [Matrix.kronecker] }

theorem exp_tensor_sum (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    NormedSpace.exp (Matrix.kronecker A (1 : Matrix κ κ ℂ) + Matrix.kronecker (1 : Matrix ι ι ℂ) B) =
      Matrix.kronecker (NormedSpace.exp A) (NormedSpace.exp B) := by
  have commuting : Commute (Matrix.kronecker A (1 : Matrix κ κ ℂ)) (Matrix.kronecker (1 : Matrix ι ι ℂ) B) := by
    show _ * _ = _ * _
    simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have left : Matrix.kronecker (NormedSpace.exp A) (1 : Matrix κ κ ℂ) =
      NormedSpace.exp (Matrix.kronecker A (1 : Matrix κ κ ℂ)) := by
    apply NormedSpace.map_exp (tensorLeftRing (κ := κ)) _ A
    change Continuous (fun M : Matrix ι ι ℂ => fun (i j : ι × κ) => M i.1 j.1 * (1 : Matrix κ κ ℂ) i.2 j.2)
    fun_prop
  have right : Matrix.kronecker (1 : Matrix ι ι ℂ) (NormedSpace.exp B) =
      NormedSpace.exp (Matrix.kronecker (1 : Matrix ι ι ℂ) B) := by
    apply NormedSpace.map_exp (tensorRightRing (ι := ι)) _ B
    change Continuous (fun M : Matrix κ κ ℂ => fun (i j : ι × κ) => (1 : Matrix ι ι ℂ) i.1 j.1 * M i.2 j.2)
    fun_prop
  rw [Matrix.exp_add_of_commute _ _ commuting, ← left, ← right]
  simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

def environmentUnitary (elapsed : ℝ) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨NormedSpace.exp (elapsed • (-Complex.I • controllerHamiltonian 2)), by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    change star (elapsed • (-Complex.I • controllerHamiltonian 2)) =
      -(elapsed • (-Complex.I • controllerHamiltonian 2))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [controllerHamiltonian, Matrix.star_apply, Matrix.smul_apply, Complex.real_smul]⟩

theorem environmentUnitary_zero : environmentUnitary 0 = 1 := by
  apply Subtype.ext
  simp [environmentUnitary]

theorem environmentUnitary_add (elapsed next : ℝ) :
    environmentUnitary (elapsed + next) = environmentUnitary elapsed * environmentUnitary next := by
  apply Subtype.ext
  change NormedSpace.exp ((elapsed + next) • (-Complex.I • controllerHamiltonian 2)) = _
  rw [add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl (-Complex.I • controllerHamiltonian 2)).smul_left elapsed).smul_right next)]
  rfl

theorem environmentUnitary_commutes (elapsed : ℝ) :
    Commute (controllerHamiltonian 2) (environmentUnitary elapsed : Matrix (Fin 2) (Fin 2) ℂ) :=
  (((Commute.refl (controllerHamiltonian 2)).smul_right (-Complex.I)).smul_right elapsed).exp_right

theorem environmentUnitary_diagonal (elapsed : ℝ) :
    (environmentUnitary elapsed : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal (fun e => Complex.exp (-Complex.I * (elapsed : ℂ) * (environmentEnergies e : ℂ))) := by
  change NormedSpace.exp (elapsed • (-Complex.I • Matrix.diagonal ![0, (2 : ℂ)])) = _
  rw [← Matrix.diagonal_smul, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext e
  fin_cases e <;>
    simp [Pi.coe_exp, environmentEnergies, Complex.real_smul, ← Complex.exp_eq_exp_ℂ,
      mul_comm, mul_left_comm, mul_assoc]

theorem source_barePCE_factor (elapsed : ℝ) :
    flowUnitary Powered.Producer.poweredTotalHamiltonian 2 0
      Powered.Producer.poweredTotalHamiltonian_hermitian Matrix.isHermitian_zero elapsed =
    Load.Quantum.localUnitary
      (flowUnitary Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
        Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian elapsed)
      (environmentUnitary elapsed) := by
  apply Subtype.ext
  change (flowUnitary Powered.Producer.poweredTotalHamiltonian 2 0
    Powered.Producer.poweredTotalHamiltonian_hermitian Matrix.isHermitian_zero elapsed : LoadedJoint) =
    Matrix.kronecker (flowUnitary Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
      Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian elapsed :
        Matrix PairController PairController ℂ)
      (environmentUnitary elapsed : Matrix (Fin 2) (Fin 2) ℂ)
  rw [flowUnitary_matrix_exp, flowUnitary_matrix_exp]
  change NormedSpace.exp (elapsed • (-Complex.I •
      (bareHamiltonian Powered.Producer.poweredTotalHamiltonian 2 + 0))) =
    Matrix.kronecker (NormedSpace.exp (elapsed • (-Complex.I • Powered.Producer.poweredTotalHamiltonian)))
      (NormedSpace.exp (elapsed • (-Complex.I • controllerHamiltonian 2)))
  rw [add_zero]
  have split : elapsed • (-Complex.I • bareHamiltonian Powered.Producer.poweredTotalHamiltonian 2) =
      Matrix.kronecker (elapsed • (-Complex.I • Powered.Producer.poweredTotalHamiltonian)) 1 +
        Matrix.kronecker 1 (elapsed • (-Complex.I • controllerHamiltonian 2)) := by
    ext i j
    simp [bareHamiltonian, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Complex.real_smul]
    ring
  rw [split, exp_tensor_sum]

theorem source_barePCE_systemReduce (elapsed : ℝ) (joint : LoadedJoint) :
    systemReduce (coupledNext Powered.Producer.poweredTotalHamiltonian 2 0
      Powered.Producer.poweredTotalHamiltonian_hermitian Matrix.isHermitian_zero elapsed joint) =
      Powered.Producer.sourceAdvance elapsed (systemReduce joint) := by
  unfold coupledNext
  rw [source_barePCE_factor]
  exact Load.Quantum.systemReduce_local_conjugation _ _ joint

theorem source_barePCE_environmentReduce (elapsed : ℝ) (joint : LoadedJoint) :
    controllerReduce (coupledNext Powered.Producer.poweredTotalHamiltonian 2 0
      Powered.Producer.poweredTotalHamiltonian_hermitian Matrix.isHermitian_zero elapsed joint) =
      Unitary.conjStarAlgAut ℂ _ (environmentUnitary elapsed) (controllerReduce joint) := by
  unfold coupledNext
  rw [source_barePCE_factor]
  exact Load.Quantum.controllerReduce_local_conjugation _ _ joint

end

end LAlanine40K2025.Thermal.Load.Recovery.Control
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
