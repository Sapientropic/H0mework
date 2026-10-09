import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.PreparedReservoirTransfer
import H0mework.Chemistry.LAlanineThermalDynamics.SwapExponential
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Positive.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Population.Readout

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Extraction

open Collision Quantum Work.Capacity
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem swap_unitary_star (i j : ι) :
    star (permutationUnitary (Equiv.swap i j)) = permutationUnitary (Equiv.swap i j) := by
  apply Subtype.ext
  change ((Equiv.swap i j).permMatrix ℂ).conjTranspose = (Equiv.swap i j).permMatrix ℂ
  simp [Matrix.conjTranspose_permMatrix]

theorem extraction_star (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    star (Spectrum.extraction H hH) = Spectrum.extraction H hH := by
  simp only [Spectrum.extraction, star_mul, star_star, swap_unitary_star, mul_assoc]

theorem extraction_hermitian (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (Spectrum.extraction H hH : Matrix ι ι ℂ).IsHermitian :=
  congrArg Subtype.val (extraction_star H hH)

theorem extraction_square (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (Spectrum.extraction H hH : Matrix ι ι ℂ) *
      (Spectrum.extraction H hH : Matrix ι ι ℂ) = 1 := by
  have h := Unitary.coe_star_mul_self (Spectrum.extraction H hH)
  rw [← Unitary.coe_star, extraction_star] at h
  exact h

def controlHamiltonian (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (q : ℝ) :
    Matrix ι ι ℂ :=
  (Real.pi / (2 * q)) • (Spectrum.extraction H hH : Matrix ι ι ℂ)

theorem control_hermitian (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (q : ℝ) :
    (controlHamiltonian H hH q).IsHermitian := by
  exact (extraction_hermitian H hH).smul (show IsSelfAdjoint (Real.pi / (2 * q)) from rfl)

theorem pulse_at_clock (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (q : ℝ) (hq : q ≠ 0) :
    NormedSpace.exp ((-Complex.I * (q : ℂ)) • controlHamiltonian H hH q) =
      (-Complex.I) • (Spectrum.extraction H hH : Matrix ι ι ℂ) := by
  have input :
      (-Complex.I * (q : ℂ)) • controlHamiltonian H hH q =
      (-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
        (Spectrum.extraction H hH : Matrix ι ι ℂ) := by
    unfold controlHamiltonian
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
    field_simp
  rw [input]
  simpa using! Dynamics.exp_neg_I_smul_involution
    (Spectrum.extraction H hH : Matrix ι ι ℂ) (extraction_square H hH) (Real.pi / 2)

def pulse (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (q t : ℝ) :
    Matrix.unitaryGroup ι ℂ :=
  ⟨NormedSpace.exp ((-Complex.I * (t : ℂ)) • controlHamiltonian H hH q), by
    let : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    apply (control_hermitian H hH q).isSelfAdjoint.smul_mem_skewAdjoint
    change star (-Complex.I * (t : ℂ)) = -(-Complex.I * (t : ℂ))
    simp⟩

theorem pulse_clock_conjugation (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (q : ℝ) (hq : q ≠ 0) (rho : Matrix ι ι ℂ) :
    conjugation (pulse H hH q q) rho = conjugation (Spectrum.extraction H hH) rho := by
  change NormedSpace.exp ((-Complex.I * (q : ℂ)) • controlHamiltonian H hH q) * rho *
      star (NormedSpace.exp ((-Complex.I * (q : ℂ)) • controlHamiltonian H hH q)) = _
  rw [pulse_at_clock H hH q hq]
  simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp
  rfl

theorem pulse_commutes (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (q t : ℝ) :
    Commute (controlHamiltonian H hH q) (pulse H hH q t : Matrix ι ι ℂ) :=
  ((Commute.refl (controlHamiltonian H hH q)).smul_right (-Complex.I * (t : ℂ))).exp_right

theorem control_energy_conserved (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (q t : ℝ) :
    energy (controlHamiltonian H hH q) (conjugation (pulse H hH q t) rho) =
      energy (controlHamiltonian H hH q) rho :=
  PreparationEnergy.commuting_energy _ _ _ (pulse_commutes H hH q t)

def switchIn (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (q : ℝ) : ℝ :=
  energy (controlHamiltonian H hH q) rho - energy H rho

def switchOut (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (q : ℝ) : ℝ :=
  energy H rho - energy (controlHamiltonian H hH q) rho

theorem switch_work_actual (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (q t : ℝ) :
    switchIn H rho hH q + switchOut H (conjugation (pulse H hH q t) rho) hH q =
      energy H (conjugation (pulse H hH q t) rho) - energy H rho := by
  unfold switchIn switchOut
  rw [control_energy_conserved]
  ring

theorem switch_clock_work (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (q : ℝ) (hq : q ≠ 0) :
    switchIn H rho hH q + switchOut H (conjugation (pulse H hH q q) rho) hH q =
      -(energy H rho - energy H (conjugation (Spectrum.extraction H hH) rho)) := by
  rw [switch_work_actual, pulse_clock_conjugation H hH q hq]
  ring

omit [Nonempty ι] in
theorem lifted_exponential {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (z : ℂ) :
    NormedSpace.exp (z • Matrix.kronecker A (1 : Matrix κ κ ℂ)) =
      Matrix.kronecker (NormedSpace.exp (z • A)) (1 : Matrix κ κ ℂ) := by
  simpa only [Matrix.kronecker, Matrix.kronecker_zero, add_zero, NormedSpace.exp_zero,
    Matrix.smul_kronecker] using!
    Load.Recovery.Control.exp_tensor_sum (z • A) (0 : Matrix κ κ ℂ)

open scoped ComplexOrder MatrixOrder
open Load.Producer.StrictThermal

omit [Nonempty ι] in
private theorem real_diagonal_energy (d : ι → ℝ) (rho : Matrix ι ι ℂ) :
    energy (Matrix.diagonal (fun i => (d i : ℂ))) rho = ∑ i, d i * (rho i i).re := by
  simp [energy,Matrix.trace,Matrix.diag,Matrix.diagonal_mul,Complex.mul_re]

theorem extraction_energy_difference (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    energy H rho - energy H (conjugation (Spectrum.extraction H hH) rho) =
      ∑ i, (hH.eigenvalues i - hH.eigenvalues (Equiv.swap Spectrum.firstIndex Spectrum.lastIndex i)) *
        ((conjugation (star hH.eigenvectorUnitary) rho) i i).re := by
  let V := hH.eigenvectorUnitary
  have pulled : conjugation (star (Spectrum.extraction H hH)) H =
      conjugation V (Matrix.diagonal (fun i =>
        (hH.eigenvalues (Equiv.swap Spectrum.firstIndex Spectrum.lastIndex i) : ℂ))) := by
    rw [extraction_star]
    change Unitary.conjStarAlgAut ℂ _ (V * permutationUnitary (Equiv.swap Spectrum.firstIndex Spectrum.lastIndex) * star V) H = _
    rw [Unitary.conjStarAlgAut_mul_apply,Unitary.conjStarAlgAut_mul_apply]
    rw [hH.conjStarAlgAut_star_eigenvectorUnitary,permutationUnitary_diagonal]
    rfl
  have energy_frame (d : ι → ℂ) :
      energy (conjugation V (Matrix.diagonal d)) rho =
        energy (Matrix.diagonal d) (conjugation (star V) rho) := by
    have h : energy (Matrix.diagonal d) (conjugation (star V) rho) =
        energy (conjugation (star (star V)) (Matrix.diagonal d)) rho := energy_pullback _ _ _
    rw [star_star] at h
    exact h.symm
  have read : energy H (conjugation (Spectrum.extraction H hH) rho) =
      energy (conjugation (star (Spectrum.extraction H hH)) H) rho := energy_pullback _ _ _
  have spectral : H = conjugation V (Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))) := hH.spectral_theorem
  rw [read,pulled]
  conv_lhs => arg 1; arg 1; rw [spectral]
  rw [energy_frame,energy_frame,real_diagonal_energy,real_diagonal_energy,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem extraction_work_lower (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (positive : rho.PosSemidef) (normalized : rho.trace=1) :
    (hH.eigenvalues Spectrum.firstIndex-hH.eigenvalues Spectrum.lastIndex) *
      (2*energy (Spectrum.reservoirState H hH) rho-1) ≤
      energy H rho-energy H (conjugation (Spectrum.extraction H hH) rho) := by
  let A := conjugation (star hH.eigenvectorUnitary) rho
  let gap := hH.eigenvalues Spectrum.firstIndex-hH.eigenvalues Spectrum.lastIndex
  have hA : A.PosSemidef := conjugation_posSemidef _ _ positive
  have normalizedA : A.trace=1 := (conjugation_trace _ _).trans normalized
  have mass : ∑ i, (A i i).re=1 := by
    simpa only [Matrix.trace,Matrix.diag,Complex.re_sum,Complex.one_re] using congrArg Complex.re normalizedA
  have top : energy (Spectrum.reservoirState H hH) rho=(A Spectrum.firstIndex Spectrum.firstIndex).re := by
    have read := energy_pullback (Spectrum.basisPure (Spectrum.firstIndex (ι := ι))) rho
      (star hH.eigenvectorUnitary)
    simp only [star_star] at read
    change energy (Spectrum.basisPure Spectrum.firstIndex) A=energy (Spectrum.reservoirState H hH) rho at read
    rw [← read]
    simp [energy,Spectrum.basisPure,Matrix.trace,Matrix.diag,Matrix.diagonal_mul]
  have nonnegative : 0 ≤ gap := sub_nonneg.mpr (Spectrum.last_le_eigenvalue H hH _)
  have scalar (i : ι) :
      gap*(2*(if i=Spectrum.firstIndex then 1 else 0)-1) ≤
        hH.eigenvalues i-hH.eigenvalues (Equiv.swap Spectrum.firstIndex Spectrum.lastIndex i) := by
    by_cases hf : i=Spectrum.firstIndex
    · subst i
      norm_num [gap]
    · by_cases hl : i=Spectrum.lastIndex
      · subst i
        simp [hf,gap]
      · rw [Equiv.swap_apply_of_ne_of_ne hf hl]
        simp only [if_neg hf,mul_zero,zero_sub,sub_self,mul_neg,mul_one]
        exact neg_nonpos.mpr nonnegative
  have row (i : ι) := mul_le_mul_of_nonneg_right (scalar i)
    (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1
  have summed := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => row i)
  have lower : (∑ i, gap*(2*(if i=Spectrum.firstIndex then (1 : ℝ) else 0)-1)*(A i i).re) =
      gap*(2*(A Spectrum.firstIndex Spectrum.firstIndex).re-1) := by
    have entry (i : ι) : gap*(2*(if i=Spectrum.firstIndex then (1 : ℝ) else 0)-1)*(A i i).re =
        (2*gap)*(if i=Spectrum.firstIndex then (A i i).re else 0)-gap*(A i i).re := by
      split_ifs <;> ring
    simp_rw [entry]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_ite_eq',Finset.mem_univ,if_true,mass]
    ring
  rw [lower] at summed
  rw [extraction_energy_difference,top]
  exact summed


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Extraction

namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract
open Collision Quantum Resource Propagation.Producer Work.Capacity Load.Source
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def pcPulse (time : ℝ) : Matrix.unitaryGroup PairController ℂ :=
  Extraction.pulse Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian (nativeClockStep : ℝ) time

def pairPulse (time : ℝ) : Matrix.unitaryGroup (PairController × PairController) ℂ :=
  Quantum.localUnitary (pcPulse time) 1

def fullPulse (time : ℝ) : Matrix.unitaryGroup Current.FullIndex ℂ :=
  Load.Quantum.localUnitary (pairPulse time) 1

def pointerPulse (time : ℝ) : Matrix.unitaryGroup PointerIndex ℂ :=
  blockUnitary (fullPulse time) (fullPulse time)

def pcControlHamiltonian : Matrix PairController PairController ℂ :=
  Extraction.controlHamiltonian Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian (nativeClockStep : ℝ)

def pairControlHamiltonian : JointMatrix PairController :=
  Matrix.kronecker pcControlHamiltonian 1

def fullControlHamiltonian : Current.FullJoint := Matrix.kronecker pairControlHamiltonian 1

def pointerControlHamiltonian : PointerJoint :=
  Matrix.fromBlocks fullControlHamiltonian 0 0 fullControlHamiltonian

theorem pc_control_hermitian : pcControlHamiltonian.IsHermitian :=
  Extraction.control_hermitian _ _ _

theorem pair_control_hermitian : pairControlHamiltonian.IsHermitian := by
  unfold pairControlHamiltonian Matrix.IsHermitian
  dsimp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, pc_control_hermitian.eq, Matrix.conjTranspose_one]

theorem full_control_hermitian : fullControlHamiltonian.IsHermitian := by
  unfold fullControlHamiltonian Matrix.IsHermitian
  dsimp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, pair_control_hermitian.eq, Matrix.conjTranspose_one]

theorem pointer_control_hermitian : pointerControlHamiltonian.IsHermitian :=
  full_control_hermitian.fromBlocks (by simp) full_control_hermitian

theorem pair_pulse_exp (time : ℝ) : (pairPulse time : JointMatrix PairController) =
    NormedSpace.exp ((-Complex.I * (time : ℂ)) • pairControlHamiltonian) := by
  rw [pairControlHamiltonian, Extraction.lifted_exponential]
  rfl

theorem full_pulse_exp (time : ℝ) : (fullPulse time : Current.FullJoint) =
    NormedSpace.exp ((-Complex.I * (time : ℂ)) • fullControlHamiltonian) := by
  rw [fullControlHamiltonian, Extraction.lifted_exponential, ← pair_pulse_exp]
  rfl

theorem pointer_pulse_exp (time : ℝ) : (pointerPulse time : PointerJoint) =
    NormedSpace.exp ((-Complex.I * (time : ℂ)) • pointerControlHamiltonian) := by
  rw [pointerControlHamiltonian, Matrix.fromBlocks_smul, smul_zero, exp_fromBlocks_diagonal,
    ← full_pulse_exp]
  rfl

attribute [local irreducible] fullControlHamiltonian pointerControlHamiltonian

attribute [local irreducible] pointerPulse in
theorem pointer_control_conserved (time : ℝ) (rho : PointerJoint) :
    energy pointerControlHamiltonian (Quantum.conjugation (pointerPulse time) rho) =
      energy pointerControlHamiltonian rho := by
  have commutes : Commute pointerControlHamiltonian (pointerPulse time : PointerJoint) := by
    rw [pointer_pulse_exp]
    have generator : (-Complex.I * (time : ℂ)) • pointerControlHamiltonian =
        time • (-Complex.I • pointerControlHamiltonian) := by
      ext i j
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
      ring
    rw [generator]
    exact matrix_generator_commutes _ _
  simpa only [Quantum.conjugation_apply] using
    PreparationEnergy.commuting_energy pointerControlHamiltonian rho (pointerPulse time) commutes

def next (current : Live.State) : Live.State :=
  ⟨current.localClock + nativeClockStep, pointerPulse (nativeClockStep : ℝ) * current.action⟩

theorem next_joint (current : Live.State) : (next current).joint =
    Quantum.conjugation (pointerPulse (nativeClockStep : ℝ)) current.joint :=
  (Environment.conjugation_comp _ current.action sourceInitial).symm

def controlEnergy (current : Live.State) : ℝ := energy pointerControlHamiltonian current.joint
def switchInWork (current : Live.State) : ℝ := controlEnergy current - Live.baselineEnergy current
def switchOutWork (current : Live.State) : ℝ := Live.baselineEnergy current - controlEnergy current
def pulseWork (current : Live.State) : ℝ := switchInWork current + switchOutWork (next current)

theorem next_control_energy (current : Live.State) : controlEnergy (next current) = controlEnergy current := by
  rw [controlEnergy, next_joint]
  exact pointer_control_conserved _ _

theorem pulse_work_actual (current : Live.State) :
    pulseWork current = Live.baselineEnergy (next current) - Live.baselineEnergy current := by
  unfold pulseWork switchInWork switchOutWork
  rw [next_control_energy]
  ring

theorem full_pc (time : ℝ) (rho : Current.FullJoint) :
    pcMatrixOf (Quantum.conjugation (fullPulse time) rho) =
      Quantum.conjugation (pcPulse time) (pcMatrixOf rho) := by
  unfold pcMatrixOf
  rw [show Powered.Dynamics.systemReduce (Quantum.conjugation (fullPulse time) rho) =
      Quantum.conjugation (pairPulse time) (Powered.Dynamics.systemReduce rho) from
    Load.Quantum.systemReduce_local_conjugation _ _ _]
  exact Quantum.systemReduce_local_conjugation _ _ _

theorem pointer_body (time : ℝ) (rho : PointerJoint) :
    bodyRead (Quantum.conjugation (pointerPulse time) rho) =
      Quantum.conjugation (fullPulse time) (bodyRead rho) := by
  unfold bodyRead pointerPulse
  rw [controlled_block_left, controlled_block_right, map_add]

theorem next_pc (current : Live.State) :
    pcMatrixOf (bodyRead (next current).joint) =
      Quantum.conjugation Source.sourceExtraction (pcMatrixOf (bodyRead current.joint)) := by
  rw [next_joint, pointer_body, full_pc]
  exact Extraction.pulse_clock_conjugation _ _ _ (by exact_mod_cast nativeClockStep_positive.ne') _

theorem full_donor (time : ℝ) (rho : Current.FullJoint) :
    donorMatrixOf (Quantum.conjugation (fullPulse time) rho) = donorMatrixOf rho := by
  unfold donorMatrixOf
  rw [show Powered.Dynamics.systemReduce (Quantum.conjugation (fullPulse time) rho) =
      Quantum.conjugation (pairPulse time) (Powered.Dynamics.systemReduce rho) from
    Load.Quantum.systemReduce_local_conjugation _ _ _]
  change Collision.bathReduce (Quantum.localConjugation (pcPulse time) 1 _) = _
  rw [Quantum.bathReduce_local_conjugation]
  simp [Quantum.conjugation_apply]

theorem full_environment (time : ℝ) (rho : Current.FullJoint) :
    Powered.Dynamics.controllerReduce (Quantum.conjugation (fullPulse time) rho) =
      Powered.Dynamics.controllerReduce rho := by
  change Powered.Dynamics.controllerReduce (Load.Quantum.localConjugation (pairPulse time) 1 rho) = _
  rw [Load.Quantum.controllerReduce_local_conjugation]
  simp [Quantum.conjugation_apply]

theorem next_donor (current : Live.State) :
    donorMatrixOf (bodyRead (next current).joint) = donorMatrixOf (bodyRead current.joint) := by
  rw [next_joint, pointer_body, full_donor]

theorem next_environment (current : Live.State) :
    Powered.Dynamics.controllerReduce (bodyRead (next current).joint) =
      Powered.Dynamics.controllerReduce (bodyRead current.joint) := by
  rw [next_joint, pointer_body, full_environment]

theorem next_pointer (current : Live.State) :
    oneRead (next current).joint = oneRead current.joint := by
  rw [next_joint]
  exact blockUnitary_preserves_oneRead _ _ _

theorem next_remaining (current : Live.State) :
    donorRemainingOf (suppliedBlock (next current)) = donorRemainingOf (suppliedBlock current) := by
  have block : suppliedBlock (next current) =
      Quantum.conjugation (fullPulse (nativeClockStep : ℝ)) (suppliedBlock current) := by
    unfold suppliedBlock
    rw [next_joint]
    exact controlled_block_right _ _ _
  rw [block]
  unfold donorRemainingOf donorEnergyOf
  rw [full_donor, Quantum.conjugation_trace]

def extractedPCWork (current : Live.State) : ℝ :=
  pcEnergyOf (bodyRead current.joint) - pcEnergyOf (bodyRead (next current).joint)

theorem pc_work_source (current : Live.State) : extractedPCWork current =
    energy Powered.Producer.poweredTotalHamiltonian (pcMatrixOf (bodyRead current.joint)) -
      energy Powered.Producer.poweredTotalHamiltonian
        (Quantum.conjugation Source.sourceExtraction (pcMatrixOf (bodyRead current.joint))) := by
  unfold extractedPCWork pcEnergyOf
  rw [next_pc]

theorem pulse_work_resources (current : Live.State) :
    pulseWork current = -extractedPCWork current +
      (boundaryEnergyOf (bodyRead (next current).joint) - boundaryEnergyOf (bodyRead current.joint)) := by
  rw [pulse_work_actual, current_total, current_total]
  unfold donorEnergyOf environmentEnergyOf pointerEnergy extractedPCWork
  rw [next_donor, next_environment, next_pointer]
  ring

theorem next_net_account (current : Live.State) :
    (Live.freeEnergy (next current) - Live.freeEnergy current) +
      (Live.entropyProduction (next current) - Live.entropyProduction current) = pulseWork current := by
  rw [pulse_work_actual]
  linarith only [Live.complete_account current, Live.complete_account (next current)]

def rho11 : Matrix PairController PairController ℂ := pcMatrixOf (bodyRead Weak.execution.joint)

attribute [local irreducible] Weak.execution

theorem original_pc_target :
    pcMatrixOf (bodyRead (next Weak.execution).joint) = Quantum.conjugation Source.sourceExtraction rho11 :=
  next_pc Weak.execution

theorem original_spectral_gap : (36/5 : ℝ) <
    Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues (Spectrum.firstIndex (ι := PairController))-
      Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues (Spectrum.lastIndex (ι := PairController)) := by
  have source := Source.donor_received_gap
  have lower := (Spectrum.energy_spectral_bounds Powered.Producer.poweredTotalHamiltonian
    (Load.Producer.RecoveryLedger.pcRead Source.received).joint Powered.Producer.poweredTotalHamiltonian_hermitian
    (Load.Producer.RecoveryLedger.pcRead Source.received).positive (Load.Producer.RecoveryLedger.pcRead Source.received).normalized).1
  change (36/5 : ℝ) < energy Powered.Producer.poweredTotalHamiltonian
    (Spectrum.spectralPure _ _ Spectrum.firstIndex)-energy Powered.Producer.poweredTotalHamiltonian
      (Load.Producer.RecoveryLedger.pcRead Source.received).joint at source
  rw [Spectrum.spectralPure_energy] at source
  linarith only [source,lower]

theorem original_pc_work_lower : (17/5 : ℝ) < extractedPCWork Weak.execution := by
  have work := Extraction.extraction_work_lower Powered.Producer.poweredTotalHamiltonian rho11
    Powered.Producer.poweredTotalHamiltonian_hermitian
    Blocks.EnergyFrame.Inverse.Scaled.Finite.Population.rho11_positive
    Blocks.EnergyFrame.Inverse.Scaled.Finite.Population.rho11_trace
  have population := Blocks.EnergyFrame.Inverse.Scaled.Finite.Population.original_top_population_lower
  change (738/1000 : ℝ) < energy Source.donor rho11 at population
  change _ * (2*energy Source.donor rho11-1) ≤ _ at work
  rw [pc_work_source]
  change (17/5 : ℝ) < energy Powered.Producer.poweredTotalHamiltonian rho11-
    energy Powered.Producer.poweredTotalHamiltonian (conjugation Source.sourceExtraction rho11)
  change _ ≤ energy Powered.Producer.poweredTotalHamiltonian rho11-
    energy Powered.Producer.poweredTotalHamiltonian (conjugation Source.sourceExtraction rho11) at work
  nlinarith only [work,population,original_spectral_gap]

open Blocks.EnergyFrame Blocks.EnergyFrame.Inverse Blocks.EnergyFrame.Inverse.Scaled.Finite Load.Producer.StrictThermal
open scoped ComplexOrder MatrixOrder

theorem boundary_read_bound (current : Live.State) :
    |boundaryEnergyOf (bodyRead current.joint)| ≤ (1 : ℝ) := by
  have read := block_energy_split Physical.boundaryHamiltonian 0 current.joint
  simp only [Complex.ofReal_zero,zero_smul,add_zero,zero_mul] at read
  change energy (pointerDiagonal Physical.boundaryHamiltonian) current.joint =
    energy Physical.boundaryHamiltonian (bodyRead current.joint) at read
  have bound := energy_abs_le_norm (pointerDiagonal Physical.boundaryHamiltonian) current.joint
    current.positive current.normalized
  rw [read] at bound
  have observableNorm : ‖pointerDiagonal Physical.boundaryHamiltonian‖ ≤ (1 : ℝ) :=
    (Post.diagonal_norm_le _).trans
      ((Blocks.EnergyFrame.body_observable_norm loadInteraction).trans actual_load_interaction_norm)
  exact bound.trans observableNorm

theorem boundary_difference_bound (current : Live.State) :
    |boundaryEnergyOf (bodyRead (next current).joint)-boundaryEnergyOf (bodyRead current.joint)| ≤ (2 : ℝ) := by
  have triangle := abs_sub (boundaryEnergyOf (bodyRead (next current).joint))
    (boundaryEnergyOf (bodyRead current.joint))
  linarith only [triangle,boundary_read_bound current,boundary_read_bound (next current)]

theorem original_net_output_lower : (7/5 : ℝ) < -pulseWork Weak.execution := by
  have boundary := (abs_le.mp (boundary_difference_bound Weak.execution)).2
  rw [pulse_work_resources]
  linarith only [boundary,original_pc_work_lower]

theorem original_capacity_lower : (17/5 : ℝ) <
    ergotropy Powered.Producer.poweredTotalHamiltonian rho11
      Powered.Producer.poweredTotalHamiltonian_hermitian Population.rho11_positive.isHermitian := by
  have upper := extractedWork_le_ergotropy Powered.Producer.poweredTotalHamiltonian rho11
    Powered.Producer.poweredTotalHamiltonian_hermitian Population.rho11_positive.isHermitian Source.sourceExtraction
  have lower := original_pc_work_lower
  rw [pc_work_source] at lower
  exact lower.trans_le upper

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
