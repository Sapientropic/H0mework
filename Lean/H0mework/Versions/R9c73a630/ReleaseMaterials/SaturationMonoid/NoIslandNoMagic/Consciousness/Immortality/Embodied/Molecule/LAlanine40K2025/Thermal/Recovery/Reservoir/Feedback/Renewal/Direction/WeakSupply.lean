import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Consumers

/-! # Fixed unit-coupling supply and load from the actual nine-q resource current

The registered unit exchange coupling acts for the original positive q on the retained PC-R-E-pointer
joint. The full generated target is passed to the original load. Payment is exact, and the sign is
exposed as a source-only energy/coherence coordinate. Positive gain and active runtime installation
are separate return obligations; neither is assumed by this source candidate.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak

open Collision Resource Propagation.Producer Load.Source Load.Producer.StrictThermal Work.Capacity
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

/-- The existing registered unit coupling, at the physical duration of the source action. -/
def pairPulse (time : ℝ) : Matrix.unitaryGroup (PairController × PairController) ℂ :=
  Dynamics.pairUnitary Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian LAlanine40K2025.Thermal.Source.pairCoupling time

theorem pair_factor (time : ℝ) : pairPulse time =
    Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time) *
      Exchange.exchangeUnitary time := by
  apply Subtype.ext
  change Dynamics.pairPropagatorMatrix Powered.Producer.poweredTotalHamiltonian 1 time =
    Matrix.kronecker (Native.freePCUnitary time : Matrix PairController PairController ℂ)
      (Native.freePCUnitary time : Matrix PairController PairController ℂ) *
      partialSwap (Real.cos time) (Real.sin time)
  rw [Dynamics.pairPropagatorMatrix_factorization, one_mul]
  congr 1
  have split : (-Complex.I * (time : ℂ)) • Dynamics.freePairH Powered.Producer.poweredTotalHamiltonian =
      Matrix.kronecker (time • (-Complex.I • Powered.Producer.poweredTotalHamiltonian)) 1 +
        Matrix.kronecker 1 (time • (-Complex.I • Powered.Producer.poweredTotalHamiltonian)) := by
    ext i j
    simp [Dynamics.freePairH, jointHamiltonian, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.smul_apply, Complex.real_smul]
    ring
  rw [split, Load.Recovery.Control.exp_tensor_sum]
  simp only [Native.freePCUnitary, flowUnitary_matrix_exp]
  rfl

def fullPulse (time : ℝ) : Matrix.unitaryGroup Current.FullIndex ℂ :=
  Load.Quantum.localUnitary (pairPulse time) (Load.Recovery.Control.environmentUnitary time)

def pointerPulse (time : ℝ) : Matrix.unitaryGroup PointerIndex ℂ :=
  blockUnitary (Current.loadPulse time) (freePhase time • fullPulse time)

def next (current : Live.State) : Live.State :=
  ⟨current.localClock + nativeClockStep, pointerPulse (nativeClockStep : ℝ) * current.action⟩

/-- The complete current already delivered by the original nine-q execution. -/
def origin : Live.State := executed
def target : Live.State := next origin
def execution : Live.State := Live.loadNext target

theorem next_joint (current : Live.State) : (next current).joint =
    Quantum.conjugation (pointerPulse (nativeClockStep : ℝ)) current.joint :=
  (Environment.conjugation_comp _ current.action sourceInitial).symm

theorem next_block (current : Live.State) : suppliedBlock (next current) =
    Quantum.conjugation (fullPulse (nativeClockStep : ℝ)) (suppliedBlock current) := by
  unfold suppliedBlock
  rw [next_joint]
  change (Quantum.conjugation (blockUnitary (Current.loadPulse (nativeClockStep : ℝ))
    (freePhase (nativeClockStep : ℝ) • fullPulse (nativeClockStep : ℝ))) current.joint).toBlocks₂₂ = _
  rw [controlled_block_right]
  exact unitPhase_conjugation _ _ _

theorem full_pair (time : ℝ) (rho : Current.FullJoint) :
    Powered.Dynamics.systemReduce (Quantum.conjugation (fullPulse time) rho) =
      Quantum.conjugation (pairPulse time) (Powered.Dynamics.systemReduce rho) :=
  Load.Quantum.systemReduce_local_conjugation _ _ _

theorem pair_pc_energy (time : ℝ) (rho : JointMatrix PairController) :
    energy Powered.Producer.poweredTotalHamiltonian (systemReduce (Quantum.conjugation (pairPulse time) rho)) =
      energy Powered.Producer.poweredTotalHamiltonian
        (systemReduce (Quantum.conjugation (Exchange.exchangeUnitary time) rho)) := by
  rw [pair_factor]
  change energy Powered.Producer.poweredTotalHamiltonian
    (systemReduce (Unitary.conjStarAlgAut ℂ _
      (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time) *
        Exchange.exchangeUnitary time) rho)) = _
  rw [Unitary.conjStarAlgAut_mul_apply]
  change energy Powered.Producer.poweredTotalHamiltonian
    (systemReduce (Quantum.localConjugation (Native.freePCUnitary time) (Native.freePCUnitary time)
      (Quantum.conjugation (Exchange.exchangeUnitary time) rho))) = _
  rw [Quantum.systemReduce_local_conjugation, Native.freePC_energy]

def pairAtNine : JointMatrix PairController := Powered.Dynamics.systemReduce (suppliedBlock origin)
def gapAtNine : ℝ := donorEnergyOf (suppliedBlock origin) - pcEnergyOf (suppliedBlock origin)
def coherenceAtNine : ℝ := coherence Powered.Producer.poweredTotalHamiltonian pairAtNine
def transfer : ℝ := pcEnergyOf (suppliedBlock target) - pcEnergyOf (suppliedBlock origin)
/-- The raw source coordinate whose strict sign settles the weak transfer. -/
def directionCoordinate : ℝ := Real.sin (nativeClockStep : ℝ) ^ 2 * gapAtNine +
  Real.sin (nativeClockStep : ℝ) * Real.cos (nativeClockStep : ℝ) * coherenceAtNine

theorem transfer_exact : transfer = directionCoordinate := by
  unfold transfer target
  rw [next_block]
  unfold pcEnergyOf pcMatrixOf
  rw [full_pair, pair_pc_energy, exchange_energy]
  have circle : Real.cos (nativeClockStep : ℝ) ^ 2 = 1 - Real.sin (nativeClockStep : ℝ) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (nativeClockStep : ℝ)]
  rw [circle]
  unfold directionCoordinate gapAtNine coherenceAtNine pairAtNine donorEnergyOf donorMatrixOf pcEnergyOf pcMatrixOf
  ring

theorem next_pair_balance (current : Live.State) :
    (pcEnergyOf (suppliedBlock (next current)) - pcEnergyOf (suppliedBlock current)) +
      (donorEnergyOf (suppliedBlock (next current)) - donorEnergyOf (suppliedBlock current)) = 0 := by
  rw [next_block]
  unfold pcEnergyOf donorEnergyOf pcMatrixOf donorMatrixOf
  rw [full_pair]
  have balance := Exchange.native_energy_balance Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian
    LAlanine40K2025.Thermal.Source.pairCoupling (nativeClockStep : ℝ)
    (Powered.Dynamics.systemReduce (suppliedBlock current))
  change energy Powered.Producer.poweredTotalHamiltonian
    (systemReduce (Quantum.conjugation (pairPulse (nativeClockStep : ℝ))
      (Powered.Dynamics.systemReduce (suppliedBlock current)))) +
    energy Powered.Producer.poweredTotalHamiltonian
    (bathReduce (Quantum.conjugation (pairPulse (nativeClockStep : ℝ))
      (Powered.Dynamics.systemReduce (suppliedBlock current)))) = _ at balance
  linarith

theorem remaining_debit : donorRemainingOf (suppliedBlock target) + transfer =
    donorRemainingOf (suppliedBlock origin) := by
  have mass : (suppliedBlock target).trace.re = (suppliedBlock origin).trace.re := by
    rw [target, next_block, Quantum.conjugation_trace]
  have balance := next_pair_balance origin
  change (pcEnergyOf (suppliedBlock target) - pcEnergyOf (suppliedBlock origin)) +
    (donorEnergyOf (suppliedBlock target) - donorEnergyOf (suppliedBlock origin)) = 0 at balance
  unfold donorRemainingOf transfer
  rw [mass]
  linarith

theorem execution_remaining : donorRemainingOf (suppliedBlock execution) + transfer =
    donorRemainingOf (suppliedBlock origin) := by
  rw [execution, load_remaining]
  exact remaining_debit

theorem supply_paid : transfer ≤ donorRemainingOf (suppliedBlock origin) := by
  linarith [remaining_debit, (remaining_range target).1]

theorem origin_is_actual : origin = Runtime.readNext Runtime.afterFirst := rfl

theorem clocks : origin.localClock = 9 * nativeClockStep ∧
    target.localClock = 10 * nativeClockStep ∧ execution.localClock = 11 * nativeClockStep := by
  refine ⟨executed_clock, ?_, ?_⟩
  · change origin.localClock + nativeClockStep = _
    rw [show origin.localClock = 9 * nativeClockStep from executed_clock]
    ring
  · change (origin.localClock + nativeClockStep) + nativeClockStep = _
    rw [show origin.localClock = 9 * nativeClockStep from executed_clock]
    ring

theorem execution_consumes_target : bodyRead execution.joint =
    Quantum.conjugation (Current.loadPulse (nativeClockStep : ℝ)) (bodyRead target.joint) :=
  Live.loadNext_body target

theorem positive_iff_source_coordinate : 0 < transfer ↔ 0 < directionCoordinate := by
  rw [transfer_exact]

structure WeakSupplyAndLoadCandidate : Prop where
  exactParent : type_of% origin_is_actual
  parentCoverage : type_of% (Runtime.face_factorizes Runtime.afterFirst .next)
  sameClock : type_of% clocks
  actualJoint : type_of% (next_joint origin)
  retainedBlock : type_of% (next_block origin)
  sourceDirection : type_of% transfer_exact
  sourcePayment : type_of% supply_paid
  donorDebit : type_of% remaining_debit
  loadConsumer : type_of% execution_consumes_target
  executionRemainder : type_of% execution_remaining

/-- Concrete source construction, exact finite payment, and its direct load consumer. -/
theorem sourceGeneratedWeakSupplyAndLoad : WeakSupplyAndLoadCandidate where
  exactParent := origin_is_actual
  parentCoverage := Runtime.face_factorizes Runtime.afterFirst .next
  sameClock := clocks
  actualJoint := next_joint origin
  retainedBlock := next_block origin
  sourceDirection := transfer_exact
  sourcePayment := supply_paid
  donorDebit := remaining_debit
  loadConsumer := execution_consumes_target
  executionRemainder := execution_remaining

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
