import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.ExchangeNorm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.LoadCost
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Evolution
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Received

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.FreeHistory
open Collision Quantum Propagation.Interface Load.Source Blocks Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def freeLoadHamiltonian : LoadedJoint :=
  Powered.Dynamics.bareHamiltonian Powered.Producer.poweredTotalHamiltonian 2

theorem free_load_hermitian : freeLoadHamiltonian.IsHermitian :=
  Powered.Dynamics.bareHamiltonian_hermitian _ _ Powered.Producer.poweredTotalHamiltonian_hermitian

def freeLoad (time : ℝ) : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  Load.Quantum.localUnitary (Native.freePCUnitary time) (Load.Recovery.Control.environmentUnitary time)

theorem free_load_matrix (time : ℝ) :
    (freeLoad time : LoadedJoint)=hamiltonianFlow freeLoadHamiltonian time := by
  change Matrix.kronecker (Native.freePCUnitary time : Matrix PairController PairController ℂ)
    (Load.Recovery.Control.environmentUnitary time : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [Native.freePCUnitary,Load.Producer.StrictThermal.flowUnitary_matrix_exp]
  change Matrix.kronecker (NormedSpace.exp (time • (-Complex.I • Powered.Producer.poweredTotalHamiltonian)))
    (NormedSpace.exp (time • (-Complex.I • Powered.Dynamics.controllerHamiltonian 2))) = _
  rw [← Load.Recovery.Control.exp_tensor_sum]
  congr 1
  ext i j
  simp only [freeLoadHamiltonian,Powered.Dynamics.bareHamiltonian,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.add_apply,Matrix.smul_apply,Complex.real_smul]
  ring

theorem actual_load_free_error (time : ℝ) :
    ‖(loadUnitary time : LoadedJoint)-(freeLoad time : LoadedJoint)‖ ≤ |time| := by
  have estimate := hamiltonian_flow_error loadTotalHamiltonian freeLoadHamiltonian
    loadTotalHamiltonian_hermitian free_load_hermitian time
  have difference : loadTotalHamiltonian-freeLoadHamiltonian=loadInteraction := by
    unfold loadTotalHamiltonian freeLoadHamiltonian Powered.Dynamics.totalHamiltonian
    abel
  rw [difference] at estimate
  rw [loadUnitary,Load.Producer.StrictThermal.flowUnitary_matrix_exp,free_load_matrix]
  change ‖hamiltonianFlow loadTotalHamiltonian time-hamiltonianFlow freeLoadHamiltonian time‖ ≤ _
  exact estimate.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left Inverse.actual_load_interaction_norm (abs_nonneg time))

theorem actual_load_observer_error (O rho : LoadedJoint) (positive : rho.PosSemidef) (time : ℝ) :
    |energy O (conjugation (loadUnitary time) rho)-energy O (conjugation (freeLoad time) rho)| ≤
      2 * ‖O‖ * |time| * rho.trace.re := by
  have bound := weighted_observable_error O rho positive (loadUnitary time) (freeLoad time)
  have mass : 0 ≤ rho.trace.re := (Complex.nonneg_iff.mp positive.trace_nonneg).1
  exact bound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (actual_load_free_error time)
      (mul_nonneg (by norm_num) (norm_nonneg O))) mass)

def freeReceivedWord : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  Load.Quantum.localUnitary
    (Load.Recovery.Control.minimalPCUnitary (3*(Propagation.Producer.nativeClockStep : ℝ)))
    (Load.Recovery.Control.environmentUnitary (3*(Propagation.Producer.nativeClockStep : ℝ))) *
  freeLoad (Propagation.Producer.nativeClockStep : ℝ) * Load.Quantum.localUnitary Load.Producer.loadParentUnitary 1

theorem original_received_word_error :
    ‖(Inverse.Scaled.Finite.Input.receivedWord : LoadedJoint)-(freeReceivedWord : LoadedJoint)‖ ≤
      (Propagation.Producer.nativeClockStep : ℝ) := by
  let U := Load.Quantum.localUnitary
    (Load.Recovery.Control.minimalPCUnitary (3*(Propagation.Producer.nativeClockStep : ℝ)))
    (Load.Recovery.Control.environmentUnitary (3*(Propagation.Producer.nativeClockStep : ℝ)))
  let V : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
    Load.Quantum.localUnitary Load.Producer.loadParentUnitary 1
  change ‖(U : LoadedJoint)*(loadUnitary (Propagation.Producer.nativeClockStep : ℝ) : LoadedJoint)*(V : LoadedJoint) -
    (U : LoadedJoint)*(freeLoad (Propagation.Producer.nativeClockStep : ℝ) : LoadedJoint)*(V : LoadedJoint)‖ ≤ _
  rw [← Matrix.sub_mul,← Matrix.mul_sub,CStarRing.norm_mul_mem_unitary _ V.property,
    CStarRing.norm_mem_unitary_mul _ U.property]
  have positive : 0 < (Propagation.Producer.nativeClockStep : ℝ) := by
    exact_mod_cast Propagation.Producer.nativeClockStep_positive
  simpa only [abs_of_pos positive] using
    actual_load_free_error (Propagation.Producer.nativeClockStep : ℝ)

theorem local_unitary_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U V : Matrix.unitaryGroup ι ℂ) (W Z : Matrix.unitaryGroup κ ℂ) :
    Load.Quantum.localUnitary U W * Load.Quantum.localUnitary V Z =
      Load.Quantum.localUnitary (U*V) (W*Z) := by
  apply Subtype.ext
  change Matrix.kronecker (U : Matrix ι ι ℂ) (W : Matrix κ κ ℂ) *
    Matrix.kronecker (V : Matrix ι ι ℂ) (Z : Matrix κ κ ℂ) =
      Matrix.kronecker ((U*V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)
        ((W*Z : Matrix.unitaryGroup κ ℂ) : Matrix κ κ ℂ)
  simp only [Matrix.kronecker,← Matrix.mul_kronecker_mul,Submonoid.coe_mul]

def freeReceivedPC : Matrix.unitaryGroup PairController ℂ :=
  Load.Recovery.Control.minimalPCUnitary (3*(Propagation.Producer.nativeClockStep : ℝ)) *
    Native.freePCUnitary (Propagation.Producer.nativeClockStep : ℝ) * Load.Producer.loadParentUnitary

def freeReceivedEnvironment : Matrix.unitaryGroup (Fin 2) ℂ :=
  Load.Recovery.Control.environmentUnitary (3*(Propagation.Producer.nativeClockStep : ℝ)) *
    Load.Recovery.Control.environmentUnitary (Propagation.Producer.nativeClockStep : ℝ)

theorem free_received_factor :
    freeReceivedWord=Load.Quantum.localUnitary freeReceivedPC freeReceivedEnvironment := by
  rw [freeReceivedWord,freeLoad,local_unitary_mul,local_unitary_mul,mul_one]
  rfl

theorem free_received_product :
    conjugation freeReceivedWord Inverse.Scaled.Finite.Input.preparedBody =
      Matrix.kronecker
        (conjugation freeReceivedPC (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair))
        (conjugation freeReceivedEnvironment environmentState) := by
  rw [free_received_factor]
  exact Load.Quantum.localConjugation_tensor _ _ _ _

theorem free_received_pc_energy (rho : Matrix PairController PairController ℂ) :
    energy Powered.Producer.poweredTotalHamiltonian (conjugation freeReceivedPC rho) =
      energy Powered.Producer.poweredTotalHamiltonian rho := by
  change energy Powered.Producer.poweredTotalHamiltonian
    (Unitary.conjStarAlgAut ℂ _ freeReceivedPC rho)=_
  rw [freeReceivedPC,Unitary.conjStarAlgAut_mul_apply,Unitary.conjStarAlgAut_mul_apply,
    Load.Recovery.Control.minimalPCUnitary_inclusive_energy]
  change energy Powered.Producer.poweredTotalHamiltonian
    (conjugation (Native.freePCUnitary (Propagation.Producer.nativeClockStep : ℝ))
      (conjugation Load.Producer.loadParentUnitary rho))=_
  rw [Native.freePC_energy]
  exact Native.freePC_energy (2*(Propagation.Producer.nativeClockStep : ℝ)) rho

section ExactInstrument
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
theorem body_product_sandwich (A body : Matrix (ι × κ) (ι × κ) ℂ) (donor : Matrix ι ι ℂ) :
    Incidence.bodyObservable A * Incidence.receivedJoint body donor * Incidence.bodyObservable A =
      Incidence.receivedJoint (A*body*A) donor := by
  unfold Incidence.bodyObservable Incidence.receivedJoint
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  congr 1
  simp only [Matrix.kronecker,← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]

theorem exact_instrument_right_product (E body : Matrix (ι × κ) (ι × κ) ℂ)
    (donor : Matrix ι ι ℂ) (complement : (1-E).PosSemidef) :
    (dilationMatrix (Incidence.bodyObservable E) * prepared (Incidence.receivedJoint body donor) *
      (dilationMatrix (Incidence.bodyObservable E))ᴴ).toBlocks₂₂ =
        Incidence.receivedJoint (complementRoot E*body*complementRoot E) donor := by
  rw [dilation_prepared_blocks,Matrix.toBlocks_fromBlocks₂₂]
  unfold complementRoot
  rw [bodyObservable_complement,← body_observable_sqrt (1-E) complement]
  exact body_product_sandwich _ _ _

omit [DecidableEq ι] [DecidableEq κ] in
theorem received_product_donor (body : Matrix (ι × κ) (ι × κ) ℂ) (donor : Matrix ι ι ℂ) :
    Collision.bathReduce (Powered.Dynamics.systemReduce (Incidence.receivedJoint body donor)) =
      body.trace • donor := by
  ext i j
  change (∑ a : ι, ∑ e : κ, body (a,e) (a,e)*donor i j)=body.trace*donor i j
  simp only [Matrix.trace,Matrix.diag,Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]

end ExactInstrument

theorem local_left_error {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Nonempty κ] (U V : Matrix.unitaryGroup ι ℂ) (W : Matrix.unitaryGroup κ ℂ) :
    ‖(Load.Quantum.localUnitary U W : Matrix (ι × κ) (ι × κ) ℂ) -
      (Load.Quantum.localUnitary V W : Matrix (ι × κ) (ι × κ) ℂ)‖ ≤
        ‖(U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)‖ := by
  have split : (Load.Quantum.localUnitary U W : Matrix (ι × κ) (ι × κ) ℂ) -
      (Load.Quantum.localUnitary V W : Matrix (ι × κ) (ι × κ) ℂ) =
      Matrix.kronecker ((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)) (W : Matrix κ κ ℂ) := by
    ext i j
    change U i.1 j.1*W i.2 j.2 - V i.1 j.1*W i.2 j.2 = (U i.1 j.1-V i.1 j.1)*W i.2 j.2
    ring
  rw [split]
  have bound := Load.Producer.StrictThermal.kronecker_norm_le
    ((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)) (W : Matrix κ κ ℂ)
  simpa only [CStarRing.norm_coe_unitary W,mul_one] using bound

def fullFree (time : ℝ) : Matrix.unitaryGroup Current.FullIndex ℂ :=
  Load.Quantum.localUnitary (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time))
    (Load.Recovery.Control.environmentUnitary time)

theorem full_free_lift (time : ℝ) :
    Incidence.localLift (freeLoad time) (Native.freePCUnitary time)=fullFree time := by
  apply Subtype.ext
  ext i j
  change ((Native.freePCUnitary time) i.1.1 j.1.1 *
      (Load.Recovery.Control.environmentUnitary time) i.2 j.2) *
      (Native.freePCUnitary time) i.1.2 j.1.2 =
    ((Native.freePCUnitary time) i.1.1 j.1.1 * (Native.freePCUnitary time) i.1.2 j.1.2) *
      (Load.Recovery.Control.environmentUnitary time) i.2 j.2
  ring

theorem full_load_free_error (time : ℝ) :
    ‖(Current.loadPulse time : Current.FullJoint)-(fullFree time : Current.FullJoint)‖ ≤ |time| := by
  rw [← full_free_lift]
  have same : (Current.loadPulse time : Current.FullJoint) -
      (Incidence.localLift (freeLoad time) (Native.freePCUnitary time) : Current.FullJoint) =
      bodyRegroup ((Load.Quantum.localUnitary (loadUnitary time) (Native.freePCUnitary time) :
        Matrix ((PairController × Fin 2) × PairController) ((PairController × Fin 2) × PairController) ℂ) -
        (Load.Quantum.localUnitary (freeLoad time) (Native.freePCUnitary time) :
        Matrix ((PairController × Fin 2) × PairController) ((PairController × Fin 2) × PairController) ℂ)) := rfl
  rw [same,StarAlgEquiv.norm_map]
  exact (local_left_error _ _ _).trans (actual_load_free_error time)

def idealSupply (time : ℝ) : Matrix.unitaryGroup Current.FullIndex ℂ :=
  Load.Quantum.localUnitary
    (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time)*Exchange.fullTransfer)
    (Load.Recovery.Control.environmentUnitary time)

theorem exchange_as_flow {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) :
    (Exchange.exchangeUnitary (ι := ι) t : JointMatrix ι)=hamiltonianFlow (t • (swapOperator : JointMatrix ι)) 1 := by
  change partialSwap (Real.cos t) (Real.sin t)=NormedSpace.exp (1 • (-Complex.I • (t • (swapOperator : JointMatrix ι))))
  rw [one_smul]
  have scalar : -Complex.I • (t • (swapOperator : JointMatrix ι)) =
      (-Complex.I*(t : ℂ)) • (swapOperator : JointMatrix ι) := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
    ring
  rw [scalar]
  exact (Dynamics.exp_neg_I_smul_involution (swapOperator : JointMatrix ι) swap_squared t).symm

theorem exchange_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (t s : ℝ) :
    ‖(Exchange.exchangeUnitary (ι := ι) t : JointMatrix ι)-(Exchange.exchangeUnitary (ι := ι) s : JointMatrix ι)‖ ≤ |t-s| := by
  have hermitian : (swapOperator : JointMatrix ι).IsHermitian := swap_adjoint
  have bound := hamiltonian_flow_error (t • (swapOperator : JointMatrix ι))
    (s • (swapOperator : JointMatrix ι)) (hermitian.smul (show IsSelfAdjoint t from rfl))
    (hermitian.smul (show IsSelfAdjoint s from rfl)) 1
  rw [← sub_smul,norm_smul,Load.Producer.StrictThermal.swap_norm,Real.norm_eq_abs,mul_one] at bound
  simpa only [exchange_as_flow,abs_one,one_mul] using bound

theorem near_transfer_sharp {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (t : ℝ) :
    ‖(Exchange.nearTransfer (ι := ι) t : JointMatrix ι)-(Exchange.fullTransfer (ι := ι) : JointMatrix ι)‖ ≤ |t| := by
  have bound := exchange_lipschitz (ι := ι) (Real.pi/2-t) (Real.pi/2)
  have sub : Real.pi/2-t-Real.pi/2=-t := by ring
  change ‖(Exchange.exchangeUnitary (ι := ι) (Real.pi/2-t) : JointMatrix ι)-
    (Exchange.exchangeUnitary (ι := ι) (Real.pi/2) : JointMatrix ι)‖ ≤ |t|
  simpa only [sub,abs_neg] using bound

theorem small_exchange_sharp {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (t : ℝ) :
    ‖(Exchange.exchangeUnitary (ι := ι) t : JointMatrix ι)-1‖ ≤ |t| := by
  have bound := exchange_lipschitz (ι := ι) t 0
  have zero : (Exchange.exchangeUnitary (ι := ι) 0 : JointMatrix ι)=1 := by
    change partialSwap (Real.cos 0) (Real.sin 0)=1
    simp [partialSwap]
  simpa only [zero,sub_zero] using bound

theorem supply_clock_error_sharp :
    ‖(Current.pulse (Propagation.Producer.nativeClockStep : ℝ) : Current.FullJoint) -
      (idealSupply (Propagation.Producer.nativeClockStep : ℝ) : Current.FullJoint)‖ ≤
        (Propagation.Producer.nativeClockStep : ℝ) := by
  let q : ℝ := Propagation.Producer.nativeClockStep
  let F := Quantum.localUnitary (Native.freePCUnitary q) (Native.freePCUnitary q)
  have positive : 0 < q := by
    change 0 < (Propagation.Producer.nativeClockStep : ℝ)
    exact_mod_cast Propagation.Producer.nativeClockStep_positive
  have pairError : ‖((F*Exchange.nearTransfer q : Matrix.unitaryGroup (PairController × PairController) ℂ) :
      JointMatrix PairController)-((F*Exchange.fullTransfer : Matrix.unitaryGroup (PairController × PairController) ℂ) :
      JointMatrix PairController)‖ ≤ q := by
    simp only [Submonoid.coe_mul]
    rw [← Matrix.mul_sub,CStarRing.norm_mem_unitary_mul _ F.property]
    simpa only [abs_of_pos positive] using near_transfer_sharp (ι := PairController) q
  have bound := (local_left_error (F*Exchange.nearTransfer q) (F*Exchange.fullTransfer)
    (Load.Recovery.Control.environmentUnitary q)).trans pairError
  rw [Current.pulse,idealSupply,Native.pairFlow_factor,Native.sourceCoupling_clock]
  exact bound

theorem weak_free_error (time : ℝ) :
    ‖(Weak.fullPulse time : Current.FullJoint)-(fullFree time : Current.FullJoint)‖ ≤ |time| := by
  let F := Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time)
  have pairError : ‖((F*Exchange.exchangeUnitary (ι := PairController) time : Matrix.unitaryGroup (PairController × PairController) ℂ) :
      JointMatrix PairController)-(F : JointMatrix PairController)‖ ≤ |time| := by
    simp only [Submonoid.coe_mul]
    have split : (F : JointMatrix PairController)*(Exchange.exchangeUnitary (ι := PairController) time : JointMatrix PairController) -
        (F : JointMatrix PairController) =
        (F : JointMatrix PairController)*((Exchange.exchangeUnitary (ι := PairController) time : JointMatrix PairController)-1) := by
      rw [Matrix.mul_sub,Matrix.mul_one]
    rw [split,CStarRing.norm_mem_unitary_mul _ F.property]
    exact small_exchange_sharp (ι := PairController) time
  rw [Weak.fullPulse,Weak.pair_factor,fullFree]
  exact (local_left_error _ _ _).trans pairError

theorem unitary_product_distance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V W Z : Matrix.unitaryGroup ι ℂ) :
    ‖((U*V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) -
      ((W*Z : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)‖ ≤
        ‖(U : Matrix ι ι ℂ)-(W : Matrix ι ι ℂ)‖ + ‖(V : Matrix ι ι ℂ)-(Z : Matrix ι ι ℂ)‖ := by
  have bound := norm_sub_le_norm_sub_add_norm_sub
    ((U : Matrix ι ι ℂ)*(V : Matrix ι ι ℂ))
    ((W : Matrix ι ι ℂ)*(V : Matrix ι ι ℂ))
    ((W : Matrix ι ι ℂ)*(Z : Matrix ι ι ℂ))
  rw [← Matrix.sub_mul,← Matrix.mul_sub,CStarRing.norm_mul_mem_unitary _ V.property,
    CStarRing.norm_mem_unitary_mul _ W.property] at bound
  exact bound

section FullSwap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem full_transfer_matrix :
    (Exchange.fullTransfer (ι := ι) : JointMatrix ι)=(-Complex.I) • swapOperator := by
  change partialSwap (Real.cos (Real.pi/2)) (Real.sin (Real.pi/2))=_
  simp [partialSwap]

theorem full_transfer_conjugation (rho : JointMatrix ι) :
    conjugation (Exchange.fullTransfer (ι := ι)) rho=swapOperator*rho*swapOperator := by
  rw [Quantum.conjugation_apply,full_transfer_matrix]
  simp only [star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    Matrix.star_eq_conjTranspose,swap_adjoint]
  simp

theorem full_transfer_system (rho : JointMatrix ι) :
    Collision.systemReduce (conjugation (Exchange.fullTransfer (ι := ι)) rho)=Collision.bathReduce rho := by
  rw [full_transfer_conjugation]
  exact swapped_system rho

theorem full_transfer_bath (rho : JointMatrix ι) :
    Collision.bathReduce (conjugation (Exchange.fullTransfer (ι := ι)) rho)=Collision.systemReduce rho := by
  rw [full_transfer_conjugation]
  ext i j
  change (∑ a : ι, (swapOperator*rho*swapOperator : JointMatrix ι) (a,i) (a,j))=
    ∑ a : ι, rho (i,a) (j,a)
  simp only [mul_swap_apply,swap_mul_apply]

theorem full_transfer_product (rho tau : SystemMatrix ι) :
    conjugation (Exchange.fullTransfer (ι := ι)) (Matrix.kronecker rho tau)=Matrix.kronecker tau rho := by
  rw [full_transfer_conjugation,swap_kronecker_swap]
end FullSwap

theorem full_free_pc (time : ℝ) (rho : Current.FullJoint) :
    Resource.pcMatrixOf (conjugation (fullFree time) rho)=
      conjugation (Native.freePCUnitary time) (Resource.pcMatrixOf rho) := by
  unfold Resource.pcMatrixOf
  have outer := Load.Quantum.systemReduce_local_conjugation
    (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time))
    (Load.Recovery.Control.environmentUnitary time) rho
  change Powered.Dynamics.systemReduce (conjugation (fullFree time) rho)=_ at outer
  rw [outer]
  exact Quantum.systemReduce_local_conjugation _ _ _

theorem full_free_donor (time : ℝ) (rho : Current.FullJoint) :
    Resource.donorMatrixOf (conjugation (fullFree time) rho)=
      conjugation (Native.freePCUnitary time) (Resource.donorMatrixOf rho) := by
  unfold Resource.donorMatrixOf
  have outer := Load.Quantum.systemReduce_local_conjugation
    (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time))
    (Load.Recovery.Control.environmentUnitary time) rho
  change Powered.Dynamics.systemReduce (conjugation (fullFree time) rho)=_ at outer
  rw [outer]
  exact Quantum.bathReduce_local_conjugation _ _ _

theorem ideal_supply_pc (time : ℝ) (rho : Current.FullJoint) :
    Resource.pcMatrixOf (conjugation (idealSupply time) rho)=
      conjugation (Native.freePCUnitary time) (Resource.donorMatrixOf rho) := by
  unfold Resource.pcMatrixOf Resource.donorMatrixOf
  have outer := Load.Quantum.systemReduce_local_conjugation
    (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time)*Exchange.fullTransfer)
    (Load.Recovery.Control.environmentUnitary time) rho
  change Powered.Dynamics.systemReduce (conjugation (idealSupply time) rho)=_ at outer
  rw [outer,← Environment.conjugation_comp]
  change Collision.systemReduce (Quantum.localConjugation (Native.freePCUnitary time)
    (Native.freePCUnitary time) (conjugation Exchange.fullTransfer (Powered.Dynamics.systemReduce rho)))=_
  rw [Quantum.systemReduce_local_conjugation,full_transfer_system]

theorem ideal_supply_donor (time : ℝ) (rho : Current.FullJoint) :
    Resource.donorMatrixOf (conjugation (idealSupply time) rho)=
      conjugation (Native.freePCUnitary time) (Resource.pcMatrixOf rho) := by
  unfold Resource.donorMatrixOf Resource.pcMatrixOf
  have outer := Load.Quantum.systemReduce_local_conjugation
    (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time)*Exchange.fullTransfer)
    (Load.Recovery.Control.environmentUnitary time) rho
  change Powered.Dynamics.systemReduce (conjugation (idealSupply time) rho)=_ at outer
  rw [outer,← Environment.conjugation_comp]
  change Collision.bathReduce (Quantum.localConjugation (Native.freePCUnitary time)
    (Native.freePCUnitary time) (conjugation Exchange.fullTransfer (Powered.Dynamics.systemReduce rho)))=_
  rw [Quantum.bathReduce_local_conjugation,full_transfer_bath]

theorem received_tensor (A B : Matrix PairController PairController ℂ)
    (E : Matrix (Fin 2) (Fin 2) ℂ) :
    Incidence.receivedJoint (Matrix.kronecker A E) B=Matrix.kronecker (Matrix.kronecker A B) E := by
  ext i j
  change (A i.1.1 j.1.1*E i.2 j.2)*B i.1.2 j.1.2=(A i.1.1 j.1.1*B i.1.2 j.1.2)*E i.2 j.2
  ring

theorem ideal_supply_product (time : ℝ) (A B : Matrix PairController PairController ℂ)
    (E : Matrix (Fin 2) (Fin 2) ℂ) :
    conjugation (idealSupply time) (Incidence.receivedJoint (Matrix.kronecker A E) B)=
      Incidence.receivedJoint
        (conjugation (freeLoad time) (Matrix.kronecker B E))
        (conjugation (Native.freePCUnitary time) A) := by
  rw [received_tensor]
  have body : conjugation (freeLoad time) (Matrix.kronecker B E)=
      Matrix.kronecker (conjugation (Native.freePCUnitary time) B)
        (conjugation (Load.Recovery.Control.environmentUnitary time) E) :=
    Load.Quantum.localConjugation_tensor _ _ _ _
  rw [body,received_tensor]
  change Load.Quantum.localConjugation
    (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time)*Exchange.fullTransfer)
    (Load.Recovery.Control.environmentUnitary time) (Matrix.kronecker (Matrix.kronecker A B) E)=_
  rw [Load.Quantum.localConjugation_tensor,← Environment.conjugation_comp,full_transfer_product]
  change Matrix.kronecker
    (Quantum.localConjugation (Native.freePCUnitary time) (Native.freePCUnitary time) (Matrix.kronecker B A))
    (conjugation (Load.Recovery.Control.environmentUnitary time) E)=_
  rw [Quantum.localConjugation_tensor]

def barePC (time : ℝ) : Matrix.unitaryGroup PairController ℂ :=
  Powered.Dynamics.flowUnitary Work.Drive.fieldBaseline 2 0 Work.Drive.fieldBaseline_hermitian
    Matrix.isHermitian_zero time

theorem free_received_bare :
    freeReceivedPC=barePC (6*(Propagation.Producer.nativeClockStep : ℝ)) := by
  let q : ℝ := Propagation.Producer.nativeClockStep
  have add (s t : ℝ) : Native.freePCUnitary (s+t)=Native.freePCUnitary s*Native.freePCUnitary t :=
    Powered.Dynamics.flowUnitary_add _ _ _ _ _ s t
  have zero : Native.freePCUnitary 0=1 := Powered.Dynamics.flowUnitary_zero _ _ _ _ _
  rw [freeReceivedPC,Load.Recovery.Control.minimalPCUnitary_phase]
  change barePC (2*(3*q))*Native.freePCUnitary (-(3*q))*Native.freePCUnitary q*
    Native.freePCUnitary (2*q)=barePC (6*q)
  rw [show 2*(3*q)=6*q by ring]
  calc
    _ = barePC (6*q)*(Native.freePCUnitary (-(3*q))*Native.freePCUnitary q*Native.freePCUnitary (2*q)) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [← add,← add,show -(3*q)+q+2*q=0 by ring,zero,mul_one]

theorem pc_load_commutator_bound :
    ‖loadInteraction*Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)*loadInteraction‖ ≤ 101 := by
  rw [Inverse.original_load_commutator_norm]
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (loadInteraction*Inverse.actualLoadPC-Inverse.actualLoadPC*loadInteraction)
    (loadInteraction*Inverse.numericLoadPC-Inverse.numericLoadPC*loadInteraction) 0
  simp only [sub_zero] at triangle
  have cost := Inverse.original_load_cost
  unfold Inverse.loadResponseCost at cost
  linarith only [triangle,Inverse.original_load_commutator_error,cost]

theorem free_boundary_commutator_bound :
    ‖freeLoadHamiltonian*loadInteraction-loadInteraction*freeLoadHamiltonian‖ ≤ 105 := by
  let A : LoadedJoint := Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)
  let B : LoadedJoint := Matrix.kronecker (1 : Matrix PairController PairController ℂ) (Powered.Dynamics.controllerHamiltonian 2)
  have bnorm : ‖B‖ ≤ 2 :=
    (NonUnitalStarAlgHom.norm_apply_le
      (Load.Producer.StrictThermal.tensorRight (ι := PairController) (κ := Fin 2)) _).trans
        Load.Producer.StrictThermal.controllerHamiltonian_norm_le
  have pc : ‖A*loadInteraction-loadInteraction*A‖ ≤ 101 := by
    rw [norm_sub_rev]
    exact pc_load_commutator_bound
  have env : ‖B*loadInteraction-loadInteraction*B‖ ≤ 4 := by
    have estimate := (norm_sub_le (B*loadInteraction) (loadInteraction*B)).trans
      (add_le_add (norm_mul_le B loadInteraction) (norm_mul_le loadInteraction B))
    have product := mul_le_mul bnorm Inverse.actual_load_interaction_norm
      (norm_nonneg loadInteraction) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [estimate,product]
  have split : freeLoadHamiltonian*loadInteraction-loadInteraction*freeLoadHamiltonian=
      (A*loadInteraction-loadInteraction*A)+(B*loadInteraction-loadInteraction*B) := by
    change (A+B)*loadInteraction-loadInteraction*(A+B)=_
    noncomm_ring
  rw [split]
  exact (norm_add_le _ _).trans (by linarith only [pc,env])

theorem free_load_boundary_response (time : ℝ) :
    ‖conjugation (star (freeLoad time)) loadInteraction-loadInteraction‖ ≤ 105*|time| := by
  have originalFlow : Powered.Dynamics.flowUnitary Powered.Producer.poweredTotalHamiltonian 2 0
      Powered.Producer.poweredTotalHamiltonian_hermitian Matrix.isHermitian_zero time=freeLoad time :=
    Load.Recovery.Control.source_barePCE_factor time
  have bound := Inverse.flow_observable_response Powered.Producer.poweredTotalHamiltonian 2 0
    Powered.Producer.poweredTotalHamiltonian_hermitian Matrix.isHermitian_zero time loadInteraction
  rw [originalFlow] at bound
  change ‖conjugation (star (freeLoad time)) loadInteraction-loadInteraction‖ ≤
    |time| * ‖(freeLoadHamiltonian+0)*loadInteraction-loadInteraction*(freeLoadHamiltonian+0)‖ at bound
  simp only [add_zero] at bound
  exact bound.trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left free_boundary_commutator_bound (abs_nonneg time))

section LargeCarrierReadouts
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem exact_instrument_conjugation_right
    (E body : Matrix (ι × κ) (ι × κ) ℂ) (donor : Matrix ι ι ℂ)
    (positive : E.PosSemidef) (complement : (1-E).PosSemidef) :
    (conjugation (dilation (Incidence.bodyObservable E)
      (bodyObservable_lawful E positive complement).1 (bodyObservable_lawful E positive complement).2)
      (prepared (Incidence.receivedJoint body donor))).toBlocks₂₂=
        Incidence.receivedJoint (complementRoot E*body*complementRoot E) donor := by
  change (dilationMatrix (Incidence.bodyObservable E) * prepared (Incidence.receivedJoint body donor) *
    (dilationMatrix (Incidence.bodyObservable E))ᴴ).toBlocks₂₂=_
  exact exact_instrument_right_product E body donor complement

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
theorem positive_trace_real (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) :
    rho.trace=(rho.trace.re : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp positive.trace_nonneg).2.symm

omit [DecidableEq ι] [DecidableEq κ] in
theorem pc_mass_of_reduced (rho : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ)
    (p : ℂ) (tau : Matrix ι ι ℂ)
    (reduced : Collision.systemReduce (Powered.Dynamics.systemReduce rho)=p • tau) (trace : tau.trace=1) :
    rho.trace=p := by
  have h : (Collision.systemReduce (Powered.Dynamics.systemReduce rho)).trace=rho.trace := by
    rw [Collision.systemReduce_trace,Powered.Dynamics.systemReduce_trace]
  rw [reduced,Matrix.trace_smul,trace,smul_eq_mul,mul_one] at h
  exact h.symm

omit [Fintype κ] [DecidableEq κ] in
theorem right_identity_read (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    energy (Matrix.fromBlocks (0 : Matrix ι ι ℂ) 0 0 1) rho=oneRead rho := by
  conv_lhs => arg 2; rw [← Matrix.fromBlocks_toBlocks rho]
  simp [energy,Matrix.fromBlocks_multiply,trace_fromBlocks,oneRead]

end LargeCarrierReadouts

theorem full_free_received (time : ℝ) (body : LoadedJoint)
    (donor : Matrix PairController PairController ℂ) :
    conjugation (fullFree time) (Incidence.receivedJoint body donor)=
      Incidence.receivedJoint (conjugation (freeLoad time) body) (conjugation (Native.freePCUnitary time) donor) := by
  rw [← full_free_lift,Incidence.localLift,Incidence.receivedJoint,Incidence.regroup_conjugation]
  change (Load.Quantum.localConjugation (freeLoad time) (Native.freePCUnitary time)
    (Matrix.kronecker body donor)).submatrix Incidence.bodyReservoir Incidence.bodyReservoir=_
  rw [Load.Quantum.localConjugation_tensor]
  rfl

theorem pc_lift_eq_bodyLift (U : Matrix.unitaryGroup PairController ℂ) :
    Load.Quantum.localUnitary (Quantum.localUnitary U 1) (1 : Matrix.unitaryGroup (Fin 2) ℂ)=
      Incidence.bodyLift (Load.Quantum.localUnitary U (1 : Matrix.unitaryGroup (Fin 2) ℂ)) := by
  apply Subtype.ext
  ext i j
  change (U i.1.1 j.1.1*(1 : Matrix PairController PairController ℂ) i.1.2 j.1.2)*
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i.2 j.2 =
    (U i.1.1 j.1.1*(1 : Matrix (Fin 2) (Fin 2) ℂ) i.2 j.2)*
      (1 : Matrix PairController PairController ℂ) i.1.2 j.1.2
  ring

theorem pc_lift_received (U : Matrix.unitaryGroup PairController ℂ) (body : LoadedJoint)
    (donor : Matrix PairController PairController ℂ) :
    conjugation (Load.Quantum.localUnitary (Quantum.localUnitary U 1)
      (1 : Matrix.unitaryGroup (Fin 2) ℂ)) (Incidence.receivedJoint body donor)=
        Incidence.receivedJoint (conjugation (Load.Quantum.localUnitary U (1 : Matrix.unitaryGroup (Fin 2) ℂ)) body) donor := by
  rw [pc_lift_eq_bodyLift,Incidence.bodyLift_received]

theorem pc_lift_body_read (U : Matrix.unitaryGroup PairController ℂ) (rho : Current.FullJoint) :
    Incidence.bodyRead (conjugation (Load.Quantum.localUnitary (Quantum.localUnitary U 1)
      (1 : Matrix.unitaryGroup (Fin 2) ℂ)) rho)=
        conjugation (Load.Quantum.localUnitary U (1 : Matrix.unitaryGroup (Fin 2) ℂ)) (Incidence.bodyRead rho) := by
  rw [pc_lift_eq_bodyLift,Incidence.bodyLift_read]

def fullSwap : Matrix.unitaryGroup Current.FullIndex ℂ :=
  Load.Quantum.localUnitary (Exchange.fullTransfer (ι := PairController)) (1 : Matrix.unitaryGroup (Fin 2) ℂ)

theorem ideal_supply_factor (time : ℝ) : idealSupply time=fullFree time*fullSwap := by
  rw [fullFree,fullSwap,local_unitary_mul,mul_one]
  rfl

theorem full_swap_twice (rho : Current.FullJoint) :
    conjugation fullSwap (conjugation fullSwap rho)=rho := by
  have square : (fullSwap : Current.FullJoint)*(fullSwap : Current.FullJoint)=(-1 : ℂ) • 1 := by
    change Matrix.kronecker (Exchange.fullTransfer (ι := PairController) : JointMatrix PairController) (1 : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.kronecker (Exchange.fullTransfer (ι := PairController) : JointMatrix PairController) (1 : Matrix (Fin 2) (Fin 2) ℂ)=_
    simp only [Matrix.kronecker,← Matrix.mul_kronecker_mul,Matrix.one_mul,full_transfer_matrix,
      Matrix.smul_mul,Matrix.mul_smul,smul_smul,swap_squared,Matrix.smul_kronecker,Matrix.one_kronecker_one]
    norm_num
  rw [Environment.conjugation_comp,Quantum.conjugation_apply]
  change ((fullSwap : Current.FullJoint)*(fullSwap : Current.FullJoint))*rho*
    star ((fullSwap : Current.FullJoint)*(fullSwap : Current.FullJoint))=_
  rw [square]
  simp

theorem full_swap_free_commute (time : ℝ) : fullSwap*fullFree time=fullFree time*fullSwap := by
  have pair : Exchange.fullTransfer*Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time)=
      Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time)*Exchange.fullTransfer := by
    apply Subtype.ext
    change (Exchange.fullTransfer (ι := PairController) : JointMatrix PairController)*
      (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time) : JointMatrix PairController)=
      (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time) : JointMatrix PairController)*
        (Exchange.fullTransfer (ι := PairController) : JointMatrix PairController)
    rw [full_transfer_matrix]
    exact ((Powered.Source.swap_commutes_shared (Native.freePCUnitary time)).smul_left (-Complex.I)).eq
  rw [fullSwap,fullFree,local_unitary_mul,local_unitary_mul,one_mul,mul_one,pair]

theorem full_free_add (s t : ℝ) : fullFree (s+t)=fullFree s*fullFree t := by
  have pc : Native.freePCUnitary (s+t)=Native.freePCUnitary s*Native.freePCUnitary t :=
    Powered.Dynamics.flowUnitary_add _ _ _ _ _ s t
  rw [fullFree,fullFree,fullFree,local_unitary_mul,
    Load.Recovery.Control.environmentUnitary_add,pc]
  have pair : Quantum.localUnitary (Native.freePCUnitary s*Native.freePCUnitary t)
      (Native.freePCUnitary s*Native.freePCUnitary t)=
      Quantum.localUnitary (Native.freePCUnitary s) (Native.freePCUnitary s)*
        Quantum.localUnitary (Native.freePCUnitary t) (Native.freePCUnitary t) :=
    (local_unitary_mul _ _ _ _).symm
  exact congrArg (fun U : Matrix.unitaryGroup (PairController × PairController) ℂ =>
    Load.Quantum.localUnitary U (Load.Recovery.Control.environmentUnitary s*Load.Recovery.Control.environmentUnitary t)) pair

theorem ideal_supply_twice (time : ℝ) (rho : Current.FullJoint) :
    conjugation (idealSupply time) (conjugation (idealSupply time) rho)=
      conjugation (fullFree (2*time)) rho := by
  have pair : (fullFree time*fullSwap)*(fullFree time*fullSwap)=
      (fullFree time*fullFree time)*(fullSwap*fullSwap) := by
    calc
      _ = fullFree time*(fullSwap*fullFree time)*fullSwap := by simp only [mul_assoc]
      _ = _ := by rw [full_swap_free_commute]; simp only [mul_assoc]
  rw [ideal_supply_factor,Environment.conjugation_comp,pair,← full_free_add,
    ← Environment.conjugation_comp,← Environment.conjugation_comp,full_swap_twice]
  rw [show time+time=2*time by ring]

section SwappedBody
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
private theorem tensor_swap_permutation :
    Matrix.kronecker (swapOperator : JointMatrix ι) (1 : Matrix κ κ ℂ)=
      Equiv.Perm.permMatrix ℂ (Equiv.prodCongr (Equiv.prodComm ι ι) (Equiv.refl κ)) := by
  ext ⟨⟨a,b⟩,e⟩ ⟨⟨c,d⟩,f⟩
  by_cases left : b=c <;> by_cases right : a=d <;> by_cases env : e=f <;>
    simp [Matrix.kronecker,swapOperator,Equiv.Perm.permMatrix,PEquiv.toMatrix_toPEquiv_eq,
      Matrix.one_apply,left,right,env]

theorem full_swap_density (rho : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    conjugation (Load.Quantum.localUnitary (Exchange.fullTransfer (ι := ι)) (1 : Matrix.unitaryGroup κ ℂ)) rho =
      rho.submatrix (fun i => ((i.1.2,i.1.1),i.2)) (fun i => ((i.1.2,i.1.1),i.2)) := by
  let e : Equiv.Perm ((ι × ι) × κ) := Equiv.prodCongr (Equiv.prodComm ι ι) (Equiv.refl κ)
  have value : (Load.Quantum.localUnitary (Exchange.fullTransfer (ι := ι)) (1 : Matrix.unitaryGroup κ ℂ) :
      Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ)=(-Complex.I) • e.permMatrix ℂ := by
    change Matrix.kronecker (Exchange.fullTransfer (ι := ι) : JointMatrix ι) (1 : Matrix κ κ ℂ)=_
    rw [full_transfer_matrix]
    simp only [Matrix.kronecker,Matrix.smul_kronecker]
    exact congrArg (fun A : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ => (-Complex.I) • A)
      (tensor_swap_permutation (ι := ι) (κ := κ))
  rw [conjugation_apply,value]
  simp only [star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  simp only [star_neg,Complex.star_def,Complex.conj_I,neg_neg]
  norm_num
  ext i j
  rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_permMatrix]
  change (e.toPEquiv.toMatrix*rho*(e⁻¹).toPEquiv.toMatrix : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) i j=_
  rw [PEquiv.mul_toMatrix_toPEquiv,PEquiv.toMatrix_toPEquiv_mul]
  rfl

theorem full_swap_body_read (body : Matrix (ι × κ) (ι × κ) ℂ) (donor : Matrix ι ι ℂ) :
    Incidence.bodyRead
      (conjugation (Load.Quantum.localUnitary (Exchange.fullTransfer (ι := ι)) (1 : Matrix.unitaryGroup κ ℂ))
        (Incidence.receivedJoint body donor)) =
      Matrix.kronecker donor (Powered.Dynamics.controllerReduce body) := by
  rw [full_swap_density]
  ext ⟨a,e⟩ ⟨b,f⟩
  change (∑ d : ι, body (d,e) (d,f)*donor a b)=donor a b*(∑ d : ι, body (d,e) (d,f))
  rw [← Finset.sum_mul,mul_comm]
end SwappedBody

theorem full_free_body_read (time : ℝ) (rho : Current.FullJoint) :
    Incidence.bodyRead (conjugation (fullFree time) rho)=conjugation (freeLoad time) (Incidence.bodyRead rho) := by
  rw [← full_free_lift,Incidence.localLift_read]

theorem ideal_supply_body_read (time : ℝ) (body : LoadedJoint)
    (donor : Matrix PairController PairController ℂ) :
    Incidence.bodyRead (conjugation (idealSupply time) (Incidence.receivedJoint body donor)) =
      Matrix.kronecker (conjugation (Native.freePCUnitary time) donor)
        (conjugation (Load.Recovery.Control.environmentUnitary time) (Powered.Dynamics.controllerReduce body)) := by
  rw [ideal_supply_factor,← Environment.conjugation_comp,full_free_body_read,fullSwap,full_swap_body_read]
  exact Load.Quantum.localConjugation_tensor _ _ _ _

private theorem energy_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (H rho : Matrix κ κ ℂ) :
    energy (H.submatrix e e) (rho.submatrix e e)=energy H rho := by
  unfold energy
  rw [Matrix.submatrix_mul_equiv]
  exact congrArg Complex.re (Equiv.sum_comp e (fun i => (H*rho) i i))

theorem boundary_diagonal_controller (R : Matrix Pair Pair ℂ) (d : Fin 2 → ℂ)
    (E : Matrix (Fin 2) (Fin 2) ℂ) :
    energy loadInteraction (Matrix.kronecker (Matrix.kronecker R (Matrix.diagonal d)) E)=0 := by
  let e := Equiv.prodAssoc Pair (Fin 2) (Fin 2)
  have state : Matrix.kronecker (Matrix.kronecker R (Matrix.diagonal d)) E=
      (Matrix.kronecker R (Matrix.kronecker (Matrix.diagonal d) E)).submatrix e e := by
    ext i j
    change (R i.1.1 j.1.1 * Matrix.diagonal d i.1.2 j.1.2)*E i.2 j.2 =
      R i.1.1 j.1.1*(Matrix.diagonal d i.1.2 j.1.2*E i.2 j.2)
    ring
  rw [state]
  change energy ((Matrix.kronecker (1 : Matrix Pair Pair ℂ) controllerEnvironmentExchange).submatrix e e)
    ((Matrix.kronecker R (Matrix.kronecker (Matrix.diagonal d) E)).submatrix e e)=0
  rw [energy_reindex]
  have small : (controllerEnvironmentExchange*Matrix.kronecker (Matrix.diagonal d) E).trace=0 := by
    norm_num [controllerEnvironmentExchange,Matrix.trace,Matrix.diag,Matrix.mul_apply,
      Matrix.kronecker,Matrix.kroneckerMap_apply,Fintype.sum_prod_type,Fin.sum_univ_two,
      Matrix.single_apply,Matrix.diagonal_apply]
  simp only [energy,Matrix.kronecker,← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.trace_kronecker]
  change (R.trace*(controllerEnvironmentExchange*Matrix.kronecker (Matrix.diagonal d) E).trace).re=0
  rw [small,mul_zero,Complex.zero_re]

def barePair (time : ℝ) : Matrix.unitaryGroup Pair ℂ :=
  Dynamics.pairUnitary Thermal.Source.energyHamiltonian Thermal.Source.energyHamiltonian_hermitian
    Thermal.Source.pairCoupling time

theorem bare_pc_factor (time : ℝ) :
    barePC time=Load.Quantum.localUnitary (barePair time) (Load.Recovery.Control.environmentUnitary time) := by
  apply Subtype.ext
  rw [barePC,Load.Producer.StrictThermal.flowUnitary_matrix_exp]
  change NormedSpace.exp (time • (-Complex.I • (Powered.Dynamics.bareHamiltonian Work.Drive.fieldBaseline 2+0))) =
    Matrix.kronecker (Dynamics.pairPropagatorMatrix Thermal.Source.energyHamiltonian Thermal.Source.pairCoupling time)
      (NormedSpace.exp (time • (-Complex.I • Powered.Dynamics.controllerHamiltonian 2)))
  rw [add_zero,Dynamics.pairPropagatorMatrix_eq_exp]
  have scalar : (-Complex.I*(time : ℂ)) • Work.Drive.fieldBaseline=time • (-Complex.I • Work.Drive.fieldBaseline) := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
    ring
  change NormedSpace.exp (time • (-Complex.I • Powered.Dynamics.bareHamiltonian Work.Drive.fieldBaseline 2)) =
    Matrix.kronecker (NormedSpace.exp ((-Complex.I*(time : ℂ)) • Work.Drive.fieldBaseline)) _
  rw [scalar]
  have split : time • (-Complex.I • Powered.Dynamics.bareHamiltonian Work.Drive.fieldBaseline 2)=
      Matrix.kronecker (time • (-Complex.I • Work.Drive.fieldBaseline)) (1 : Matrix (Fin 2) (Fin 2) ℂ)+
      Matrix.kronecker (1 : Matrix Pair Pair ℂ) (time • (-Complex.I • Powered.Dynamics.controllerHamiltonian 2)) := by
    ext i j
    simp only [Powered.Dynamics.bareHamiltonian,Matrix.smul_apply,Matrix.add_apply,
      Matrix.kronecker,Matrix.kroneckerMap_apply,Complex.real_smul]
    ring
  rw [split,Load.Recovery.Control.exp_tensor_sum]

theorem environment_diagonal_fixed (time : ℝ) (d : Fin 2 → ℂ) :
    conjugation (Load.Recovery.Control.environmentUnitary time) (Matrix.diagonal d)=Matrix.diagonal d := by
  have commute : Commute (Matrix.diagonal d)
      (Load.Recovery.Control.environmentUnitary time : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Load.Recovery.Control.environmentUnitary_diagonal]
    exact Matrix.commute_diagonal _ _
  rw [conjugation_apply,← commute.eq,Matrix.mul_assoc,
    Unitary.mul_star_self_of_mem (Load.Recovery.Control.environmentUnitary time).property,Matrix.mul_one]

theorem bare_pc_diagonal_controller (time : ℝ) (R : Matrix Pair Pair ℂ) (d : Fin 2 → ℂ) :
    conjugation (barePC time) (Matrix.kronecker R (Matrix.diagonal d))=
      Matrix.kronecker (conjugation (barePair time) R) (Matrix.diagonal d) := by
  rw [bare_pc_factor]
  change Load.Quantum.localConjugation (barePair time) (Load.Recovery.Control.environmentUnitary time)
    (Matrix.kronecker R (Matrix.diagonal d))=_
  rw [Load.Quantum.localConjugation_tensor,environment_diagonal_fixed]

theorem free_boundary_energy_error (time : ℝ) (rho : LoadedJoint) (positive : rho.PosSemidef) :
    |energy loadInteraction (conjugation (freeLoad time) rho)-energy loadInteraction rho| ≤
      105 * |time| * rho.trace.re := by
  have pulled : energy loadInteraction (conjugation (freeLoad time) rho)=
      energy (conjugation (star (freeLoad time)) loadInteraction) rho :=
    Load.Producer.StrictThermal.energy_pullback _ _ _
  rw [pulled,← Load.Producer.HeatProbability.energy_sub_left]
  have bound := energy_norm_mass (conjugation (star (freeLoad time)) loadInteraction-loadInteraction) rho positive
  exact bound.trans (mul_le_mul_of_nonneg_right (free_load_boundary_response time)
    (Complex.nonneg_iff.mp positive.trace_nonneg).1)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.FreeHistory
