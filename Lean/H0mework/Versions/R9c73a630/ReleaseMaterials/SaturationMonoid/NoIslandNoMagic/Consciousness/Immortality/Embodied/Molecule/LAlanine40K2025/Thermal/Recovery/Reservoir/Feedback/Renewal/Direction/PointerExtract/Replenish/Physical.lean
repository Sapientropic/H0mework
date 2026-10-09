import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Readout
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Physical
open Collision Quantum Resource Propagation.Interface Propagation.Producer Load.Source
open Load.Producer.StrictThermal Blocks Blocks.EnergyFrame Inverse.Scaled.Finite
open Replenish.Readout
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def donorLift (H : Matrix PairController PairController ℂ) : Current.FullJoint :=
  Matrix.kronecker (Matrix.kronecker (1 : Matrix PairController PairController ℂ) H)
    (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem donor_lift_norm (H : Matrix PairController PairController ℂ) : ‖donorLift H‖ ≤ ‖H‖ :=
  (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController × PairController) (κ := Fin 2)) _).trans
    (NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := PairController) (κ := PairController)) H)

theorem donor_lift_covariance (U : Matrix.unitaryGroup PairController ℂ) (H : Matrix PairController PairController ℂ) :
    conjugation (spectatorFrame (Quantum.localUnitary U U)) (donorLift H)=donorLift (conjugation U H) := by
  rw [donorLift,spectator_conjugation]
  change Matrix.kronecker (Quantum.localConjugation U U (Matrix.kronecker (1 : Matrix PairController PairController ℂ) H))
    (1 : Matrix (Fin 2) (Fin 2) ℂ)=_
  rw [Quantum.localConjugation_tensor]
  have one : conjugation U (1 : Matrix PairController PairController ℂ)=1 := map_one (Unitary.conjStarAlgAut ℂ _ U)
  rw [one]
  rfl

theorem right_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (H : Matrix ι ι ℂ) :
    conjugation (blockUnitary U U) (rightBlock H)=rightBlock (conjugation U H) := by
  change (blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)*Matrix.fromBlocks 0 0 0 H*
    star (blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)=_
  rw [blockUnitary_conjugation_blocks]
  simp [rightBlock,conjugation_apply]

theorem right_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    energy (rightBlock H) rho=energy H rho.toBlocks₂₂ := by
  conv_lhs => arg 2; rw [← Matrix.fromBlocks_toBlocks rho]
  simp [energy,rightBlock,Matrix.fromBlocks_multiply,trace_fromBlocks]

private theorem tensor_right_energy {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι ι ℂ)
    (rho : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    energy (Matrix.kronecker (Matrix.kronecker (1 : Matrix ι ι ℂ) H) (1 : Matrix κ κ ℂ)) rho =
      energy H (Collision.bathReduce (Powered.Dynamics.systemReduce rho)) := by
  have outer := Powered.Dynamics.jointEnergy_real_eq_reduced
    (Matrix.kronecker (1 : Matrix ι ι ℂ) H) (0 : Matrix κ κ ℂ) rho
  have first : energy (Matrix.kronecker (Matrix.kronecker (1 : Matrix ι ι ℂ) H)
      (1 : Matrix κ κ ℂ)) rho =
      energy (Matrix.kronecker (1 : Matrix ι ι ℂ) H)
        (Powered.Dynamics.systemReduce rho) := by
    simpa [energy, Matrix.kronecker] using outer
  rw [first]
  simpa [energy,Matrix.kronecker,Powered.Dynamics.controllerReduce,Collision.bathReduce] using
    Powered.Dynamics.jointEnergy_real_eq_reduced (0 : Matrix ι ι ℂ) H (Powered.Dynamics.systemReduce rho)

theorem donor_lift_energy (H : Matrix PairController PairController ℂ) (rho : Current.FullJoint) :
    energy (donorLift H) rho=energy H (donorMatrixOf rho) := tensor_right_energy H rho

theorem source_right : suppliedBlock Replenish.origin=
    conjugation (Extract.fullPulse (nativeClockStep : ℝ)) (suppliedBlock Weak.execution) := by
  unfold suppliedBlock
  rw [Replenish.origin_joint]
  change (Extract.next Weak.execution).joint.toBlocks₂₂=_
  rw [Extract.next_joint,Extract.pointerPulse,controlled_block_right]

theorem source_right_pc : pcMatrixOf (suppliedBlock Replenish.origin)=
    conjugation Source.sourceExtraction (pcMatrixOf (suppliedBlock Weak.execution)) := by
  rw [source_right,Extract.full_pc]
  exact Extraction.pulse_clock_conjugation _ _ _ (by exact_mod_cast nativeClockStep_positive.ne') _

theorem source_right_donor : donorMatrixOf (suppliedBlock Replenish.origin)=
    donorMatrixOf (suppliedBlock Weak.execution) := by rw [source_right,Extract.full_donor]

theorem source_right_mass : (suppliedBlock Replenish.origin).trace=(suppliedBlock Weak.execution).trace := by
  rw [source_right,conjugation_trace]

private theorem ground_after_extraction {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    energy (Spectrum.spectralPure H hH Spectrum.lastIndex)
      (conjugation (Spectrum.extraction H hH) rho)=energy (Spectrum.reservoirState H hH) rho := by
  have both := Work.Capacity.energy_unitary_conjugation (Spectrum.reservoirState H hH) rho (Spectrum.extraction H hH)
  rw [Spectrum.extraction_acts] at both
  exact both

theorem source_right_ground : energy Replenish.groundProjector (pcMatrixOf (suppliedBlock Replenish.origin))=
    energy Source.donor (pcMatrixOf (suppliedBlock Weak.execution)) := by
  rw [source_right_pc]
  exact ground_after_extraction _ _ _

private theorem conjugation_forward_back {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (O : Matrix ι ι ℂ) :
    conjugation U (conjugation (star U) O)=O := by
  change Unitary.conjStarAlgAut ℂ _ U (Unitary.conjStarAlgAut ℂ _ (star U) O)=O
  rw [← Unitary.conjStarAlgAut_symm]
  exact StarAlgEquiv.apply_symm_apply _ _

private theorem conjugation_back_forward {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (O : Matrix ι ι ℂ) :
    conjugation (star U) (conjugation U O)=O := by
  simpa only [star_star] using conjugation_forward_back (star U) O

theorem original_top_observable : originalObservable topObservable=
    rightBlock (Post.pcLift Supply.sourceFiniteDonor) := by
  have cov : conjugation Post.pointerFrame (rightBlock (Post.pcLift Supply.sourceFiniteDonor))=topObservable := by
    change conjugation (blockUnitary Supply.installedFullFrame Supply.installedFullFrame) _=_
    rw [right_conjugation]
    rw [show conjugation Supply.installedFullFrame (Post.pcLift Supply.sourceFiniteDonor)=
      Post.pcLift (conjugation installedPCFrame Supply.sourceFiniteDonor) from
        Post.pc_lift_covariance _ _,Supply.finite_donor_calculated]
    rfl
  rw [originalObservable,← cov,conjugation_back_forward]

theorem right_sub {ι : Type*} (A B : Matrix ι ι ℂ) : rightBlock A-rightBlock B=rightBlock (A-B) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [rightBlock,Matrix.fromBlocks]

theorem pc_lift_sub (A B : Matrix PairController PairController ℂ) : Post.pcLift A-Post.pcLift B=Post.pcLift (A-B) := by
  ext i j
  simp only [Post.pcLift,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
  ring

theorem donor_lift_sub (A B : Matrix PairController PairController ℂ) : donorLift A-donorLift B=donorLift (A-B) := by
  ext i j
  simp only [donorLift,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
  ring

theorem original_right_top_lower : (3709/10000 : ℝ) < energy Source.donor (pcMatrixOf (suppliedBlock Weak.execution)) := by
  have lower := original_top_reference_lower
  rw [original_top_observable,right_energy,Population.pc_lift_energy] at lower
  have delta : ‖rightBlock (Post.pcLift Source.donor)-rightBlock (Post.pcLift Supply.sourceFiniteDonor)‖ ≤ (1/10^9 : ℝ) := by
    rw [right_sub,pc_lift_sub]
    exact (right_norm _).trans ((Post.pc_lift_norm _).trans Supply.original_finite_donor_error)
  have error := (energy_abs_le_norm
    (rightBlock (Post.pcLift Source.donor)-rightBlock (Post.pcLift Supply.sourceFiniteDonor))
    Weak.execution.joint Weak.execution.positive Weak.execution.normalized).trans delta
  rw [Load.Producer.HeatProbability.energy_sub_left,right_energy,right_energy,
    Population.pc_lift_energy,Population.pc_lift_energy] at error
  change |energy Source.donor (pcMatrixOf (suppliedBlock Weak.execution))-
    energy Supply.sourceFiniteDonor (pcMatrixOf (suppliedBlock Weak.execution))| ≤ _ at error
  change (371/1000 : ℝ) < energy Supply.sourceFiniteDonor (pcMatrixOf (suppliedBlock Weak.execution)) at lower
  linarith only [lower,(abs_le.mp error).1]

theorem current_right_ground_lower : (3709/10000 : ℝ) <
    energy Replenish.groundProjector (pcMatrixOf (suppliedBlock Replenish.origin)) := by
  rw [source_right_ground]
  exact original_right_top_lower

private theorem conjugation_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (H : Matrix ι ι ℂ) (r : ℝ) :
    conjugation U (H+r • 1)=conjugation U H+r • 1 := by
  change Unitary.conjStarAlgAut ℂ _ U (H+(r : ℂ) • 1)=Unitary.conjStarAlgAut ℂ _ U H+(r : ℂ) • 1
  rw [map_add,map_smul,map_one]

private theorem conjugation_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ) :
    conjugation U (A-B)=conjugation U A-conjugation U B :=
  map_sub (Unitary.conjStarAlgAut ℂ _ U) A B

def actualDonorObservable : PointerJoint :=
  rightBlock (donorLift (Powered.Producer.poweredTotalHamiltonian+(192/5 : ℝ) • 1))

theorem actual_donor_coordinates : conjugation Post.pointerFrame actualDonorObservable=
    rightBlock (donorLift (conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian+(192/5 : ℝ) • 1)) := by
  change conjugation (blockUnitary Supply.installedFullFrame Supply.installedFullFrame) _=_
  rw [actualDonorObservable,right_conjugation]
  rw [show conjugation Supply.installedFullFrame (donorLift (Powered.Producer.poweredTotalHamiltonian+(192/5 : ℝ) • 1))=
    donorLift (conjugation installedPCFrame (Powered.Producer.poweredTotalHamiltonian+(192/5 : ℝ) • 1)) from
      donor_lift_covariance _ _,conjugation_shift]

theorem donor_observable_error : ‖actualDonorObservable-originalObservable donorObservable‖ ≤ (126/10^12 : ℝ) := by
  have normFrame : ‖conjugation Post.pointerFrame (actualDonorObservable-originalObservable donorObservable)‖=
      ‖actualDonorObservable-originalObservable donorObservable‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ PointerJoint Post.pointerFrame) _
  rw [← normFrame,conjugation_sub,actual_donor_coordinates]
  rw [show conjugation Post.pointerFrame (originalObservable donorObservable)=donorObservable from
    conjugation_forward_back _ _]
  change ‖rightBlock (donorLift (conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian+(192/5 : ℝ) • 1))-
    rightBlock (donorLift (sourcePCH E+(192/5 : ℝ) • 1))‖ ≤ _
  rw [right_sub,donor_lift_sub,add_sub_add_right_eq_sub]
  exact (right_norm _).trans ((donor_lift_norm _).trans actual_powered_Hamiltonian_error)

private theorem shift_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H rho : Matrix ι ι ℂ) (r : ℝ) : energy (H+r • 1) rho=energy H rho+r*rho.trace.re := by
  simp [energy,Matrix.add_mul,Matrix.trace_add,Matrix.trace_smul]

theorem actual_donor_read : energy actualDonorObservable Weak.execution.joint=
    donorEnergyOf (suppliedBlock Weak.execution)+(192/5 : ℝ)*(suppliedBlock Weak.execution).trace.re := by
  rw [actualDonorObservable,right_energy,donor_lift_energy,shift_energy]
  change donorEnergyOf (suppliedBlock Weak.execution)+(192/5 : ℝ)*(donorMatrixOf (suppliedBlock Weak.execution)).trace.re=_
  rw [donorMatrixOf,Collision.bathReduce_trace,Powered.Dynamics.systemReduce_trace]

theorem original_right_donor_lower : (179/25 : ℝ) <
    donorEnergyOf (suppliedBlock Weak.execution)+(192/5 : ℝ)*(suppliedBlock Weak.execution).trace.re := by
  have lower := original_donor_reference_lower
  have error := (energy_abs_le_norm (actualDonorObservable-originalObservable donorObservable)
    Weak.execution.joint Weak.execution.positive Weak.execution.normalized).trans donor_observable_error
  rw [Load.Producer.HeatProbability.energy_sub_left,actual_donor_read] at error
  linarith only [lower,(abs_le.mp error).1]

theorem current_right_donor_lower : (179/25 : ℝ) <
    donorEnergyOf (suppliedBlock Replenish.origin)+(192/5 : ℝ)*(suppliedBlock Replenish.origin).trace.re := by
  unfold donorEnergyOf
  rw [source_right_donor,source_right_mass]
  exact original_right_donor_lower

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Physical
