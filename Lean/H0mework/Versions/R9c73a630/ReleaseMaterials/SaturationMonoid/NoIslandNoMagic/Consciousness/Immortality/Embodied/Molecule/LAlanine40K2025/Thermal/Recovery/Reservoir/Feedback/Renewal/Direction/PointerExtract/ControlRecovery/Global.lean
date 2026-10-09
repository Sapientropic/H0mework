import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Hpc

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery
open Collision Propagation.Interface Load.Source Blocks
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def orientationSign (p : Pair) : ℂ := if p.1 ≤ p.2 then 1 else -1
def orientationPhase : Matrix Pair Pair ℂ := Matrix.diagonal orientationSign
def equalPair : Matrix Pair Pair ℂ :=
  Matrix.diagonal (fun p => if p.1=p.2 then 1 else 0)
def controllerFlip : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

theorem sign_square (p : Pair) : orientationSign p * orientationSign p = 1 := by
  unfold orientationSign
  split_ifs <;> norm_num

theorem sign_star (p : Pair) : star (orientationSign p)=orientationSign p := by
  unfold orientationSign
  split_ifs <;> simp

theorem phase_hermitian : orientationPhase.IsHermitian := by
  ext i j
  simp only [orientationPhase,Matrix.conjTranspose_apply,Matrix.diagonal_apply]
  by_cases same : i=j
  · subst j
    simp [sign_star]
  · simp [same,Ne.symm same]

theorem phase_involution : orientationPhase*orientationPhase=1 := by
  rw [orientationPhase,Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext sign_square)

def phaseUnitary : Matrix.unitaryGroup Pair ℂ :=
  ⟨orientationPhase, Matrix.mem_unitaryGroup_iff.mpr (by
    change orientationPhase*orientationPhaseᴴ=1
    rw [phase_hermitian.eq,phase_involution])⟩

theorem controller_flip_hermitian : controllerFlip.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controllerFlip,Matrix.conjTranspose_apply]

theorem controller_flip_involution : controllerFlip*controllerFlip=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controllerFlip,Matrix.mul_apply,Fin.sum_univ_succ]

def controllerUnitary : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨controllerFlip, Matrix.mem_unitaryGroup_iff.mpr (by
    change controllerFlip*controllerFlipᴴ=1
    rw [controller_flip_hermitian.eq,controller_flip_involution])⟩

def sourceControl : Matrix.unitaryGroup PairController ℂ :=
  ⟨Matrix.kronecker orientationPhase controllerFlip,
    Matrix.kronecker_mem_unitary phaseUnitary.property controllerUnitary.property⟩

theorem source_control_hermitian :
    (sourceControl : Matrix PairController PairController ℂ).IsHermitian := by
  change (Matrix.kronecker orientationPhase controllerFlip)ᴴ=
    Matrix.kronecker orientationPhase controllerFlip
  simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,
    phase_hermitian.eq,controller_flip_hermitian.eq]

theorem source_control_involution :
    (sourceControl : Matrix PairController PairController ℂ) *
      (sourceControl : Matrix PairController PairController ℂ)=1 := by
  have h := Unitary.coe_star_mul_self sourceControl
  change (sourceControl : Matrix PairController PairController ℂ)ᴴ *
    (sourceControl : Matrix PairController PairController ℂ)=1 at h
  rwa [source_control_hermitian.eq] at h

theorem phase_diagonal (d : Pair → ℂ) :
    orientationPhase * Matrix.diagonal d * orientationPhase = Matrix.diagonal d := by
  ext i j
  simp only [orientationPhase,Matrix.mul_diagonal,Matrix.diagonal_apply]
  by_cases same : i=j
  · subst j
    rw [if_pos rfl,if_pos rfl]
    calc orientationSign i*d i*orientationSign i =
        (orientationSign i*orientationSign i)*d i := by ring
      _ = d i := by rw [sign_square,one_mul]
  · simp [same]

theorem phase_swap :
    orientationPhase * (swapOperator : JointMatrix Basis) * orientationPhase =
      -swapOperator + (2 : ℂ) • equalPair := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp only [orientationPhase,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.add_apply,Matrix.neg_apply,Matrix.smul_apply,swap_entry,
    equalPair,Matrix.diagonal_apply,smul_eq_mul]
  by_cases swapped : (b,a)=(c,d)
  · cases swapped
    by_cases same : a=b
    · subst b
      norm_num [orientationSign]
    · have different : (a,b)≠(b,a) := by
        intro h
        exact same (congrArg Prod.fst h)
      simp only [if_neg different,mul_zero,add_zero]
      unfold orientationSign
      by_cases ordered : a≤b
      · rw [if_pos ordered,if_neg (not_le.mpr (lt_of_le_of_ne ordered same))]
        norm_num
      · rw [if_neg ordered,if_pos (le_of_lt (lt_of_not_ge ordered))]
        norm_num
  · by_cases diagonal : (a,b)=(c,d)
    · cases diagonal
      have different : a≠b := by
        intro same
        subst b
        exact swapped rfl
      simp [swapped,different]
    · simp [swapped,diagonal]

theorem free_pair_diagonal (d : Basis → ℂ) :
    Dynamics.freePairH (Matrix.diagonal d) =
      Matrix.diagonal (fun p : Pair => d p.1 + d p.2) := by
  ext ⟨a,b⟩ ⟨c,e⟩
  by_cases left : a=c <;> by_cases right : b=e <;>
    simp [Dynamics.freePairH,jointHamiltonian,Matrix.kronecker,Matrix.diagonal,
      left,right]

theorem phase_pair (d : Basis → ℂ) :
    orientationPhase * Dynamics.pairH (Matrix.diagonal d) 1 * orientationPhase =
      Dynamics.freePairH (Matrix.diagonal d) - swapOperator + (2 : ℂ) • equalPair := by
  simp only [Dynamics.pairH,Complex.ofReal_one,one_smul,mul_add,add_mul,
    free_pair_diagonal,phase_diagonal,phase_swap]
  module

theorem phase_raising (e : Basis → ℝ) :
    orientationPhase * Powered.Source.raising (Matrix.diagonal (fun i => (e i : ℂ))) *
      orientationPhase =
        (Powered.Source.raising (Matrix.diagonal (fun i => (e i : ℂ))))ᴴ := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp only [orientationPhase,Matrix.mul_diagonal,Matrix.diagonal_mul,
    Matrix.conjTranspose_apply,raising_entry]
  by_cases same : (a,b)=(c,d)
  · cases same
    by_cases diagonal : a=b
    · subst b
      simp
    · have swapDifferent : (b,a)≠(a,b) := by
        intro h
        exact diagonal (congrArg Prod.snd h)
      by_cases ordered : a≤b <;>
        norm_num [orientationSign,swapDifferent,ordered]
  · by_cases swapped : (b,a)=(c,d)
    · cases swapped
      have reverseDifferent : (b,a)≠(a,b) := Ne.symm same
      have diagonal : a≠b := by
        intro h
        subst b
        exact same rfl
      by_cases ordered : a≤b
      · norm_num [orientationSign,same,reverseDifferent,ordered,
          not_le.mpr (lt_of_le_of_ne ordered diagonal)]
        ring
      · norm_num [orientationSign,same,reverseDifferent,ordered,
          le_of_lt (lt_of_not_ge ordered)]
        ring
    · have reverseSame : (c,d)≠(a,b) := Ne.symm same
      have reverseSwap : (d,c)≠(a,b) := by
        intro h
        exact swapped (Prod.ext (congrArg Prod.snd h).symm (congrArg Prod.fst h).symm)
      simp [same,swapped,reverseSame,reverseSwap]

theorem controller_flip_lowering :
    controllerFlip * Powered.Source.lowering * controllerFlip =
      Powered.Source.loweringᴴ := by
  ext i j
  simp only [Matrix.mul_apply,Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;>
    norm_num [controllerFlip,Powered.Source.lowering,Matrix.conjTranspose_apply,
      Matrix.single_apply]

theorem controller_flip_energy :
    Powered.Dynamics.controllerHamiltonian 2 -
      controllerFlip * Powered.Dynamics.controllerHamiltonian 2 * controllerFlip =
        Matrix.diagonal (![-2,2] : Fin 2 → ℂ) := by
  ext i j
  change Powered.Dynamics.controllerHamiltonian 2 i j -
    (controllerFlip * Powered.Dynamics.controllerHamiltonian 2 * controllerFlip) i j = _
  simp only [Matrix.mul_apply,Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;>
    norm_num [controllerFlip,Powered.Dynamics.controllerHamiltonian,Matrix.diagonal_apply]

theorem control_tensor (A : Matrix Pair Pair ℂ) (C : Matrix (Fin 2) (Fin 2) ℂ) :
    Quantum.conjugation sourceControl (Matrix.kronecker A C) =
      Matrix.kronecker (orientationPhase*A*orientationPhase)
        (controllerFlip*C*controllerFlip) := by
  rw [Quantum.conjugation_apply]
  change Matrix.kronecker orientationPhase controllerFlip * Matrix.kronecker A C *
    (Matrix.kronecker orientationPhase controllerFlip)ᴴ = _
  simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,
    phase_hermitian.eq,controller_flip_hermitian.eq,← Matrix.mul_kronecker_mul]

theorem control_transfer (e : Basis → ℝ) :
    Quantum.conjugation sourceControl
      (Powered.Source.transfer (Matrix.diagonal (fun i => (e i : ℂ)))) =
        (Powered.Source.transfer (Matrix.diagonal (fun i => (e i : ℂ))))ᴴ := by
  rw [Powered.Source.transfer,control_tensor,phase_raising,controller_flip_lowering]
  exact (Matrix.conjTranspose_kronecker _ _).symm

theorem control_interaction (e : Basis → ℝ) :
    Quantum.conjugation sourceControl
      (Powered.Source.interaction (Matrix.diagonal (fun i => (e i : ℂ)))) =
        Powered.Source.interaction (Matrix.diagonal (fun i => (e i : ℂ))) := by
  let T := Powered.Source.transfer (Matrix.diagonal (fun i => (e i : ℂ)))
  change Quantum.conjugation sourceControl (T+Tᴴ) = T+Tᴴ
  rw [map_add]
  have adjoint := map_star (Unitary.conjStarAlgAut ℂ _ sourceControl) T
  change Quantum.conjugation sourceControl Tᴴ = (Quantum.conjugation sourceControl T)ᴴ at adjoint
  rw [adjoint]
  change Quantum.conjugation sourceControl
    (Powered.Source.transfer (Matrix.diagonal (fun i => (e i : ℂ)))) +
    (Quantum.conjugation sourceControl
      (Powered.Source.transfer (Matrix.diagonal (fun i => (e i : ℂ)))))ᴴ = _
  rw [control_transfer,Matrix.conjTranspose_conjTranspose]
  exact add_comm _ _

def globalWork : Matrix PairController PairController ℂ :=
  (2 : ℂ) • Matrix.kronecker ((swapOperator : JointMatrix Basis)-equalPair) 1 +
    Matrix.kronecker (1 : Matrix Pair Pair ℂ) (Matrix.diagonal (![-2,2] : Fin 2 → ℂ))

theorem control_work (e : Basis → ℝ) :
    let H := Powered.Dynamics.totalHamiltonian
      (Dynamics.pairH (Matrix.diagonal (fun i => (e i : ℂ))) 1) 2
      (Powered.Source.interaction (Matrix.diagonal (fun i => (e i : ℂ))))
    H - Quantum.conjugation sourceControl H = globalWork := by
  dsimp only
  rw [Powered.Dynamics.totalHamiltonian,map_add,control_interaction]
  simp only [Powered.Dynamics.bareHamiltonian,map_add,control_tensor,Matrix.mul_one,
    phase_involution,controller_flip_involution,phase_pair]
  have controller :
      controllerFlip * Powered.Dynamics.controllerHamiltonian 2 * controllerFlip =
        Powered.Dynamics.controllerHamiltonian 2-Matrix.diagonal (![-2,2] : Fin 2 → ℂ) := by
    calc
      _ = Powered.Dynamics.controllerHamiltonian 2 -
          (Powered.Dynamics.controllerHamiltonian 2 -
            controllerFlip * Powered.Dynamics.controllerHamiltonian 2 * controllerFlip) := by abel
      _ = _ := by rw [controller_flip_energy]
  rw [controller]
  ext i j
  simp only [Dynamics.pairH,Complex.ofReal_one,one_smul,globalWork,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem original_control_work :
    Powered.Producer.poweredTotalHamiltonian -
      Quantum.conjugation sourceControl Powered.Producer.poweredTotalHamiltonian =
        globalWork := control_work Preparation.sourceEnergies

theorem equal_pair_adjoint : equalPairᴴ=equalPair := by
  ext i j
  by_cases same : i=j
  · subst j
    simp only [equalPair,Matrix.conjTranspose_apply,Matrix.diagonal_apply]
    split_ifs <;> simp
  · simp [equalPair,Matrix.conjTranspose_apply,same,Ne.symm same]

theorem equal_pair_squared : equalPair*equalPair=equalPair := by
  rw [equalPair,Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext p
  split_ifs <;> norm_num

theorem swap_equal_pair : (swapOperator : JointMatrix Basis)*equalPair=equalPair := by
  ext ⟨a,b⟩ ⟨c,d⟩
  rw [swap_mul_apply]
  by_cases same : a=b
  · subst b
    rfl
  · have reverse : b≠a := Ne.symm same
    simp [equalPair,Matrix.diagonal_apply,same,reverse]

theorem equal_pair_swap : equalPair*(swapOperator : JointMatrix Basis)=equalPair := by
  have h := congrArg Matrix.conjTranspose swap_equal_pair
  simpa only [Matrix.conjTranspose_mul,swap_adjoint,equal_pair_adjoint] using h

def offSymmetric : JointMatrix Basis := 1+swapOperator-(2 : ℂ) • equalPair

theorem off_symmetric_hermitian : offSymmetric.IsHermitian := by
  change offSymmetricᴴ=offSymmetric
  simp [offSymmetric,Matrix.conjTranspose_smul,swap_adjoint,equal_pair_adjoint]

theorem off_symmetric_squared : offSymmetric*offSymmetric=(2 : ℂ) • offSymmetric := by
  simp only [offSymmetric,Matrix.sub_mul,Matrix.mul_sub,Matrix.add_mul,Matrix.mul_add,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,
    equal_pair_squared,swap_equal_pair,equal_pair_swap,swap_squared]
  module

theorem off_symmetric_positive : offSymmetric.PosSemidef := by
  have positive := (Matrix.posSemidef_conjTranspose_mul_self offSymmetric).smul
    (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [off_symmetric_hermitian.eq,off_symmetric_squared] at positive
  have same : (1/2 : ℝ) • ((2 : ℂ) • offSymmetric)=offSymmetric := by
    ext i j
    simp [Complex.real_smul]
  rwa [same] at positive

theorem charged_work_read (rho : JointMatrix Basis) :
    energy globalWork (Powered.Dynamics.chargedInput rho) =
      2*rho.trace.re + 2*energy ((swapOperator : JointMatrix Basis)-equalPair) rho := by
  simp only [globalWork,Powered.Dynamics.chargedInput,energy,Matrix.add_mul,
    Matrix.smul_mul,Matrix.trace_add,Matrix.trace_smul,Matrix.kronecker,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.trace_kronecker]
  have charged : (Matrix.diagonal (![-2,2] : Fin 2 → ℂ) *
      Powered.Dynamics.excitedController).trace=2 := by
    norm_num [Powered.Dynamics.excitedController,Matrix.diagonal_mul_diagonal,
      Matrix.trace_diagonal,Fin.sum_univ_two]
  rw [charged,Powered.Dynamics.excitedController_trace,mul_one]
  simp [Complex.mul_re]
  ring

theorem charged_work_lower (rho : JointMatrix Basis) (positive : rho.PosSemidef) :
    rho.trace.re + energy (swapOperator : JointMatrix Basis) rho ≤
      energy globalWork (Powered.Dynamics.chargedInput rho) := by
  have residual := QuadraticEnergy.positive_energy offSymmetric rho off_symmetric_positive positive
  rw [charged_work_read]
  simp only [offSymmetric,energy,Matrix.sub_mul,Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,
    Matrix.trace_sub,Matrix.trace_add,Matrix.trace_smul,Complex.sub_re,Complex.add_re] at residual ⊢
  norm_num at residual ⊢
  linarith only [residual]

theorem pair_work_norm : ‖(swapOperator : JointMatrix Basis)-equalPair‖ ≤ 1 := by
  let A : JointMatrix Basis := swapOperator-equalPair
  have hermitian : A.IsHermitian := by
    change (swapOperator-equalPair)ᴴ=swapOperator-equalPair
    rw [Matrix.conjTranspose_sub,swap_adjoint,equal_pair_adjoint]
  have square : A*A=1-equalPair := by
    simp only [A,Matrix.sub_mul,Matrix.mul_sub,equal_pair_squared,swap_equal_pair,
      equal_pair_swap,swap_squared]
    module
  have diagonal : (1 : JointMatrix Basis)-equalPair=
      Matrix.diagonal (fun p : Pair => if p.1=p.2 then (0 : ℂ) else 1) := by
    ext i j
    by_cases same : i=j
    · subst j
      simp only [Matrix.sub_apply,Matrix.one_apply,equalPair,Matrix.diagonal_apply]
      split_ifs <;> norm_num
    · simp [equalPair,Matrix.sub_apply,same]
  have normSquare : ‖A*A‖ ≤ 1 := by
    rw [square,diagonal,Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro p
    split_ifs <;> simp
  rw [hermitian.isSelfAdjoint.norm_mul_self] at normSquare
  change ‖A‖ ≤ 1
  nlinarith [norm_nonneg A]

theorem global_work_norm : ‖globalWork‖ ≤ 4 := by
  have left := NonUnitalStarAlgHom.norm_apply_le
    (Load.Producer.StrictThermal.tensorLeft (ι := Pair) (κ := Fin 2))
    ((swapOperator : JointMatrix Basis)-equalPair)
  have right := NonUnitalStarAlgHom.norm_apply_le
    (Load.Producer.StrictThermal.tensorRight (ι := Pair) (κ := Fin 2))
    (Matrix.diagonal (![-2,2] : Fin 2 → ℂ))
  have controller : ‖Matrix.diagonal (![-2,2] : Fin 2 → ℂ)‖ ≤ 2 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    fin_cases i <;> norm_num
  have estimate := norm_add_le
    ((2 : ℂ) • Matrix.kronecker ((swapOperator : JointMatrix Basis)-equalPair) (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (Matrix.kronecker (1 : Matrix Pair Pair ℂ) (Matrix.diagonal (![-2,2] : Fin 2 → ℂ)))
  rw [norm_smul] at estimate
  norm_num at estimate
  change ‖Matrix.kronecker ((swapOperator : JointMatrix Basis)-equalPair) (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ _ at left
  change ‖Matrix.kronecker (1 : Matrix Pair Pair ℂ) (Matrix.diagonal (![-2,2] : Fin 2 → ℂ))‖ ≤ _ at right
  change ‖globalWork‖ ≤ _ at estimate
  simp only [Matrix.kronecker] at left right
  linarith only [estimate,left,right,controller,pair_work_norm]

def transportedControl (U : Matrix.unitaryGroup PairController ℂ) :
    Matrix.unitaryGroup PairController ℂ := U*sourceControl*star U

def transportedWork (U : Matrix.unitaryGroup PairController ℂ) :
    Matrix PairController PairController ℂ := Quantum.conjugation U globalWork

theorem base_work_readout (rho : Matrix PairController PairController ℂ) :
    energy Powered.Producer.poweredTotalHamiltonian rho -
      energy Powered.Producer.poweredTotalHamiltonian (Quantum.conjugation sourceControl rho) =
        energy globalWork rho := by
  have starControl : star sourceControl=sourceControl := by
    apply Subtype.ext
    exact source_control_hermitian
  have pulled : energy Powered.Producer.poweredTotalHamiltonian (Quantum.conjugation sourceControl rho)=
      energy (Quantum.conjugation (star sourceControl) Powered.Producer.poweredTotalHamiltonian) rho :=
    Load.Producer.StrictThermal.energy_pullback _ _ _
  rw [pulled,starControl,← original_control_work]
  simp only [energy,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re]

theorem transported_work_readout (U : Matrix.unitaryGroup PairController ℂ)
    (conserved : ∀ rho : Matrix PairController PairController ℂ,
      energy Powered.Producer.poweredTotalHamiltonian (Quantum.conjugation U rho)=
        energy Powered.Producer.poweredTotalHamiltonian rho)
    (rho : Matrix PairController PairController ℂ) :
    energy Powered.Producer.poweredTotalHamiltonian rho -
      energy Powered.Producer.poweredTotalHamiltonian (Quantum.conjugation (transportedControl U) rho) =
        energy (transportedWork U) rho := by
  have inverse : Quantum.conjugation U (Quantum.conjugation (star U) rho)=rho := by
    change Unitary.conjStarAlgAut ℂ _ U (Unitary.conjStarAlgAut ℂ _ (star U) rho)=_
    rw [← Unitary.conjStarAlgAut_symm]
    exact (Unitary.conjStarAlgAut ℂ _ U).apply_symm_apply rho
  have before := conserved (Quantum.conjugation (star U) rho)
  rw [inverse] at before
  have after : Quantum.conjugation (transportedControl U) rho =
      Quantum.conjugation U (Quantum.conjugation sourceControl (Quantum.conjugation (star U) rho)) := by
    change Unitary.conjStarAlgAut ℂ _ (U*sourceControl*star U) rho=_
    rw [Unitary.conjStarAlgAut_mul_apply,Unitary.conjStarAlgAut_mul_apply]
    rfl
  rw [before,after,conserved,base_work_readout]
  change energy globalWork (Unitary.conjStarAlgAut ℂ _ (star U) rho)=
    energy (Unitary.conjStarAlgAut ℂ _ U globalWork) rho
  have pulled := Load.Producer.StrictThermal.energy_pullback globalWork rho (star U)
  simpa only [star_star] using pulled

theorem transported_work_norm (U : Matrix.unitaryGroup PairController ℂ) :
    ‖transportedWork U‖ ≤ 4 := by
  have same : ‖transportedWork U‖=‖globalWork‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ _ U) globalWork
  rw [same]
  exact global_work_norm

theorem transported_reference_read (U : Matrix.unitaryGroup PairController ℂ)
    (rho : Matrix PairController PairController ℂ) :
    energy (transportedWork U) (Quantum.conjugation U rho)=energy globalWork rho := by
  change (Unitary.conjStarAlgAut ℂ _ U globalWork *
    Unitary.conjStarAlgAut ℂ _ U rho).trace.re=(globalWork*rho).trace.re
  rw [← map_mul]
  exact congrArg Complex.re (Quantum.conjugation_trace U (globalWork*rho))

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery
