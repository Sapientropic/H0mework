import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMAuxiliaryInverseMatrix
import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMAuxiliaryFeedback
open ActualDressedEMNativeAuxiliary ActualEMAction
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockVector ActualDressedEMZeroClockColumns
open ActualDressedZeroClockFrequency ActualDressedEMQuantumThreshold
open LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

def correctedFullJacobi (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ) := emOriginalJacobi p-Q

def correctedRestRest (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ) :=
  (correctedFullJacobi p Q).submatrix nativeRestIndex nativeRestIndex

def correctedRestAuxiliary (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ) :=
  (correctedFullJacobi p Q).submatrix nativeRestIndex gaugeAuxiliaryIndex

def correctedAuxiliaryRest (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ) :=
  (correctedFullJacobi p Q).submatrix gaugeAuxiliaryIndex nativeRestIndex

def correctedAuxiliaryPencil (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ) :=
  (correctedFullJacobi p Q).submatrix gaugeAuxiliaryIndex gaugeAuxiliaryIndex

/-- The complete original Q_BB enters the source-normalized auxiliary feedback loop. -/
def auxiliaryFeedbackLoop (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ) :=
  nativeAuxiliaryInverseMatrix*correctedAuxiliaryPencil p Q

/-- Adjugate elimination keeps the actual auxiliary chart factor without dividing it. -/
def clearedCorrectedSchur (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ) :=
  (auxiliaryFeedbackLoop p Q).det • correctedRestRest p Q-
    correctedRestAuxiliary p Q*(auxiliaryFeedbackLoop p Q).adjugate*
      nativeAuxiliaryInverseMatrix*correctedAuxiliaryRest p Q

theorem actual_auxiliary_feedback_loop (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ) :
    auxiliaryFeedbackLoop p Q=1-nativeAuxiliaryInverseMatrix*
      Q.submatrix gaugeAuxiliaryIndex gaugeAuxiliaryIndex := by
  change nativeAuxiliaryInverseMatrix*(originalGaugeAuxiliaryPencil p-
    Q.submatrix gaugeAuxiliaryIndex gaugeAuxiliaryIndex)=_
  rw [Matrix.mul_sub,actual_native_auxiliary_matrix_left]

private theorem cleared_schur_kernel {R B : Type*} [Fintype R] [Fintype B] [DecidableEq B]
    (A : Matrix R R ℂ) (G : Matrix R B ℂ) (C : Matrix B R ℂ) (D W : Matrix B B ℂ)
    (r : R → ℂ) (b : B → ℂ) (top : A*ᵥr+G*ᵥb=0) (bottom : C*ᵥr+D*ᵥb=0) :
    ((W*D).det • A-G*(W*D).adjugate*W*C)*ᵥr=0 := by
  let L := W*D
  have forced : D*ᵥb=-(C*ᵥr) := by
    exact add_eq_zero_iff_eq_neg.mp (by simpa only [add_comm] using bottom)
  have pay : L.det • b=-((L.adjugate*W*C)*ᵥr) := by
    calc
      _=(L.adjugate*L)*ᵥb := by rw [Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]
      _=L.adjugate*ᵥ(W*ᵥ(D*ᵥb)) := by simp only [L,Matrix.mulVec_mulVec]
      _=-((L.adjugate*W*C)*ᵥr) := by
        rw [forced]
        simp only [Matrix.mulVec_neg,Matrix.mulVec_mulVec,Matrix.mul_assoc]
  have eliminate : L.det • (G*ᵥb)=-((G*L.adjugate*W*C)*ᵥr) := by
    rw [← Matrix.mulVec_smul,pay]
    simp only [Matrix.mulVec_neg,Matrix.mulVec_mulVec,Matrix.mul_assoc]
  have scaled := congrArg (fun v : R → ℂ => L.det • v) top
  simp only [smul_add,smul_zero] at scaled
  rw [eliminate] at scaled
  change (L.det • A-G*L.adjugate*W*C)*ᵥr=0
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec]
  simpa only [sub_eq_add_neg] using scaled

private def wholeFieldIndex : Fin 217 ⊕ (Fin 6 × Fin 12) ≃ Fin 289 :=
  (Equiv.sumCongr (Equiv.refl (Fin 217)) finProdFinEquiv).trans finSumFinEquiv

private theorem whole_field_left (i : Fin 217) : wholeFieldIndex (Sum.inl i)=nativeRestIndex i := rfl

private theorem whole_field_right (i : Fin 6 × Fin 12) :
    wholeFieldIndex (Sum.inr i)=gaugeAuxiliaryIndex i := by
  apply Fin.ext
  change 217+(i.2.val+12*i.1.val)=217+12*i.1.val+i.2.val
  omega

private theorem full_row_split (M : Matrix (Fin 289) (Fin 289) ℂ) (v : Fin 289 → ℂ)
    (i : Fin 289) :
    (M*ᵥv) i=((M.submatrix (fun _ : Unit => i) nativeRestIndex)*ᵥemRestSlice v) ()+
      ((M.submatrix (fun _ : Unit => i) gaugeAuxiliaryIndex)*ᵥemAuxiliarySlice v) () := by
  change (∑ j, M i j*v j)=_
  rw [← wholeFieldIndex.sum_comp (fun j => M i j*v j),Fintype.sum_sum_type]
  simp only [whole_field_left,whole_field_right]
  rfl

private theorem corrected_rest_rows (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289 → ℂ) :
    emRestSlice (correctedFullJacobi p Q*ᵥv)=
      correctedRestRest p Q*ᵥemRestSlice v+correctedRestAuxiliary p Q*ᵥemAuxiliarySlice v := by
  funext i
  exact full_row_split (correctedFullJacobi p Q) v (nativeRestIndex i)

private theorem corrected_auxiliary_rows (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289 → ℂ) :
    emAuxiliarySlice (correctedFullJacobi p Q*ᵥv)=
      correctedAuxiliaryRest p Q*ᵥemRestSlice v+correctedAuxiliaryPencil p Q*ᵥemAuxiliarySlice v := by
  funext i
  exact full_row_split (correctedFullJacobi p Q) v (gaugeAuxiliaryIndex i)

private theorem source_auxiliary_feedback (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289 → ℂ) (balance : emOriginalJacobi p*ᵥv=Q*ᵥv) :
    auxiliaryFeedbackLoop p Q*ᵥemAuxiliarySlice v=
      -((nativeAuxiliaryInverseMatrix*correctedAuxiliaryRest p Q)*ᵥemRestSlice v) := by
  have kernel : correctedFullJacobi p Q*ᵥv=0 := by
    rw [correctedFullJacobi,Matrix.sub_mulVec,balance,sub_self]
  have observed := congrArg (fun w => nativeAuxiliaryInverseMatrix*ᵥemAuxiliarySlice w) kernel
  rw [corrected_auxiliary_rows] at observed
  simp only [Matrix.mulVec_add,Matrix.mulVec_mulVec] at observed
  rw [show emAuxiliarySlice (0 : Fin 289 → ℂ)=0 from rfl,Matrix.mulVec_zero] at observed
  exact add_eq_zero_iff_eq_neg.mp (by simpa only [auxiliaryFeedbackLoop,add_comm] using observed)

/-- This reconstruction uses all 217 remaining fields and the original corrected auxiliary equation. -/
def auxiliaryFeedbackReconstruction (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (r : Fin 217 → ℂ) : (Fin 6 × Fin 12) → ℂ :=
  (auxiliaryFeedbackLoop p Q).det⁻¹ •
    (-(((auxiliaryFeedbackLoop p Q).adjugate*nativeAuxiliaryInverseMatrix*correctedAuxiliaryRest p Q)*ᵥr))

private theorem source_auxiliary_reconstruction (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289 → ℂ) (balance : emOriginalJacobi p*ᵥv=Q*ᵥv)
    (chart : (auxiliaryFeedbackLoop p Q).det≠0) :
    emAuxiliarySlice v=auxiliaryFeedbackReconstruction p Q (emRestSlice v) := by
  have loop := source_auxiliary_feedback p Q v balance
  have pay := congrArg (fun b => (auxiliaryFeedbackLoop p Q).adjugate*ᵥb) loop
  simp only [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec,
    Matrix.mulVec_neg] at pay
  calc
    _=(auxiliaryFeedbackLoop p Q).det⁻¹ • ((auxiliaryFeedbackLoop p Q).det • emAuxiliarySlice v) := by
      simp [smul_smul,chart]
    _=auxiliaryFeedbackReconstruction p Q (emRestSlice v) := by
      rw [pay]
      simp only [auxiliaryFeedbackReconstruction,Matrix.mul_assoc]

private theorem full_slices_zero (v : Fin 289 → ℂ)
    (rest : emRestSlice v=0) (auxiliary : emAuxiliarySlice v=0) : v=0 := by
  funext i
  obtain ⟨a,rfl⟩ := wholeFieldIndex.surjective i
  cases a with
  | inl r =>
    rw [whole_field_left]
    exact congrFun rest r
  | inr b =>
    rw [whole_field_right]
    exact congrFun auxiliary b

private theorem source_rest_nonzero (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289 → ℂ) (balance : emOriginalJacobi p*ᵥv=Q*ᵥv) (nonzero : v≠0)
    (chart : (auxiliaryFeedbackLoop p Q).det≠0) : emRestSlice v≠0 := by
  intro restZero
  have forced := source_auxiliary_reconstruction p Q v balance chart
  rw [restZero] at forced
  have auxiliaryZero : emAuxiliarySlice v=0 := by
    simpa only [auxiliaryFeedbackReconstruction,Matrix.mulVec_zero,neg_zero,smul_zero] using forced
  exact nonzero (full_slices_zero v restZero auxiliaryZero)

private theorem nonzero_kernel_determinant {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (v : I → ℂ) (kernel : M*ᵥv=0) (nonzero : v≠0) : M.det=0 := by
  by_contra regular
  have pay := congrArg (fun w => M.adjugate*ᵥw) kernel
  simp only [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,
    Matrix.one_mulVec,Matrix.mulVec_zero] at pay
  exact nonzero ((smul_eq_zero.mp pay).resolve_left regular)

private theorem source_cleared_schur_kernel (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289 → ℂ) (balance : emOriginalJacobi p*ᵥv=Q*ᵥv) :
    clearedCorrectedSchur p Q*ᵥemRestSlice v=0 := by
  have kernel : correctedFullJacobi p Q*ᵥv=0 := by
    rw [correctedFullJacobi,Matrix.sub_mulVec,balance,sub_self]
  have top := congrArg emRestSlice kernel
  have bottom := congrArg emAuxiliarySlice kernel
  rw [corrected_rest_rows] at top
  rw [corrected_auxiliary_rows] at bottom
  exact cleared_schur_kernel _ _ _ _ _ _ _ top bottom

/-- The actual EM root generates a closed 217-field corrected spectral equation, including singular auxiliary charts. -/
theorem actual_em_cleared_corrected_schur (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    clearedCorrectedSchur (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)*ᵥ
      emRestSlice (actualEMZeroClockMode event eps n nu (s : ℂ))=0 := by
  exact source_cleared_schur_kernel _ _ _
    (actual_zero_clock_em_original_balance event eps s n mu nu balanced finite regular root)

/-- The same complete source mode pays the actual quantum auxiliary loop equation. -/
theorem actual_em_auxiliary_feedback (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    auxiliaryFeedbackLoop (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)*ᵥ
      emAuxiliarySlice (actualEMZeroClockMode event eps n nu (s : ℂ))=
    -((nativeAuxiliaryInverseMatrix*correctedAuxiliaryRest (frequencyRay eps s n)
      (zeroClockQuantumResponse event eps s n))*ᵥ
        emRestSlice (actualEMZeroClockMode event eps n nu (s : ℂ))) := by
  exact source_auxiliary_feedback _ _ _
    (actual_zero_clock_em_original_balance event eps s n mu nu balanced finite regular root)

/-- On the actual loop chart, the same full EM mode returns its original auxiliary field. -/
theorem actual_em_auxiliary_feedback_reconstruction (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (chart : (auxiliaryFeedbackLoop (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)).det≠0) :
    emAuxiliarySlice (actualEMZeroClockMode event eps n nu (s : ℂ))=
      auxiliaryFeedbackReconstruction (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)
        (emRestSlice (actualEMZeroClockMode event eps n nu (s : ℂ))) := by
  exact source_auxiliary_reconstruction _ _ _
    (actual_zero_clock_em_original_balance event eps s n mu nu balanced finite regular root) chart

/-- The regular auxiliary chart generates a nonzero full remaining-field mode in the corrected spectrum. -/
theorem actual_em_corrected_schur_mode (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (chart : (auxiliaryFeedbackLoop (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)).det≠0) :
    emRestSlice (actualEMZeroClockMode event eps n nu (s : ℂ))≠0 ∧
      (clearedCorrectedSchur (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)).det=0 := by
  have nonzero := source_rest_nonzero _ _ _
    (actual_zero_clock_em_original_balance event eps s n mu nu balanced finite regular root)
    (actual_zero_clock_em_full_mode event eps n mu nu (s : ℂ) balanced finite root).1 chart
  exact ⟨nonzero,nonzero_kernel_determinant _ _
    (actual_em_cleared_corrected_schur event eps s n mu nu balanced finite regular root) nonzero⟩

/-- Every original EM root is retained in the source-generated auxiliary/corrected-Schur spectral factors. -/
theorem actual_em_corrected_spectral_factor (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    (auxiliaryFeedbackLoop (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)).det*
      (clearedCorrectedSchur (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)).det=0 := by
  by_cases chart : (auxiliaryFeedbackLoop (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)).det=0
  · rw [chart,zero_mul]
  · rw [(actual_em_corrected_schur_mode event eps s n mu nu balanced finite regular root chart).2,mul_zero]

end LowEnergy.GaussComposite.ActualDressedEMAuxiliaryFeedback
