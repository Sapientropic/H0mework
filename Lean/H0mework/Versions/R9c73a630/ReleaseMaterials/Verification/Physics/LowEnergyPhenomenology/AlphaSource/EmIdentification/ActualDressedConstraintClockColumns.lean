import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintHistory
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedClockSchur

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSchurClock
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumCurrentSignalOperator
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil ActualDressedClockMoment
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open ActualDressedNullNative ActualEMDressedClockGerm ActualEMDressedClockSchur
open scoped Matrix BigOperators Topology
attribute [local irreducible] originalChange originalReadback sourceNullLift sourceCokernel

private abbrev matrixNorm (m n : ℕ) : NormedAddCommGroup (Matrix (Fin m) (Fin n) ℂ) := by
  unfold Matrix
  infer_instance

attribute [local instance] matrixNorm

private abbrev matrixSpace (m n : ℕ) : NormedSpace ℂ (Matrix (Fin m) (Fin n) ℂ) := by
  unfold Matrix
  infer_instance

attribute [local instance] matrixSpace

private theorem term_clock_affine (a : SourceTerm) (degree : a.powers.temporal≤1)
    (z : ℂ) (i j : Fin 289) :
    a.matrix (sourceInputClock z) i j=a.matrix (sourceInputClock 0) i j+
      z*(a.matrix (sourceInputClock 1) i j-a.matrix (sourceInputClock 0) i j) := by
  simp only [SourceTerm.matrix,Matrix.single_apply]
  split_ifs
  · have cases : a.powers.temporal=0 ∨ a.powers.temporal=1 := by omega
    rcases cases with zero | one
    · simp [Powers.value,sourceInputClock,zero]
    · simp only [Powers.value,sourceInputClock,Pi.single_eq_same,Pi.single_eq_of_ne (by decide : (1:Fin 4)≠0),
        Pi.single_eq_of_ne (by decide : (2:Fin 4)≠0),Pi.single_eq_of_ne (by decide : (3:Fin 4)≠0),one,pow_one]
      ring
  · simp

private theorem matrix_clock_affine (terms : List SourceTerm)
    (degree : ∀a∈terms,a.powers.temporal≤1) (z : ℂ) (i j : Fin 289) :
    sourceMatrix terms (sourceInputClock z) i j=sourceMatrix terms (sourceInputClock 0) i j+
      z*(sourceMatrix terms (sourceInputClock 1) i j-sourceMatrix terms (sourceInputClock 0) i j) := by
  induction terms with
  | nil=>simp only [sourceMatrix_nil,Matrix.zero_apply,sub_self,mul_zero,add_zero]
  | cons a rest ih=>
    have tail : ∀b∈rest,b.powers.temporal≤1 := fun b member=>degree b (List.mem_cons_of_mem a member)
    simp only [sourceMatrix_cons,Matrix.add_apply]
    rw [term_clock_affine a (degree a (by simp)) z i j,ih tail]
    ring

/-- The original nine columns, with their actual Fourier clock. -/
def clockNativeNull (z : ℂ) : Matrix (Fin 289) (Fin 9) ℂ :=
  fun i n=>originalNullColumn (sourceInputClock z) n i

/-- The source table is affine in this clock, so these two exact source evaluations generate its coefficient. -/
def clockNativeNullJet : Matrix (Fin 289) (Fin 9) ℂ := clockNativeNull 1-clockNativeNull 0

/-- The original left map uses the opposite Fourier covector, without conjugation. -/
def clockNativeCokernel (z : ℂ) : Matrix (Fin 9) (Fin 289) ℂ := (clockNativeNull (-z)).transpose

private theorem clock_null_affine (z : ℂ) : clockNativeNull z=clockNativeNull 0+z • clockNativeNullJet := by
  have certificate : ∀n : Fin 9,(nullColumnTerms n).all (fun a=>decide (a.powers.temporal≤1))=true := by decide +kernel
  ext i n
  simp only [clockNativeNull,clockNativeNullJet,Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,
    original_null_column_literal]
  exact matrix_clock_affine (nullColumnTerms n)
    (fun a member=>of_decide_eq_true (List.all_eq_true.mp (certificate n) a member)) z i (nullColumnIndex n)

private theorem clock_neg (z : ℂ) : -sourceInputClock z=sourceInputClock (-z) := by
  funext i
  by_cases zero : i=0
  · subst i
    simp only [sourceInputClock,Pi.neg_apply,Pi.single_eq_same]
  · simp only [sourceInputClock,Pi.neg_apply,Pi.single_eq_of_ne zero,neg_zero]

/-- Both rectangular matrices consume the previously generated original nine-coordinate maps. -/
theorem clock_native_columns_actual (z : ℂ) (initial : Fin 9→ℂ) (a : SignalAmplitude) :
    clockNativeNull z*ᵥinitial=sourceNullLift (sourceInputClock z) initial ∧
      clockNativeCokernel z*ᵥa=sourceCokernel (sourceInputClock z) a := by
  constructor
  · have expansion : initial=∑n : Fin 9,initial n • Pi.single n (1:ℂ) := by
      ext n
      simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul,
        mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    conv_rhs => arg 2; rw [expansion]
    simp only [map_sum,map_smul,original_null_lift_single]
    ext i
    simp only [Matrix.mulVec,dotProduct,clockNativeNull,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
  · ext n
    rw [original_null_cokernel,clock_neg]
    rfl

/-- The source's exact frequency-varying left and right columns generate both true derivatives. -/
theorem clock_native_columns_derivative (z : ℂ) :
    HasDerivAt clockNativeNull clockNativeNullJet z ∧
      HasDerivAt clockNativeCokernel (-clockNativeNullJet.transpose) z := by
  have first (w : ℂ) : HasDerivAt clockNativeNull clockNativeNullJet w := by
    have original : HasDerivAt (fun v : ℂ=>clockNativeNull 0+v • clockNativeNullJet) clockNativeNullJet w := by
      simpa only [one_smul,zero_add] using!
        (hasDerivAt_const w (clockNativeNull 0)).add ((hasDerivAt_id w).smul_const clockNativeNullJet)
    exact original.congr_of_eventuallyEq (Filter.Eventually.of_forall clock_null_affine)
  refine ⟨first z,?_⟩
  apply hasDerivAt_pi.mpr
  intro n
  apply hasDerivAt_pi.mpr
  intro i
  have entry : HasDerivAt (fun w=>clockNativeNull w i n) (clockNativeNullJet i n) (-z) :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp (first (-z)) i) n
  have generated:=entry.comp z (hasDerivAt_id z).neg
  simpa only [clockNativeCokernel,Matrix.transpose_apply,Matrix.neg_apply,mul_neg,mul_one,Function.comp_def] using! generated

end LowEnergy.GaussComposite.ActualDressedSchurClock
