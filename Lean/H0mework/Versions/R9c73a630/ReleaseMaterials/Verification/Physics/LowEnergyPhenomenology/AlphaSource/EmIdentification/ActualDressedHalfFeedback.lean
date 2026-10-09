import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedSchur
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedDampedFourier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedHalfGreenSchur
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open ActualDressedFullCoulomb ActualDressedFrequencyHalf
open ActualEMDressedConstraint ActualEMDressedSchur ActualEMAction
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceGreen frequencyQuantumCorrection frequencyResponsePencil
  originalJacobi sourceNull sourceNullLift sourceCokernel

def halfFeedback (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  1-sourceGreen p*frequencyQuantumCorrection event transfer p.val lambda

/-- The regularity test is the actual finite source determinant, not an inverse certificate. -/
def halfFeedbackDet (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) : ℂ := (halfFeedback event transfer p lambda).det

def halfFeedbackPrice (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) : ℝ :=
  ∑i : Fin 289,∑j : Fin 289,‖(sourceGreen p*frequencyQuantumCorrection event transfer p.val lambda) i j‖

def halfRegularRegion (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) : Set ℂ := {lambda|halfFeedbackDet event transfer p lambda≠0}

def halfFeedbackResolvent (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  (halfFeedback event transfer p lambda)⁻¹

attribute [local irreducible] halfFeedback halfFeedbackDet halfFeedbackPrice halfFeedbackResolvent

private theorem matrix_entry_price (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (a : Fin n→ℂ) :
    ‖B*ᵥa‖≤(∑i,∑j,‖B i j‖)*‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  calc
    _ ≤ ∑j,‖B i j*a j‖ := norm_sum_le _ _
    _ ≤ ∑j,‖B i j‖*‖a‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm a j) (norm_nonneg _)
    _=(∑j,‖B i j‖)*‖a‖ := by rw [Finset.sum_mul]
    _ ≤ (∑k,∑j,‖B k j‖)*‖a‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg a)
      exact Finset.single_le_sum (f:=fun k : Fin n=>∑j,‖B k j‖)
        (fun k _=>Finset.sum_nonneg (fun j _=>norm_nonneg (B k j))) (Finset.mem_univ i)

private theorem matrix_feedback_unit (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (small : (∑i,∑j,‖B i j‖)<1) : IsUnit (1-B) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro a b same
  have equation : (1-B)*ᵥ(a-b)=0 := by rw [Matrix.mulVec_sub,same,sub_self]
  have fixed : a-b=B*ᵥ(a-b) := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec] at equation
    exact sub_eq_zero.mp equation
  have price:=matrix_entry_price n B (a-b)
  rw [←fixed] at price
  have zero : ‖a-b‖=0 := by nlinarith [norm_nonneg (a-b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp zero)

theorem half_feedback_regular_of_source_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (small : halfFeedbackPrice event transfer p lambda<1) :
    halfFeedbackDet event transfer p lambda≠0 := by
  have unit : IsUnit (halfFeedback event transfer p lambda) := by
    unfold halfFeedback
    unfold halfFeedbackPrice at small
    exact matrix_feedback_unit _ _ small
  unfold halfFeedbackDet
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp unit)

theorem half_feedback_inverse_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (regular : halfFeedbackDet event transfer p lambda≠0) :
    halfFeedback event transfer p lambda*halfFeedbackResolvent event transfer p lambda=1 ∧
      halfFeedbackResolvent event transfer p lambda*halfFeedback event transfer p lambda=1 := by
  unfold halfFeedbackDet at regular
  unfold halfFeedbackResolvent
  have unit : IsUnit (halfFeedback event transfer p lambda).det := isUnit_iff_ne_zero.mpr regular
  exact ⟨Matrix.mul_nonsing_inv _ unit,Matrix.nonsing_inv_mul _ unit⟩

theorem half_feedback_response (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (regular : halfFeedbackDet event transfer p lambda≠0)
    (forcing : Fin 289→ℂ) :
    halfFeedbackResolvent event transfer p lambda*ᵥforcing=
      forcing+sourceGreen p*ᵥ(frequencyQuantumCorrection event transfer p.val lambda*ᵥ
        (halfFeedbackResolvent event transfer p lambda*ᵥforcing)) := by
  have equation:=congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>A*ᵥforcing)
    (half_feedback_inverse_generated event transfer p lambda regular).1
  rw [←Matrix.mulVec_mulVec,Matrix.one_mulVec,halfFeedback,Matrix.sub_mulVec,
    Matrix.one_mulVec,←Matrix.mulVec_mulVec] at equation
  exact sub_eq_iff_eq_add.mp equation

end LowEnergy.GaussComposite.ActualDressedHalfGreenSchur
