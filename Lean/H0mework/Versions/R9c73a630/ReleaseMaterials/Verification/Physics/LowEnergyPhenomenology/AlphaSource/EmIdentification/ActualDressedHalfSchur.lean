import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedHalfFeedback

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
  originalJacobi sourceNull sourceNullLift sourceCokernel halfFeedback halfFeedbackResolvent

def halfResponseNine (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (forcing : Fin 289→ℂ) (initial : Fin 9→ℂ) : Fin 289→ℂ :=
  halfFeedbackResolvent event transfer p lambda*ᵥ(sourceGreen p*ᵥforcing+sourceNullLift p.val initial)

def halfSchur (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) : Matrix (Fin 9) (Fin 9) ℂ :=
  LinearMap.toMatrix' ((sourceCokernel p.val).comp
    ((Matrix.toLin' (frequencyQuantumCorrection event transfer p.val lambda)).comp
      ((Matrix.toLin' (halfFeedbackResolvent event transfer p lambda)).comp (sourceNullLift p.val))))

def halfSchurSource (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (forcing : Fin 289→ℂ) : Fin 9→ℂ :=
  -sourceCokernel p.val (forcing+frequencyQuantumCorrection event transfer p.val lambda*ᵥ
    (halfFeedbackResolvent event transfer p lambda*ᵥ(sourceGreen p*ᵥforcing)))

attribute [local irreducible] halfResponseNine halfSchur halfSchurSource

theorem half_response_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (regular : halfFeedbackDet event transfer p lambda≠0)
    (forcing : Fin 289→ℂ) (initial : Fin 9→ℂ) :
    halfResponseNine event transfer p lambda forcing initial=
      sourceNullLift p.val initial+sourceGreen p*ᵥ(forcing+
        frequencyQuantumCorrection event transfer p.val lambda*ᵥ
          halfResponseNine event transfer p lambda forcing initial) := by
  have generated:=half_feedback_response event transfer p lambda regular
    (sourceGreen p*ᵥforcing+sourceNullLift p.val initial)
  rw [←halfResponseNine] at generated
  exact generated.trans (by rw [Matrix.mulVec_add];abel)

theorem half_response_null_data (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (regular : halfFeedbackDet event transfer p lambda≠0)
    (forcing : Fin 289→ℂ) (initial : Fin 9→ℂ) :
    sourceNull p.val*ᵥhalfResponseNine event transfer p lambda forcing initial=sourceNullLift p.val initial := by
  conv_lhs => arg 2;rw [half_response_generated event transfer p lambda regular]
  rw [Matrix.mulVec_add,source_null_lift_fixed,Matrix.mulVec_mulVec,source_null_green,
    Matrix.zero_mulVec,add_zero]

theorem half_response_euler (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (regular : halfFeedbackDet event transfer p lambda≠0)
    (forcing : Fin 289→ℂ) (initial : Fin 9→ℂ) :
    frequencyResponsePencil event transfer p.val lambda*ᵥ
      halfResponseNine event transfer p lambda forcing initial=
      forcing-originalRowLift p.val*ᵥsourceCompatibility p.val
        (forcing+frequencyQuantumCorrection event transfer p.val lambda*ᵥ
          halfResponseNine event transfer p lambda forcing initial) := by
  have null : originalJacobi p.val*ᵥsourceNullLift p.val initial=0 := by
    rw [←source_null_lift_fixed p.val initial,Matrix.mulVec_mulVec,source_null_euler,Matrix.zero_mulVec]
  rw [frequencyResponsePencil,em_jacobi_source,Matrix.sub_mulVec]
  conv_lhs => arg 1;arg 2;rw [half_response_generated event transfer p lambda regular]
  rw [Matrix.mulVec_add,null,zero_add]
  have original:=original_forced_field p
    (forcing+frequencyQuantumCorrection event transfer p.val lambda*ᵥ
      halfResponseNine event transfer p lambda forcing initial)
  rw [PreparationVacuumOriginalGreenFeedback.sourceField] at original
  rw [original]
  abel

private theorem half_response_restores (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (regular : halfFeedbackDet event transfer p lambda≠0)
    (a : Fin 289→ℂ) :
    halfResponseNine event transfer p lambda (frequencyResponsePencil event transfer p.val lambda*ᵥa)
      (sourceNullCoordinates p.val a)=a := by
  have original : sourceGreen p*originalJacobi p.val=1-sourceNull p.val := by
    simpa only [sourceNull] using sourceGreen_original_left p
  have equation : sourceGreen p*ᵥ(frequencyResponsePencil event transfer p.val lambda*ᵥa)+
      sourceNullLift p.val (sourceNullCoordinates p.val a)=halfFeedback event transfer p lambda*ᵥa := by
    rw [frequencyResponsePencil,em_jacobi_source,Matrix.sub_mulVec,Matrix.mulVec_sub,
      Matrix.mulVec_mulVec,original,Matrix.sub_mulVec,Matrix.one_mulVec,
      source_null_coordinates_generated,halfFeedback,Matrix.sub_mulVec,Matrix.one_mulVec,
      ←Matrix.mulVec_mulVec]
    abel
  rw [halfResponseNine,equation,Matrix.mulVec_mulVec,
    (half_feedback_inverse_generated event transfer p lambda regular).2,Matrix.one_mulVec]

theorem half_schur_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (forcing : Fin 289→ℂ) (initial : Fin 9→ℂ) :
    sourceCokernel p.val (forcing+frequencyQuantumCorrection event transfer p.val lambda*ᵥ
      halfResponseNine event transfer p lambda forcing initial)=
      halfSchur event transfer p lambda*ᵥinitial-halfSchurSource event transfer p lambda forcing := by
  rw [halfSchur,LinearMap.toMatrix'_mulVec]
  simp only [LinearMap.comp_apply,Matrix.toLin'_apply]
  unfold halfResponseNine halfSchurSource
  rw [Matrix.mulVec_add,Matrix.mulVec_add,←add_assoc,map_add]
  abel

/-- Every complete actual halfline solution returns through the same feedback and original nine rows. -/
theorem half_full_solution_schur (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (regular : halfFeedbackDet event transfer p lambda≠0)
    (forcing a : Fin 289→ℂ) :
    frequencyResponsePencil event transfer p.val lambda*ᵥa=forcing ↔
      ∃initial : Fin 9→ℂ,a=halfResponseNine event transfer p lambda forcing initial ∧
        halfSchur event transfer p lambda*ᵥinitial=halfSchurSource event transfer p lambda forcing := by
  constructor
  · intro equation
    have compatible : sourceCompatibility p.val
        (forcing+frequencyQuantumCorrection event transfer p.val lambda*ᵥa)=0 := by
      have sumEq : forcing+frequencyQuantumCorrection event transfer p.val lambda*ᵥa=
          originalJacobi p.val*ᵥa := by
        rw [←equation,frequencyResponsePencil,em_jacobi_source,Matrix.sub_mulVec]
        abel
      rw [sumEq]
      exact source_compatibility_euler p.val a
    have restored:=half_response_restores event transfer p lambda regular a
    rw [equation] at restored
    refine ⟨sourceNullCoordinates p.val a,restored.symm,?_⟩
    have nine:=(source_compatibility_nine p.val _).mp compatible
    rw [←restored,half_schur_generated] at nine
    exact sub_eq_zero.mp nine
  · rintro ⟨initial,rfl,schur⟩
    have compatible : sourceCompatibility p.val
        (forcing+frequencyQuantumCorrection event transfer p.val lambda*ᵥ
          halfResponseNine event transfer p lambda forcing initial)=0 := by
      apply (source_compatibility_nine p.val _).mpr
      rw [half_schur_generated,schur,sub_self]
    rw [half_response_euler event transfer p lambda regular,compatible,Matrix.mulVec_zero,sub_zero]

end LowEnergy.GaussComposite.ActualDressedHalfGreenSchur
