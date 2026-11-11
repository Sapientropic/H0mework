import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusJetFeedbackConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCompressedRSourceKernel.Kernel

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusPaCayleySource
open Complex MeasureTheory BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace
abbrev PaSource := OriginalKPaCompressedRSourceKernel.PaSourceCarrier
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKCombCofinalPaAction.Q
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "delta" => (sourceDamping c : ℂ)

def wholeUnit : BurnolPaAmbientCarrier:=burnolZeroOwnedUnitTailState observation nontrivial half.down

def unitQ : BurnolPaAmbientCarrier:=burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (wholeUnit observation nontrivial half)

def rawUpdate (input : PaSource) : BurnolL2:=sourceCayley c (input.val : BurnolL2)

/-- The next Pa is a dependent read of the executed original U action. -/
def sourceNext (input : PaSource) : PaSource:=
  ⟨E (rawUpdate observation nontrivial half input),Submodule.starProjection_apply_mem _ _⟩

/-- The complete original unit-Q residue is generated at the same input coefficient. -/
def sourceQ (input : PaSource) : BurnolPaAmbientCarrier:=
  (delta*burnolPaResolventSourceCoefficient c input.val) • unitQ observation nontrivial half

private theorem raw_physical (input : PaSource) :
    rawUpdate observation nontrivial half input∈evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  let response:=burnolPaResolventPhysicalResponse observation nontrivial half.down input.val input.property
  have typed : (response : BurnolL2)=burnolDirectRightResolvent ((c).value/2) (input.val : BurnolL2):=rfl
  rw [rawUpdate,sourceCayley_apply,←typed]
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.add_mem input.val.property
    ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.smul_mem _ response.property)

def physicalUpdate (input : PaSource) : BurnolPaAmbientCarrier:=
  ⟨rawUpdate observation nontrivial half input,raw_physical observation nontrivial half input⟩

theorem actual_source_Q (input : PaSource) :
    Q (rawUpdate observation nontrivial half input)=sourceQ observation nontrivial half input := by
  have physical : burnolEvenAmbientProjection (rawUpdate observation nontrivial half input)=
      physicalUpdate observation nontrivial half input:=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (physicalUpdate observation nontrivial half input)
  have native:=burnolPaResolventPhysicalResponse_Q observation nontrivial half.down input.val input.property
  let response:=burnolPaResolventPhysicalResponse observation nontrivial half.down input.val input.property
  change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection response=
    burnolPaResolventSourceCoefficient c input.val • unitQ observation nontrivial half at native
  have whole : physicalUpdate observation nontrivial half input=input.val+delta • response:=by
    apply Subtype.ext
    rfl
  change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
    (burnolEvenAmbientProjection (rawUpdate observation nontrivial half input))=_
  rw [physical,whole,map_add,map_smul,Submodule.starProjection_orthogonal_apply_eq_zero input.property,
    zero_add,native,smul_smul]
  rfl

/-- Both components come from the same full physical event, retaining the complete unit-Q vector. -/
theorem actual_whole_update (input : PaSource) : rawUpdate observation nontrivial half input=
    ((sourceNext observation nontrivial half input : BurnolPaAmbientCarrier) : BurnolL2)+
      (sourceQ observation nontrivial half input : BurnolL2) := by
  have split:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection (rawUpdate observation nontrivial half input))
  change (sourceNext observation nontrivial half input : BurnolPaAmbientCarrier)+
    Q (rawUpdate observation nontrivial half input)=_ at split
  rw [actual_source_Q] at split
  have physical : burnolEvenAmbientProjection (rawUpdate observation nontrivial half input)=
      physicalUpdate observation nontrivial half input:=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (physicalUpdate observation nontrivial half input)
  rw [physical] at split
  exact (congrArg (fun value : BurnolPaAmbientCarrier=>(value : BurnolL2)) split).symm

theorem actual_outside_zero (input : PaSource) : O (rawUpdate observation nontrivial half input)=0 := by
  have whole : O (rawUpdate observation nontrivial half input)=rawUpdate observation nontrivial half input-
      (burnolEvenAmbientProjection (rawUpdate observation nontrivial half input) : BurnolL2):=
    Submodule.starProjection_orthogonal_val _
  have physical : burnolEvenAmbientProjection (rawUpdate observation nontrivial half input)=
      physicalUpdate observation nontrivial half input:=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (physicalUpdate observation nontrivial half input)
  rw [whole,physical]
  exact sub_self _

theorem unitQ_ne_zero : unitQ observation nontrivial half≠0 := by
  intro zero
  apply burnolZeroOwnedUnitTailState_notInPa observation nontrivial half.down
  have split:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (wholeUnit observation nontrivial half)
  change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (wholeUnit observation nontrivial half)+
    unitQ observation nontrivial half=wholeUnit observation nontrivial half at split
  rw [zero,add_zero] at split
  change wholeUnit observation nontrivial half∈burnolCompactCoPoissonClosedRange
  rw [←split]
  exact Submodule.starProjection_apply_mem _ _

def unitPrice : ℝ:=(sourceDamping c)^2*‖unitQ observation nontrivial half‖^2

theorem unitPrice_positive : 0<unitPrice observation nontrivial half:=
  mul_pos (sq_pos_of_pos (sourceDamping_pos c))
    (sq_pos_of_pos (norm_pos_iff.mpr (unitQ_ne_zero observation nontrivial half)))

/-- Original whole-U conservation is consumed only after the full Pa/Q split has executed. -/
theorem actual_Pa_loss (input : PaSource) :
    ‖(input : BurnolPaAmbientCarrier)‖^2-‖(sourceNext observation nontrivial half input : BurnolPaAmbientCarrier)‖^2=
      unitPrice observation nontrivial half*‖burnolPaResolventSourceCoefficient c input.val‖^2 := by
  have balance:=Submodule.norm_sq_eq_add_norm_sq_starProjection
    (burnolEvenAmbientProjection (rawUpdate observation nontrivial half input))
    burnolCompactCoPoissonClosedRange.toSubmodule
  change ‖burnolEvenAmbientProjection (rawUpdate observation nontrivial half input)‖^2=
    ‖(sourceNext observation nontrivial half input : BurnolPaAmbientCarrier)‖^2+
      ‖Q (rawUpdate observation nontrivial half input)‖^2 at balance
  have physical : burnolEvenAmbientProjection (rawUpdate observation nontrivial half input)=
      physicalUpdate observation nontrivial half input:=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (physicalUpdate observation nontrivial half input)
  rw [physical,actual_source_Q] at balance
  have conservation : ‖physicalUpdate observation nontrivial half input‖=‖(input : BurnolPaAmbientCarrier)‖:=
    sourceCayley_norm c (input.val : BurnolL2)
  rw [conservation] at balance
  have fee : ‖sourceQ observation nontrivial half input‖^2=
      unitPrice observation nontrivial half*‖burnolPaResolventSourceCoefficient c input.val‖^2 := by
    unfold sourceQ unitPrice
    rw [norm_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sourceDamping_pos c)]
    ring
  rw [fee] at balance
  linarith

theorem actual_Pa_loss_zero_iff (input : PaSource) :
    ‖(input : BurnolPaAmbientCarrier)‖^2-‖(sourceNext observation nontrivial half input : BurnolPaAmbientCarrier)‖^2=0 ↔
      burnolPaResolventSourceCoefficient c input.val=0 := by
  rw [actual_Pa_loss]
  simp only [mul_eq_zero,(unitPrice_positive observation nontrivial half).ne',false_or,
    sq_eq_zero_iff,norm_eq_zero]

end OriginalWholeDebtRJointMobiusPaCayleySource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
