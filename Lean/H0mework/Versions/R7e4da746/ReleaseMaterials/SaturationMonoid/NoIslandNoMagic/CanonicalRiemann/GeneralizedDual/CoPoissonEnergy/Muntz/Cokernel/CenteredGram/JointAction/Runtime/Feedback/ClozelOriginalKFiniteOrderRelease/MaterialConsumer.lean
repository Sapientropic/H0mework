import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.BPowerCayleyMaterialConsumer

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_release_on_original_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_firstborn_release_consumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.MaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource SourceOperationScalarInventoryLift
open OriginalKCrossParameterRAdjointSource
open scoped InnerProductSpace
namespace First
export OriginalKCombFirstFullSource
 (born split actual_born_pair actual_complete actual_whole actual_next all_inventories original_source_trace)
end First
namespace Dynamics
export OriginalKCombFirstFullSourceDynamics
 (original_xi_value initial_next_active source_branches joint_source_trace)
end Dynamics
local instance releaseMaterialGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance releaseMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "δ" => (CayleyEnergySource.sourceDamping c:ℂ)
local notation "V" => PhysicalOutsideSource.physicalOutsideColumn c
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "proj" => burnolEvenAmbientProjectionEndomorphism
local notation "actor0" => OriginalKFiniteOrderRelease.actor observation half.down 0 m
local notation "actorFirst" => OriginalKFiniteOrderRelease.actor observation half.down 0 (m+1)
variable (depth : Nat)
local notation "value" => OriginalKCombPhysicalAction.value observation nontrivial depth half
local notation "pair" => (First.born observation nontrivial half depth).activeEnvironment () ()

/-- Definitionally identical original R iterates retain their original finite actor, not a reference state. -/
theorem value_actual_actor : value=actor0 := by
 rw [Dynamics.original_xi_value]
 unfold OriginalKFiniteOrderRelease.actor CombSource.Division.rawIterate
 exact congrArg (fun operation:BurnolL2 →ₗ[ℂ] BurnolL2 => operation (burnolPaCombApproximation 0:BurnolL2))
  (ContinuousLinearMap.toLinearMap_pow (CombSource.Division.rawAction observation half.down) m).symm

/-- The existing first born reads the generated full outside vector at order m+1. -/
theorem actual_firstborn_release :
 pair.2=(-2*OriginalKFiniteOrderRelease.releaseRead observation 0) • V ∧ pair.2≠0 := by
 have source : pair.2=O actorFirst := by
  rw [First.actual_born_pair]
  change O (OriginalKCombPhysicalAction.R observation nontrivial half value)=O actorFirst
  rw [value_actual_actor,OriginalKCombCofinalRAction.original_R_direct,
   ←OriginalKFiniteOrderRelease.actor_succ observation half.down 0 m]
 exact ⟨source.trans (OriginalKFiniteOrderRelease.actor_first_outside_source observation nontrivial half.down 0),
  fun zero => OriginalKFiniteOrderRelease.actor_first_outside_ne_zero observation nontrivial half.down 0 (source.symm.trans zero)⟩

/-- Exact full-U conservation pays the complete actual outside cost before giving a strict physical loss. -/
theorem actual_firstborn_energy :
 (‖value‖^2-‖value+δ • pair.1‖^2=‖δ • pair.2‖^2) ∧
 (‖value+δ • pair.1‖^2<‖value‖^2) := by
 have native : value∈evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  rw [value_actual_actor]
  exact OriginalKFiniteOrderRelease.actor_physical observation nontrivial half.down 0 m (le_refl _)
 let physical : BurnolPaAmbientCarrier := ⟨value,native⟩
 have fixed : proj value=value := congrArg (fun x:BurnolPaAmbientCarrier=>(x:BurnolL2))
  (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self physical)
 have outsideZero : O value=0 := Submodule.starProjection_orthogonal_apply_eq_zero native
 have physicalRead : proj (burnolDirectRightResolvent ((c).value/2) value)=pair.1 := by
  rw [First.actual_born_pair]
  rfl
 have outsideRead : O (burnolDirectRightResolvent ((c).value/2) value)=pair.2 := by
  rw [First.actual_born_pair]
  rfl
 have projected : proj (CayleyEnergySource.sourceCayley c value)=value+δ • pair.1 := by
  rw [CayleyEnergySource.sourceCayley_apply,map_add,map_smul,fixed,physicalRead]
 have outsideAction : O (CayleyEnergySource.sourceCayley c value)=δ • pair.2 := by
  rw [CayleyEnergySource.sourceCayley_apply,map_add,map_smul,outsideZero,zero_add,outsideRead]
 have balance:=Submodule.norm_sq_eq_add_norm_sq_starProjection (CayleyEnergySource.sourceCayley c value)
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
 change ‖CayleyEnergySource.sourceCayley c value‖^2=
  ‖proj (CayleyEnergySource.sourceCayley c value)‖^2+‖O (CayleyEnergySource.sourceCayley c value)‖^2 at balance
 rw [CayleyEnergySource.sourceCayley_norm,projected,outsideAction] at balance
 have dampingNe : δ≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (CayleyEnergySource.sourceDamping_pos c))
 have nonzero : δ • pair.2≠0 := smul_ne_zero dampingNe (actual_firstborn_release observation nontrivial half depth).2
 have costPositive : 0<‖δ • pair.2‖^2 := pow_pos (norm_pos_iff.mpr nonzero) 2
 constructor <;> linarith

variable (ordinal : Nat)
/-- The nonzero literal first born is consumed in its full energy effect and the existing next source branches. -/
theorem actual_release_on_original_whole_next :
 type_of% (BPowerCayleyMaterialConsumer.actual_power_return_on_original_whole_next observation nontrivial half depth ordinal) ∧
 (value=actor0) ∧
 (pair.2=(-2*OriginalKFiniteOrderRelease.releaseRead observation 0) • V) ∧
 (pair.2≠0) ∧
 (‖value‖^2-‖value+δ • pair.1‖^2=‖δ • pair.2‖^2) ∧
 (‖value+δ • pair.1‖^2<‖value‖^2) ∧
 type_of% (First.actual_born_pair observation nontrivial half depth) ∧
 type_of% (First.actual_complete observation nontrivial half depth) ∧
 type_of% (First.original_source_trace observation nontrivial half depth) ∧
 type_of% (Dynamics.initial_next_active observation nontrivial half depth) ∧
 type_of% (Dynamics.source_branches observation nontrivial half depth) ∧
 type_of% (Dynamics.joint_source_trace observation nontrivial half depth) ∧
 type_of% (First.actual_whole observation nontrivial half depth) ∧
 type_of% (First.actual_next observation nontrivial half depth) ∧
 type_of% (First.all_inventories observation nontrivial half depth) := by
 have released:=actual_firstborn_release observation nontrivial half depth
 have energy:=actual_firstborn_energy observation nontrivial half depth
 exact ⟨BPowerCayleyMaterialConsumer.actual_power_return_on_original_whole_next observation nontrivial half depth ordinal,
  value_actual_actor observation nontrivial half depth,released.1,released.2,energy.1,energy.2,
  First.actual_born_pair observation nontrivial half depth,First.actual_complete observation nontrivial half depth,
  First.original_source_trace observation nontrivial half depth,Dynamics.initial_next_active observation nontrivial half depth,
  Dynamics.source_branches observation nontrivial half depth,Dynamics.joint_source_trace observation nontrivial half depth,
  First.actual_whole observation nontrivial half depth,First.actual_next observation nontrivial half depth,
  First.all_inventories observation nontrivial half depth⟩

/-- A separate reader consumes the exact firstborn loss and actual four-branch next, with all inherited inventory. -/
theorem actual_firstborn_release_consumer :
 type_of% (BPowerCayleyMaterialConsumer.actual_power_return_born_consumer observation nontrivial half depth ordinal) ∧
 (pair.2≠0) ∧
 (‖value‖^2-‖value+δ • pair.1‖^2=‖δ • pair.2‖^2) ∧
 (‖value+δ • pair.1‖^2<‖value‖^2) ∧
 type_of% (Dynamics.initial_next_active observation nontrivial half depth) ∧
 type_of% (Dynamics.source_branches observation nontrivial half depth) ∧
 type_of% (First.actual_whole observation nontrivial half depth) ∧
 type_of% (First.actual_next observation nontrivial half depth) ∧
 type_of% (First.all_inventories observation nontrivial half depth) := by
 have actual:=actual_release_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨BPowerCayleyMaterialConsumer.actual_power_return_born_consumer observation nontrivial half depth ordinal,
  actual.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

include nontrivial in
/-- The actual low-order actors do not release: their Fourier read and their next outside are both zero. -/
theorem lower_order_no_release (k:Nat) (before:k<m) :
 CombSource.Division.fourierRead observation half.down (OriginalKFiniteOrderRelease.actor observation half.down 0 k)=0 ∧
 O (OriginalKFiniteOrderRelease.actor observation half.down 0 (k+1))=0 := by
 constructor
 · exact CombSource.Division.actual_comb_fourier_zero observation nontrivial half.down 0 k before
 · exact Submodule.starProjection_orthogonal_apply_eq_zero
    (OriginalKFiniteOrderRelease.actor_physical observation nontrivial half.down 0 (k+1) (by omega))

theorem zero_actor_has_no_release (k:Nat) :
 O (CombSource.Division.rawIterate observation half.down k 0)=0 := by rw [map_zero,map_zero]

theorem zero_scaled_actor_has_no_release (k:Nat) (input:BurnolL2) :
 O (CombSource.Division.rawIterate observation half.down k ((0:ℂ) • input))=0 := by
 rw [zero_smul]
 exact zero_actor_has_no_release observation half k

theorem actual_complete_outside_cannot_be_dropped :
 OriginalKCombPhysicalAction.R observation nontrivial half value≠pair.1 := by
 intro erased
 have full:=First.actual_complete observation nontrivial half depth
 rw [erased] at full
 exact (actual_firstborn_release observation nontrivial half depth).2 (add_left_cancel (full.trans (add_zero pair.1).symm))

/-- The full actual delta-outside cost rules out a zero-cost interpretation of this physical compression. -/
theorem actual_outside_energy_cannot_be_dropped :
 ‖value‖^2-‖value+δ • pair.1‖^2≠0 := by
 have strict:=(actual_firstborn_energy observation nontrivial half depth).2
 linarith

end OriginalKFiniteOrderRelease.MaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
