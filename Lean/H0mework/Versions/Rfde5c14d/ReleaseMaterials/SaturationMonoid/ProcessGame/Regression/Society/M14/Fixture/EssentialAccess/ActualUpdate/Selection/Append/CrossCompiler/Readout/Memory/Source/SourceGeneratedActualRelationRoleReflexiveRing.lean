import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Cohomology.ProofCarryingActualRelationThreeCycleResidual
import H0mework.Realization.CyclicMemory.P119

/-!
# Role-native reflexive ring of the actual relation cycle

The already generated three-cycle supplies each query's source role, target
role and incoming edge.  A query writes its actual target role.  The
downstream read recognizes only the target role of its actual incoming edge,
so its complete generated interaction phase is the existing cycle cochain,
not merely an equality on the three selected edges.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedActualRelationRoleReflexiveRing

noncomputable section

open Lifecycle Universal Relations
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedActualRelationThreeCycle
open M14ProofCarryingActualRelationThreeCycleResidual

/-- Source role of one generated cycle edge. -/
def actualRelationCycleSourceRoleAt
    (base : Nat) (index : ThreeCycleTime) : EssentialAccessRole :=
  actualRelationSourceRoleAt (actualRelationCycleDepthAt base index)

/-- Target role of one generated cycle edge. -/
def actualRelationCycleTargetRoleAt
    (base : Nat) (index : ThreeCycleTime) : EssentialAccessRole :=
  actualRelationTargetRoleAt (actualRelationCycleDepthAt base index)

@[simp] theorem actualRelationCycleSourceRoleAt_eq_provider
    (base : Nat) (index : ThreeCycleTime) :
    actualRelationCycleSourceRoleAt base index = .provider := by
  unfold actualRelationCycleSourceRoleAt actualRelationSourceRoleAt
  rfl

@[simp] theorem criticalTargetRole_tenure :
    essentialAccessRelationCompiler.roleAt
        (essentialAccessCriticalRelation .tenure) .target =
      .tenureProvider :=
  rfl

@[simp] theorem criticalTargetRole_health :
    essentialAccessRelationCompiler.roleAt
        (essentialAccessCriticalRelation .health) .target =
      .healthProvider :=
  rfl

@[simp] theorem criticalTargetRole_platform :
    essentialAccessRelationCompiler.roleAt
        (essentialAccessCriticalRelation .platform) .target =
      .platformProvider :=
  rfl

/-- The generated target-role map on the three native relation events is
injective.  This is a case theorem about the existing role compiler, not a
role table accepted by the ring. -/
theorem essentialAccessCriticalTargetRole_injective :
    Function.Injective (fun event : EssentialAccessEvent =>
      essentialAccessRelationCompiler.roleAt
        (essentialAccessCriticalRelation event) .target) := by
  intro left right equality
  cases left <;> cases right <;>
    simp_all only [criticalTargetRole_tenure, criticalTargetRole_health,
      criticalTargetRole_platform]
  all_goals first | rfl | cases equality

theorem essentialAccessCriticalTargetRole_ne_provider
    (event : EssentialAccessEvent) :
    essentialAccessRelationCompiler.roleAt
        (essentialAccessCriticalRelation event) .target ≠ .provider := by
  cases event <;>
    simp only [criticalTargetRole_tenure, criticalTargetRole_health,
      criticalTargetRole_platform] <;>
    intro equality <;> cases equality

theorem actualRelationCycleTargetRoleAt_injective (base : Nat) :
    Function.Injective (actualRelationCycleTargetRoleAt base) := by
  intro left right equality
  apply actualRelationCycleActorAt_injective base
  unfold actualRelationCycleActorAt actualRelationActorAt
  have eventEquality :
      (actualRelationSeedAt
          (actualRelationCycleDepthAt base left)).1 =
        (actualRelationSeedAt
          (actualRelationCycleDepthAt base right)).1 := by
    exact essentialAccessCriticalTargetRole_injective equality
  have seedEquality :
      actualRelationSeedAt (actualRelationCycleDepthAt base left) =
        actualRelationSeedAt (actualRelationCycleDepthAt base right) := by
    apply Subtype.ext
    exact eventEquality
  rw [seedEquality]

theorem actualRelationCycleTargetRoleAt_ne_provider
    (base : Nat) (index : ThreeCycleTime) :
    actualRelationCycleTargetRoleAt base index ≠ .provider := by
  unfold actualRelationCycleTargetRoleAt actualRelationTargetRoleAt
  exact essentialAccessCriticalTargetRole_ne_provider _

theorem actualRelationCycleSourceRoleAt_ne_targetRoleAt
    (base : Nat) (source target : ThreeCycleTime) :
    actualRelationCycleSourceRoleAt base source ≠
      actualRelationCycleTargetRoleAt base target := by
  rw [actualRelationCycleSourceRoleAt_eq_provider]
  exact (actualRelationCycleTargetRoleAt_ne_provider base target).symm

/-- The incoming edge whose target role is recognized by query `index`. -/
def actualRelationIncomingIndex (index : ThreeCycleTime) : ThreeCycleTime :=
  threeCycleNext.symm index

/-- Integer readout of the actual incoming target role. -/
def actualRelationIncomingRoleReadAt
    (base : Nat) (index : ThreeCycleTime) : EssentialAccessRole → Int :=
  fun role =>
    if role = actualRelationCycleTargetRoleAt base
        (actualRelationIncomingIndex index) then 1 else 0

/-- Reflexive query generated by one actual edge role transport. -/
def actualRelationRoleQueryAt
    (base : Nat) (index : ThreeCycleTime) :
    ReflexiveQuery EssentialAccessRole Int where
  read := actualRelationIncomingRoleReadAt base index
  write := fun _ => actualRelationCycleTargetRoleAt base index

/-- The finite reflexive ring is a readout of the existing actual cycle.  It
stores no phase, residual, event schedule or alternate occurrence. -/
def actualRelationRoleReflexiveRingAt
    (base : Nat) :
    FiniteReflexiveInteractionRing ThreeCycleTime EssentialAccessRole Int where
  next := threeCycleNext
  query := actualRelationRoleQueryAt base
  base := actualRelationCycleSourceRoleAt base
  nondegenerate := by
    rw [show Fintype.card ThreeCycleTime = 3 by
      rw [Fintype.card]
      rw [show (Finset.univ : Finset ThreeCycleTime) =
          {ThreeCycleTime.t0, ThreeCycleTime.t1, ThreeCycleTime.t2} by
        ext index
        cases index <;> simp]
      simp]

theorem actualRelationIncomingRoleReadAt_source_eq_zero
    (base : Nat) (source target : ThreeCycleTime) :
    actualRelationIncomingRoleReadAt base target
        (actualRelationCycleSourceRoleAt base source) = 0 := by
  unfold actualRelationIncomingRoleReadAt
  rw [if_neg (actualRelationCycleSourceRoleAt_ne_targetRoleAt base source
    (actualRelationIncomingIndex target))]

theorem actualRelationIncomingRoleReadAt_target_eq_one_iff
    (base : Nat) (source target : ThreeCycleTime) :
    actualRelationIncomingRoleReadAt base target
        (actualRelationCycleTargetRoleAt base source) = 1 ↔
      target = threeCycleNext source := by
  rw [actualRelationIncomingRoleReadAt]
  constructor
  · intro readOne
    split at readOne
    next roleEquality =>
      have indexEquality : source = actualRelationIncomingIndex target :=
        actualRelationCycleTargetRoleAt_injective base roleEquality
      calc
        target = threeCycleNext (actualRelationIncomingIndex target) := by
          simp [actualRelationIncomingIndex]
        _ = threeCycleNext source := congrArg threeCycleNext indexEquality.symm
    next roleDifferent => simp at readOne
  · intro targetExact
    subst target
    simp [actualRelationIncomingIndex]

/-- Full mechanism-faithfulness square: every pair value of the read/write
ring equals the existing actual-cycle cochain. -/
theorem actualRelationRoleReflexiveRing_generatedInteractionPhase_eq
    (base : Nat) :
    (actualRelationRoleReflexiveRingAt base).generatedInteractionPhase =
      actualRelationCycleCochain base := by
  funext source target
  rw [FiniteReflexiveInteractionRing.generatedInteractionPhase]
  change actualRelationIncomingRoleReadAt base target
        (actualRelationCycleTargetRoleAt base source) -
      actualRelationIncomingRoleReadAt base target
        (actualRelationCycleSourceRoleAt base target) = _
  rw [actualRelationIncomingRoleReadAt_source_eq_zero]
  unfold actualRelationCycleCochain
  by_cases selected : target = threeCycleNext source
  · rw [if_pos selected]
    rw [(actualRelationIncomingRoleReadAt_target_eq_one_iff
      base source target).2 selected]
    simp [actualRelationCycleIncidenceOf]
  · rw [if_neg selected]
    have roleDifferent :
        actualRelationCycleTargetRoleAt base source ≠
          actualRelationCycleTargetRoleAt base
            (actualRelationIncomingIndex target) := by
      intro roleEquality
      have indexEquality :
          source = actualRelationIncomingIndex target :=
        actualRelationCycleTargetRoleAt_injective base roleEquality
      apply selected
      calc
        target = threeCycleNext (actualRelationIncomingIndex target) := by
          simp [actualRelationIncomingIndex]
        _ = threeCycleNext source := congrArg threeCycleNext indexEquality.symm
    rw [actualRelationIncomingRoleReadAt, if_neg roleDifferent]
    rfl

theorem actualRelationRoleReflexiveRing_generatedResidual_eq_three
    (base : Nat) :
    (actualRelationRoleReflexiveRingAt base).generatedResidual = 3 := by
  unfold FiniteReflexiveInteractionRing.generatedResidual
  rw [actualRelationRoleReflexiveRing_generatedInteractionPhase_eq]
  change (∑ index,
    actualRelationCycleCochain base index (threeCycleNext index)) = 3
  rw [threeCycleNext_sum_eq_residual]
  exact actualRelationCycle_residual_eq_three base

theorem actualRelationRoleReflexiveRing_directConsumer (base : Nat) :
    Function.Injective (actualRelationCycleTargetRoleAt base) ∧
      (∀ source target,
        actualRelationCycleSourceRoleAt base source ≠
          actualRelationCycleTargetRoleAt base target) ∧
      (actualRelationRoleReflexiveRingAt base).generatedInteractionPhase =
        actualRelationCycleCochain base ∧
      (actualRelationRoleReflexiveRingAt base).generatedResidual = 3 :=
  ⟨actualRelationCycleTargetRoleAt_injective base,
    actualRelationCycleSourceRoleAt_ne_targetRoleAt base,
    actualRelationRoleReflexiveRing_generatedInteractionPhase_eq base,
    actualRelationRoleReflexiveRing_generatedResidual_eq_three base⟩

end
end M14SourceGeneratedActualRelationRoleReflexiveRing
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedActualRelationRoleReflexiveRing.actualRelationRoleReflexiveRingAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedActualRelationRoleReflexiveRing.actualRelationRoleReflexiveRing_generatedInteractionPhase_eq
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedActualRelationRoleReflexiveRing.actualRelationRoleReflexiveRing_directConsumer
