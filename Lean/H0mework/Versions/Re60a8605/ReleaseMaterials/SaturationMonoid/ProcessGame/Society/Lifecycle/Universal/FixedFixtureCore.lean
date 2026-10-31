import H0mework.Foundation.Agency.LifecycleSeeds
import H0mework.Foundation.Agency.FibreExhaustion
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.ActualActorEvent

/-!
# Fixed six-class fixture as a universal two-state core

The earlier neutral-token fixture is installed on the universal adjacent
edge API.  This module supplies only exact source data and fibre calculations;
the sealed lifecycle law and responsibility edge live in the companion file.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Lifecycle
namespace Universal
namespace FixedAdapter

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open _root_.SaturationMonoid.ProcessGame.Society.Lifecycle

def sourceFace : M0BoundaryFace actualEventOccurrenceOf where
  Seed := SourceToken
  Lineage := fun _ => SourceToken
  SeedAt := sourceSeedAt
  lineageOf := fun _ seed => seed.1
  state := fun _ => .before
  seedAt_state := by
    intro source state seed active
    exact active

def targetFace : M0BoundaryFace actualEventOccurrenceOf where
  Seed := TargetToken
  Lineage := fun _ => TargetToken
  SeedAt := targetSeedAt
  lineageOf := fun _ seed => seed.1
  state := fun _ => .after
  seedAt_state := by
    intro source state seed active
    exact active

def historySeedAt (_source : Unit) (state : EventState)
    (_seed : SourceToken) : Prop :=
  state = .before

def core : SourceOwnedLifecycleCore actualEventOccurrenceOf actualEventGame where
  sourceFace := sourceFace
  targetFace := targetFace
  HistorySeed := SourceToken
  HistoryLineage := fun _ => SourceToken
  historySeedAt := historySeedAt
  historyLineageOf := fun _ seed => seed.1
  LinkSeed := TransferToken
  linkAdmittedAt := fun link => eventTransfers link.1 link.2
  linkSource := Prod.fst
  linkTarget := Prod.snd
  linkSource_active := by
    intro link admitted
    rfl
  linkTarget_active := by
    intro link admitted
    rfl
  IdentitySeed := IdentitySeed
  identityAdmittedAt := fun _ => True
  identitySource := fun _ => .s0
  identityTarget := fun _ => .t0
  identitySource_active := by
    intro identity admitted
    rfl
  identityTarget_active := by
    intro identity admitted
    rfl
  ExitSeed := Unit
  exitAdmittedAt := fun _ => True
  exitSource := fun _ => .s4
  exitSource_active := by
    intro exit admitted
    rfl
  FreshSeed := Unit
  freshAdmittedAt := fun _ => True
  freshTarget := fun _ => .t5
  freshTarget_active := by
    intro fresh admitted
    rfl
  ReappearanceSeed := Empty
  reappearanceAdmittedAt := fun reappearance => nomatch reappearance
  reappearanceHistory := fun reappearance => nomatch reappearance
  reappearanceHistoryState := fun reappearance => nomatch reappearance
  reappearanceHistory_active := by
    intro reappearance
    exact nomatch reappearance
  reappearanceTarget := fun reappearance => nomatch reappearance
  reappearanceTarget_active := by
    intro reappearance
    exact nomatch reappearance
  sourceIndex := 0
  source_state_mem := by simp [actualEventOccurrenceOf, sourceFace]
  target_state_mem := by simp [actualEventOccurrenceOf, targetFace]
  source_at_index := rfl
  target_follows_source := rfl
  history_before_event := by
    intro state seed active
    subst state
    simp [actualEventOccurrenceOf]

def sourceActor (token : SourceToken) : core.SourceActor :=
  core.sourceActorOf (sourceSeed token)

def targetActor (token : TargetToken) : core.TargetActor :=
  core.targetActorOf (targetSeed token)

@[simp] theorem sourceActor_value (token : SourceToken) :
    (sourceActor token).1 = token :=
  rfl

@[simp] theorem targetActor_value (token : TargetToken) :
    (targetActor token).1 = token :=
  rfl

def exactLink (source : SourceToken) (target : TargetToken)
    (admitted : eventTransfers source target) : core.ExactLinkSeed :=
  transferSeed source target admitted

def exactIdentity : core.ExactIdentitySeed :=
  ⟨.i0, .after, by simp [actualEventOccurrenceOf], rfl, trivial⟩

def identityAuthority :
    core.DomainIdentityTransportAt (sourceActor .s0) (targetActor .t0) where
  identity := exactIdentity
  source_eq := rfl
  target_eq := rfl

def exactExit : core.ExactExitSeed :=
  ⟨(), .after, by simp [actualEventOccurrenceOf], rfl, trivial⟩

def exitAuthority : core.DomainExitAuthorityAt (sourceActor .s4) where
  exit := exactExit
  source_eq := rfl

def exactFresh : core.ExactFreshSeed :=
  ⟨(), .after, by simp [actualEventOccurrenceOf], rfl, trivial⟩

def freshAuthority : core.DomainFreshOriginAt (targetActor .t5) where
  fresh := exactFresh
  target_eq := rfl

@[simp] theorem actorRelated_iff (source : core.SourceActor)
    (target : core.TargetActor) :
    core.ActorRelated source target ↔ eventTransfers source.1 target.1 := by
  constructor
  · rintro ⟨link, sourceEq, targetEq⟩
    have admitted := link.admitted core
    have sourceValue := congrArg Subtype.val sourceEq
    have targetValue := congrArg Subtype.val targetEq
    change link.1.1 = source.1 at sourceValue
    change link.1.2 = target.1 at targetValue
    change eventTransfers link.1.1 link.1.2 at admitted
    rw [sourceValue, targetValue] at admitted
    exact admitted
  · intro admitted
    refine ⟨exactLink source.1 target.1 admitted, ?_, ?_⟩
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

theorem relation_s0_t0 :
    core.ActorRelated (sourceActor .s0) (targetActor .t0) := by
  simp [eventTransfers]

theorem relation_s1_t1 :
    core.ActorRelated (sourceActor .s1) (targetActor .t1) := by
  simp [eventTransfers]

theorem relation_s1_t2 :
    core.ActorRelated (sourceActor .s1) (targetActor .t2) := by
  simp [eventTransfers]

theorem relation_s2_t1 :
    core.ActorRelated (sourceActor .s2) (targetActor .t1) := by
  simp [eventTransfers]

theorem relation_s2_t2 :
    core.ActorRelated (sourceActor .s2) (targetActor .t2) := by
  simp [eventTransfers]

theorem relation_s2_t3 :
    core.ActorRelated (sourceActor .s2) (targetActor .t3) := by
  simp [eventTransfers]

theorem relation_s3_t3 :
    core.ActorRelated (sourceActor .s3) (targetActor .t3) := by
  simp [eventTransfers]

theorem relation_s5_t4 :
    core.ActorRelated (sourceActor .s5) (targetActor .t4) := by
  simp [eventTransfers]

theorem split_s1 : core.SplitAt (sourceActor .s1) :=
  ⟨targetActor .t1, targetActor .t2, relation_s1_t1, relation_s1_t2,
    by intro equal; cases congrArg Subtype.val equal⟩

theorem split_s2 : core.SplitAt (sourceActor .s2) :=
  ⟨targetActor .t1, targetActor .t2, relation_s2_t1, relation_s2_t2,
    by intro equal; cases congrArg Subtype.val equal⟩

theorem split_s3 : core.SplitAt (sourceActor .s3) :=
  ⟨targetActor .t1, targetActor .t2,
    by simp [eventTransfers], by simp [eventTransfers],
    by intro equal; cases congrArg Subtype.val equal⟩

theorem merge_t1 : core.MergeAt (targetActor .t1) :=
  ⟨sourceActor .s1, sourceActor .s2, relation_s1_t1, relation_s2_t1,
    by intro equal; cases congrArg Subtype.val equal⟩

theorem merge_t3 : core.MergeAt (targetActor .t3) :=
  ⟨sourceActor .s2, sourceActor .s3, relation_s2_t3, relation_s3_t3,
    by intro equal; cases congrArg Subtype.val equal⟩

theorem exit_s4 : core.ExitAt (sourceActor .s4) := by
  intro target related
  have admitted := (actorRelated_iff _ _).mp related
  cases targetValue : target.1 <;>
    rw [targetValue] at admitted <;>
    simp [eventTransfers] at admitted

theorem empty_t5 : core.EmptyPredecessorAt (targetActor .t5) := by
  intro source related
  have admitted := (actorRelated_iff _ _).mp related
  cases sourceValue : source.1 <;>
    rw [sourceValue] at admitted <;>
    simp [eventTransfers] at admitted

theorem singleton_s0_t0 :
    core.SingletonDescendantAt (sourceActor .s0) (targetActor .t0) ∧
      core.SingletonPredecessorAt (sourceActor .s0) (targetActor .t0) := by
  constructor
  · refine ⟨relation_s0_t0, ?_⟩
    intro target related
    have admitted := (actorRelated_iff _ _).mp related
    have value : target.1 = .t0 := by
      cases targetValue : target.1 <;>
        rw [targetValue] at admitted <;>
        simp [eventTransfers] at admitted
    apply Subtype.ext
    exact value
  · refine ⟨relation_s0_t0, ?_⟩
    intro source related
    have admitted := (actorRelated_iff _ _).mp related
    have value : source.1 = .s0 := by
      cases sourceValue : source.1 <;>
        rw [sourceValue] at admitted <;>
        simp [eventTransfers] at admitted
    apply Subtype.ext
    exact value

theorem singleton_s5_t4 :
    core.SingletonDescendantAt (sourceActor .s5) (targetActor .t4) ∧
      core.SingletonPredecessorAt (sourceActor .s5) (targetActor .t4) := by
  constructor
  · refine ⟨relation_s5_t4, ?_⟩
    intro target related
    have admitted := (actorRelated_iff _ _).mp related
    have value : target.1 = .t4 := by
      cases targetValue : target.1 <;>
        rw [targetValue] at admitted <;>
        simp [eventTransfers] at admitted
    apply Subtype.ext
    exact value
  · refine ⟨relation_s5_t4, ?_⟩
    intro source related
    have admitted := (actorRelated_iff _ _).mp related
    have value : source.1 = .s5 := by
      cases sourceValue : source.1 <;>
        rw [sourceValue] at admitted <;>
        simp [eventTransfers] at admitted
    apply Subtype.ext
    exact value

theorem eventTransfers_cases (source : SourceToken) (target : TargetToken)
    (admitted : eventTransfers source target) :
    (source = .s0 ∧ target = .t0) ∨
      ((source = .s1 ∨ source = .s2 ∨ source = .s3) ∧
        (target = .t1 ∨ target = .t2 ∨ target = .t3)) ∨
      (source = .s5 ∧ target = .t4) := by
  cases source <;> cases target <;>
    simp [eventTransfers] at admitted ⊢

end FixedAdapter
end Universal
end Lifecycle
end Society
end ProcessGame
end SaturationMonoid
