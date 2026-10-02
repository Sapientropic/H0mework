import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffRoots.Consumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffRoots.Coordinates

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffSource
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}

abbrev JointValue (rank : Ordinal.{0}) := MotherAuthorityCoordinates.Output × MotherHandoffRoots.Value rank

/-- Current full source/root and the full dependent event/successor family
are separate projections of a single mother material. -/
def formJoint (material : MotherArenaHigher.Material rank) : Option (JointValue rank) :=
  let parts := MotherArenaHigher.split rank material
  (MotherArenaTheory.formTheory parts.1).bind (fun root =>
    (MotherHandoffRoots.formRoots parts.2).map (fun handoff => (root, handoff)))

structure JointPresentation {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeAuthoritativeRootClosure N V) (events : EventFamily root.source)
    (declaration : Declaration root.source events) (value : JointValue rank) where
  authority : MotherAuthorityRoot.Presentation root value.1.1.1 value.1.1.2 value.1.2
  handoff : MotherHandoffRoots.Presentation (Index root.source) events declaration.emit N
    (fun point => (declaration.continuation point).next.1)
    (fun point => (declaration.continuation point).next.2) value.2

abbrev JointAddress {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeAuthoritativeRootClosure N V) (events : EventFamily root.source)
    (declaration : Declaration root.source events) :=
  MotherAuthorityRoot.AddressTotal root ⊕ Index root.source ⊕ (EventPoint events) ⊕
    (Σ point, MotherAuthorityRoot.AddressTotal (declaration.continuation point).next.2)

theorem joint_at_rank {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeAuthoritativeRootClosure N V) (events : EventFamily root.source)
    (declaration : Declaration root.source events)
    (shared : JointAddress root events declaration ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank, ∃ value : JointValue rank,
      formJoint material = some value ∧ Nonempty (JointPresentation root events declaration value) := by
  let mainCode : MotherAuthorityRoot.AddressTotal root ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let indexCode : Index root.source ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let eventCode : EventPoint events ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  let rootCode : (Σ point, MotherAuthorityRoot.AddressTotal (declaration.continuation point).next.2) ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr value))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  obtain ⟨rootMaterial, rootValue, rootData, rootSurface, rootMap, rootFormed, _rootRecovered, _original⟩ :=
    MotherAuthorityRoot.root_at_rank N V root mainCode
  obtain ⟨handoffMaterial, handoffValue, handoffFormed, ⟨handoffMap⟩⟩ :=
    MotherHandoffRoots.roots_at_rank (Index root.source) events declaration.emit N
      (fun point => (declaration.continuation point).next.1)
      (fun point => (declaration.continuation point).next.2) indexCode eventCode rootCode
  refine ⟨MotherArenaHigher.pack rank (rootMaterial, handoffMaterial),
    (⟨⟨rootValue, rootData⟩, rootSurface⟩, handoffValue), ?_, ⟨⟨rootMap, handoffMap⟩⟩⟩
  simp only [formJoint, MotherArenaHigher.split_pack, rootFormed, Option.bind_some, handoffFormed, Option.map_some]

theorem joint_root_formed (material : MotherArenaHigher.Material rank) (value : JointValue rank)
    (formed : formJoint material = some value) :
    MotherArenaTheory.formTheory (MotherArenaHigher.split rank material).1 = some value.1 := by
  unfold formJoint at formed
  dsimp only at formed
  obtain ⟨root, rootFormed, selected⟩ := Option.bind_eq_some_iff.mp formed
  obtain ⟨handoff, _handoffFormed, same⟩ := Option.map_eq_some_iff.mp selected
  exact rootFormed.trans (congrArg some (congrArg Prod.fst same))

theorem joint_handoff_formed (material : MotherArenaHigher.Material rank) (value : JointValue rank)
    (formed : formJoint material = some value) :
    MotherHandoffRoots.formRoots (MotherArenaHigher.split rank material).2 = some value.2 := by
  unfold formJoint at formed
  dsimp only at formed
  obtain ⟨root, _rootFormed, selected⟩ := Option.bind_eq_some_iff.mp formed
  obtain ⟨handoff, handoffFormed, same⟩ := Option.map_eq_some_iff.mp selected
  exact handoffFormed.trans (congrArg some (congrArg Prod.snd same))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffSource
