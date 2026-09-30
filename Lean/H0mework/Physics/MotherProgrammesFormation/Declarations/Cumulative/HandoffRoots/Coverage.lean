import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffRoots.Factory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRoots
open MotherHandoffEvents
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}

def pointEquiv {I : Type} {events : I → Type} {emit : (index : I) → events index}
    {value : MotherHandoffEvents.Value rank} (p : MotherHandoffEvents.Presentation I events emit value) :
    Sigma events ≃ Point value.1 := Equiv.sigmaCongr p.context p.event

structure Presentation (I : Type) (events : I → Type) (emit : (index : I) → events index)
    (N : WorldRelationNetwork.{0}) (V : Sigma events → ConstructiveRoot.Vocabulary.{0})
    (roots : (point : Sigma events) → SourceNativeAuthoritativeRootClosure N (V point))
    (value : Value rank) where
  event : MotherHandoffEvents.Presentation I events emit value.1
  root : ∀ point, MotherAuthorityRoot.Presentation (roots point)
    (value.2 (pointEquiv event point)).1.1 (value.2 (pointEquiv event point)).1.2 (value.2 (pointEquiv event point)).2

variable {I : Type} {events : I → Type} {emit : (index : I) → events index}
    {N : WorldRelationNetwork.{0}} {V : Sigma events → ConstructiveRoot.Vocabulary.{0}}
    {roots : (point : Sigma events) → SourceNativeAuthoritativeRootClosure N (V point)} {value : Value rank}

def Presentation.restrictRoots (p : Presentation I events emit N V roots value) :
    Sigma events → (Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, SourceNativeAuthoritativeRootClosure N vocabulary) :=
  fun point => (p.root point).restrictHeader

theorem Presentation.restrictRoots_eq (p : Presentation I events emit N V roots value) :
    p.restrictRoots = fun point => ⟨V point, roots point⟩ :=
  funext (fun point => (p.root point).restrictHeader_eq)

theorem roots_at_rank (I : Type) (events : I → Type) (emit : (index : I) → events index)
    (N : WorldRelationNetwork.{0}) (V : Sigma events → ConstructiveRoot.Vocabulary.{0})
    (roots : (point : Sigma events) → SourceNativeAuthoritativeRootClosure N (V point))
    (indexCode : I ↪ MotherArenaHigher.Base rank)
    (eventCode : Sigma events ↪ MotherArenaHigher.Base rank)
    (rootCode : (Σ point, MotherAuthorityRoot.AddressTotal (roots point)) ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank, ∃ value : Value rank,
      formRoots material = some value ∧ Nonempty (Presentation I events emit N V roots value) := by
  obtain ⟨parent, eventValue, parentFormed, ⟨eventMap⟩⟩ :=
    MotherHandoffEvents.every_events_at I events emit indexCode eventCode
  have allRoots : ∀ point, MotherAuthorityRoot.FormationAt rank (roots point) := fun point =>
    MotherAuthorityRoot.root_at_rank N (V point) (roots point)
      ((Function.Embedding.sigmaMk point).trans rootCode)
  simp only [MotherAuthorityRoot.FormationAt] at allRoots
  choose materials values data surfaces presentations formed recovered original using allRoots
  let points := pointEquiv eventMap
  let children : Point eventValue.1 → MotherAuthorityFamilies.Output := fun point =>
    ⟨⟨values (points.symm point), data (points.symm point)⟩, surfaces (points.symm point)⟩
  obtain ⟨material, formedFamily⟩ := roots_on_events parent eventValue parentFormed children
    (fun point => materials (points.symm point)) (fun point => formed (points.symm point))
  refine ⟨material, ⟨eventValue, children⟩, formedFamily, ⟨{
    event := eventMap
    root := fun point => ?_ }⟩⟩
  change MotherAuthorityRoot.Presentation (roots point)
    (values (points.symm (points point))) (data (points.symm (points point)))
    (surfaces (points.symm (points point)))
  rw [points.symm_apply_apply]
  exact presentations point

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRoots
