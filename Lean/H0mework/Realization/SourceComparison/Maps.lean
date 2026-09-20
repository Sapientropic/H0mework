import H0mework.Realization.SourceComparison.RawConsumption

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot
namespace SourceComparison

universe u v w

/-- Local material maps preserve the original input, emitter, and every event update.
No inverse, root, history, equivalence, or final physical result is supplied. -/
structure Map (source : Dynamics.{u}) (target : Dynamics.{v}) where
  state : source.State → target.State
  event : {current : source.State} → source.EventAt current → target.EventAt (state current)
  initial : state source.initial = target.initial
  emitted : ∀ current, event (source.emit current) = target.emit (state current)
  updated : ∀ {current} (actual : source.EventAt current),
    state (source.update actual) = target.update (event actual)

variable {source : Dynamics.{u}} {target : Dynamics.{v}} {next : Dynamics.{w}}

def Map.identity (source : Dynamics.{u}) : Map source source where
  state := id
  event := id
  initial := rfl
  emitted := fun _ => rfl
  updated := fun _ => rfl

def Map.then (first : Map source target) (last : Map target next) : Map source next where
  state := last.state ∘ first.state
  event := fun actual => last.event (first.event actual)
  initial := by change last.state (first.state source.initial) = _; rw [first.initial, last.initial]
  emitted := fun current => by rw [first.emitted, last.emitted]; rfl
  updated := fun actual => by change last.state (first.state (source.update actual)) = _; rw [first.updated, last.updated]

theorem Map.generated (map : Map source target) (index : ℕ) :
    map.state (currentAt source index) = currentAt target index := by
  induction index with
  | zero => exact map.initial
  | succ index prior =>
    change map.state (source.update (source.emit (currentAt source index))) = _
    rw [map.updated, map.emitted, prior]
    rfl

def Generated (source : Dynamics.{u}) := Set.range (currentAt source)

def generatedAt (source : Dynamics.{u}) (index : ℕ) : Generated source :=
  ⟨currentAt source index, index, rfl⟩

def Map.restrict (map : Map source target) (current : Generated source) : Generated target :=
  ⟨map.state current.val, by
    rcases current.property with ⟨index, same⟩
    exact ⟨index, (map.generated index).symm.trans (congrArg map.state same)⟩⟩

theorem Map.restrict_at (map : Map source target) (index : ℕ) :
    map.restrict (generatedAt source index) = generatedAt target index :=
  Subtype.ext (map.generated index)

theorem Map.restrict_unique (first last : Map source target) :
    first.restrict = last.restrict := by
  funext current
  rcases current with ⟨_, index, rfl⟩
  exact (first.restrict_at index).trans (last.restrict_at index).symm

def advance (current : Generated source) : Generated source :=
  ⟨source.update (source.emit current.val), by
    rcases current.property with ⟨index, same⟩
    exact ⟨index + 1, congrArg (fun state => source.update (source.emit state)) same⟩⟩

theorem Map.advance (map : Map source target) (current : Generated source) :
    map.restrict (advance current) = advance (map.restrict current) := by
  apply Subtype.ext
  exact (map.updated _).trans (congrArg target.update (map.emitted current.val))

end SourceComparison
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot
