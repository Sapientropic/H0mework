import H0mework.Foundation.Inquiry.Engine
import Mathlib.Logic.Equiv.Defs

/-! Coverage-side recharting of the entire original inquiry process.  The
material factory does not call `rechart` or receive its target process.
Whole native nodes are retained, so every dependent query and every complete
compiler branch keeps its original root, authority, and face indices. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRegistryRecovery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

universe u

structure Presentation (source target : SourceNativeInquiryEngineProcess.{u}) where
  state : source.State ≃ target.State
  node : ∀ current, source.stateAt current = target.stateAt (state current)
  initial : state source.initial = target.initial
  successor : ∀ current query,
    state (source.successorAt current query).val =
      (target.successorAt (state current)
        (Eq.mp (congrArg RootInquiryProcessNode.Query (node current)) query)).val

def rechart (target : SourceNativeInquiryEngineProcess.{u})
    {Carrier : Type u} (state : Carrier ≃ target.State) :
    SourceNativeInquiryEngineProcess.{u} where
  State := Carrier
  stateAt := fun current => target.stateAt (state current)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive erased
    exact state.injective (target.erase_injective leftActive rightActive erased)
  initial := state.symm target.initial
  successorAt := fun current query =>
    ⟨state.symm (target.successorAt (state current) query).val, by
      simpa only [Equiv.apply_symm_apply] using
        (target.successorAt (state current) query).property⟩

def rechartPresentation (target : SourceNativeInquiryEngineProcess.{u})
    {Carrier : Type u} (state : Carrier ≃ target.State) :
    Presentation (rechart target state) target where
  state := state
  node := fun _ => rfl
  initial := state.apply_symm_apply target.initial
  successor := fun current query =>
    state.apply_symm_apply (target.successorAt (state current) query).val

def Compilation : (node : RootInquiryProcessNode.{u}) → node.Query → Type (u + 11)
  | .active state, query => type_of% (state.state.base.compileInquiry query)
  | .answered _ _, query => nomatch query

def compile : (node : RootInquiryProcessNode.{u}) → (query : node.Query) → Compilation node query
  | .active state, query => state.state.base.compileInquiry query
  | .answered _ _, query => nomatch query

private theorem compile_of_node_eq {source target : RootInquiryProcessNode.{u}}
    (same : source = target) (query : source.Query) :
    HEq (compile source query)
      (compile target (Eq.mp (congrArg RootInquiryProcessNode.Query same) query)) := by
  cases same
  rfl

namespace Presentation

variable {source target : SourceNativeInquiryEngineProcess.{u}}

def query (presentation : Presentation source target)
    (current : source.State) :
    (source.stateAt current).Query ≃ (target.stateAt (presentation.state current)).Query :=
  Equiv.cast (congrArg RootInquiryProcessNode.Query (presentation.node current))

def events (presentation : Presentation source target) :
    (Σ current : source.State, (source.stateAt current).Query) ≃
      (Σ current : target.State, (target.stateAt current).Query) :=
  Equiv.sigmaCongr presentation.state presentation.query

theorem erase_eq (presentation : Presentation source target) (current : source.State) :
    (source.stateAt current).erase = (target.stateAt (presentation.state current)).erase :=
  congrArg RootInquiryProcessNode.erase (presentation.node current)

theorem compile_heq (presentation : Presentation source target)
    (current : source.State) (query : (source.stateAt current).Query) :
    HEq (compile (source.stateAt current) query)
      (compile (target.stateAt (presentation.state current))
        (presentation.query current query)) := by
  exact compile_of_node_eq (presentation.node current) query

end Presentation

end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRegistryRecovery
