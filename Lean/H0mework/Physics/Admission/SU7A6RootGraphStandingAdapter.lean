import H0mework.Physics.Source.RawSourceDynamics
import H0mework.Physics.Admission.StandingPullback
import H0mework.Arithmetic.SourceAtoms.EndpointCoordinates

/-!
# Unfiltered SU7/A6 root-graph standing adapter

`SU7RepresentationGeneratedRepairLaw` already contains a genuine A6 Cartan
operation: `su7A6LowerBySimpleRoot`.  It acts on Dynkin-coordinate labels and
every simple-root move lowers the signed height by exactly one.  This module
uses that operation below branching, endpoint filtering, P950, thin source
data, and coverage.

A derivation state is a multiset of simple-root moves.  Its current A6 label
is the root label minus the sum of the corresponding Cartan rows.  Multisets
are the correct path carrier here: simple-root lowering is translation by a
fixed Cartan row, so order is irrelevant.  From two descendants `x` and `y`
of the same root, both can reach `x + y`; this gives a genuine global
confluence theorem for the unfiltered A6 root graph.

The result is deliberately not the missing physical SU7 producer.  It proves
native source reachability, signed-height monotonicity, and path confluence at
the unfiltered representation layer.  The still-open hard gate is that these
root moves survive branching, no-prime/endpoint filtering, and completion and
then generate the same source object consumed by gauge and gluing operations.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7A6RootGraphStandingAdapter

open StandardModelConstraint

noncomputable section

abbrev RootIndex := Fin 6
abbrev DerivationState := Multiset RootIndex

/-- Sum of Cartan rows selected by the commutative derivation state. -/
def cartanDisplacement
    (moves : DerivationState) (coordinate : RootIndex) : Int :=
  (moves.map fun root => su7A6CartanEntry root coordinate).sum

/-- Current Dynkin label generated from a root label and root-move multiset.
-/
def generatedLabel
    (root : SU7A6WeightLabel) (moves : DerivationState) :
    SU7A6WeightLabel :=
  fun coordinate => root coordinate - cartanDisplacement moves coordinate

@[simp] theorem generatedLabel_zero
    (root : SU7A6WeightLabel) :
    generatedLabel root 0 = root := by
  funext coordinate
  simp [generatedLabel, cartanDisplacement]

/-- Adding one root to the multiset is exactly the repository's native A6
simple-root lowering operation. -/
theorem generatedLabel_cons
    (root : SU7A6WeightLabel)
    (moves : DerivationState) (simpleRoot : RootIndex) :
    generatedLabel root (simpleRoot ::ₘ moves) =
      su7A6LowerBySimpleRoot simpleRoot (generatedLabel root moves) := by
  funext coordinate
  simp [generatedLabel, cartanDisplacement, su7A6LowerBySimpleRoot]
  ring

/-- Six native successor states, one for each A6 simple root. -/
def successors (moves : DerivationState) : List DerivationState :=
  (List.finRange 6).map fun simpleRoot => simpleRoot ::ₘ moves

/-- Raw source system rooted at the empty derivation.  `current` is an
operation input, not a reachability certificate. -/
def sourceSystem
    (root : SU7A6WeightLabel) (current : DerivationState) :
    RawSourceDynamics DerivationState DerivationState Int where
  roots := [0]
  successors := successors
  current := some current
  handleOf := id
  energyOf := fun moves => su7A6SignedHeight (generatedLabel root moves)

theorem step_cons
    (root : SU7A6WeightLabel) (current moves : DerivationState)
    (simpleRoot : RootIndex) :
    (sourceSystem root current).Step moves (simpleRoot ::ₘ moves) := by
  simp [RawSourceDynamics.Step, sourceSystem, successors]

/-- Any finite multiset of root moves is generated from the empty root state.
-/
theorem reachableFrom_zero
    (root : SU7A6WeightLabel) (current moves : DerivationState) :
    (sourceSystem root current).ReachableFrom 0 moves := by
  induction moves using Multiset.induction_on with
  | empty => exact Relation.ReflTransGen.refl
  | @cons simpleRoot tail ih =>
      exact ih.trans
        (Relation.ReflTransGen.single
          (step_cons root current tail simpleRoot))

theorem everyState_reachable
    (root : SU7A6WeightLabel) (current moves : DerivationState) :
    (sourceSystem root current).Reachable moves := by
  exact ⟨0, by simp [sourceSystem], reachableFrom_zero root current moves⟩

theorem currentSourceReachable
    (root : SU7A6WeightLabel) (current : DerivationState) :
    (sourceSystem root current).CurrentSourceReachable := by
  exact ⟨current, rfl, 0, by simp [sourceSystem],
    reachableFrom_zero root current current⟩

/-- Every native A6 edge is an exact signed-height unit descent. -/
theorem step_signedHeight_unit
    (root : SU7A6WeightLabel) (current : DerivationState)
    {source target : DerivationState}
    (hstep : (sourceSystem root current).Step source target) :
    su7A6SignedHeight (generatedLabel root target) + 1 =
      su7A6SignedHeight (generatedLabel root source) := by
  change target ∈ successors source at hstep
  simp only [successors, List.mem_map, List.mem_finRange] at hstep
  rcases hstep with ⟨simpleRoot, _hbound, rfl⟩
  rw [generatedLabel_cons]
  exact su7A6SignedHeight_lowerBySimpleRoot
    (generatedLabel root source) simpleRoot

theorem sourceEnergyMonotone
    (root : SU7A6WeightLabel) (current : DerivationState) :
    (sourceSystem root current).SourceEnergyMonotone := by
  intro source target hstep
  have hunit := step_signedHeight_unit root current hstep
  change
    su7A6SignedHeight (generatedLabel root target) ≤
      su7A6SignedHeight (generatedLabel root source)
  omega

/-- Starting at `left`, append every move in `right`. -/
theorem reachableFrom_add
    (root : SU7A6WeightLabel) (current : DerivationState)
    (left right : DerivationState) :
    (sourceSystem root current).ReachableFrom left (left + right) := by
  induction right using Multiset.induction_on with
  | empty =>
      change Relation.ReflTransGen
        (sourceSystem root current).Step left (left + 0)
      simpa using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen
            (sourceSystem root current).Step left left)
  | @cons simpleRoot tail ih =>
      have hstep :
          (sourceSystem root current).Step
            (left + tail) (simpleRoot ::ₘ (left + tail)) :=
        step_cons root current (left + tail) simpleRoot
      have hpath := ih.trans (Relation.ReflTransGen.single hstep)
      change Relation.ReflTransGen (sourceSystem root current).Step
        left (left + (simpleRoot ::ₘ tail))
      simpa [Multiset.add_cons] using hpath

/-- Root-lowering paths are globally confluent before filtering: two
descendants join at the multiset union of their root moves. -/
theorem graphConfluent
    (root : SU7A6WeightLabel) (current : DerivationState) :
    (sourceSystem root current).GraphConfluent := by
  intro declaredRoot hroot left right hleft hright
  have hrootZero : declaredRoot = 0 := by
    simpa [sourceSystem] using hroot
  subst declaredRoot
  refine ⟨left + right, reachableFrom_add root current left right, ?_⟩
  simpa [Multiset.add_comm] using
    (reachableFrom_add root current right left)

/-- The retained handle is the commutative derivation multiset itself.  This
proves provenance-handle faithfulness; it does not claim here that the current
Dynkin-label readout is injective without a separate Cartan-lattice theorem.
-/
theorem handleFaithfulOnReachable
    (root : SU7A6WeightLabel) (current : DerivationState) :
    (sourceSystem root current).HandleFaithfulOnReachable := by
  intro left right _hleft _hright hhandle
  exact hhandle

theorem sourceSystem_admissible
    (root : SU7A6WeightLabel) (current : DerivationState) :
    (sourceSystem root current).SourceDynamicsAdmissible :=
  ⟨currentSourceReachable root current,
    sourceEnergyMonotone root current,
    graphConfluent root current,
    handleFaithfulOnReachable root current⟩

/-! ## Nonconstant-lineage native standing graph -/

structure Presentation where
  rootLabel : SU7A6WeightLabel
  moves : DerivationState

namespace Presentation

def currentLabel (presentation : Presentation) : SU7A6WeightLabel :=
  generatedLabel presentation.rootLabel presentation.moves

def sourceReachable (presentation : Presentation) : Prop :=
  (sourceSystem presentation.rootLabel presentation.moves).Reachable
    presentation.moves

def sourceConfluent (presentation : Presentation) : Prop :=
  (sourceSystem presentation.rootLabel presentation.moves).GraphConfluent

end Presentation

def apply
    (simpleRoot : RootIndex) (presentation : Presentation) :
    Option Presentation :=
  some
    { rootLabel := presentation.rootLabel
      moves := simpleRoot ::ₘ presentation.moves }

def operations :
    AnchoredStandingOperations Presentation RootIndex SU7A6WeightLabel where
  toNativeStandingOperations := { apply }
  anchor := Presentation.rootLabel
  anchor_preserved := by
    intro simpleRoot source result happlies
    change some
        { rootLabel := source.rootLabel
          moves := simpleRoot ::ₘ source.moves } = some result at happlies
    injection happlies with hresult
    subst result
    rfl

theorem sourceReachable_nativeMoveInvariant :
    NativeMoveInvariant operations.toNativeStandingOperations
      Presentation.sourceReachable := by
  intro move source result happlies
  exact iff_of_true
    (everyState_reachable source.rootLabel source.moves source.moves)
    (everyState_reachable result.rootLabel result.moves result.moves)

theorem sourceReachable_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity operations.toNativeStandingOperations)
      Presentation.sourceReachable :=
  (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
    operations.toNativeStandingOperations _).mpr
      sourceReachable_nativeMoveInvariant

theorem sourceConfluent_nativeMoveInvariant :
    NativeMoveInvariant operations.toNativeStandingOperations
      Presentation.sourceConfluent := by
  intro move source result happlies
  exact iff_of_true
    (graphConfluent source.rootLabel source.moves)
    (graphConfluent result.rootLabel result.moves)

theorem sourceConfluent_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity operations.toNativeStandingOperations)
      Presentation.sourceConfluent :=
  (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
    operations.toNativeStandingOperations _).mpr
      sourceConfluent_nativeMoveInvariant

/-- Every native standing move is the same repository A6 simple-root move on
the generated current label. -/
theorem currentLabel_of_apply
    (simpleRoot : RootIndex) (source result : Presentation)
    (happlies : apply simpleRoot source = some result) :
    result.currentLabel =
      su7A6LowerBySimpleRoot simpleRoot source.currentLabel := by
  change some
      { rootLabel := source.rootLabel
        moves := simpleRoot ::ₘ source.moves } = some result at happlies
  injection happlies with hresult
  subst result
  exact generatedLabel_cons source.rootLabel source.moves simpleRoot

/-- Different A6 roots remain different source lineages even though every
lineage has the same root-move operation shape. -/
theorem different_root_not_sameStanding
    {left right : Presentation}
    (hne : left.rootLabel ≠ right.rootLabel) :
    ¬ GeneratedStandingEquiv operations.toNativeStandingOperations
        left right := by
  intro hstanding
  have hanchor := operations.anchor_eq_of_generatedStandingEquiv hstanding
  exact hne hanchor.symm

end
end SU7A6RootGraphStandingAdapter
end PhysicsCore
end SaturationMonoid
