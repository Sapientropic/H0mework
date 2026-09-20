/-
  Proposition 54: structural generator-to-recollection correspondence.

  Proposition 53 gave a finite witness: a graph-side cross-boundary generator
  can be specified independently and then shown strongly isomorphic to a
  recollection act that installs future trace.

  This file abstracts the reusable theorem behind that witness.  A
  `GeneratorTraceBridge` consists of:

    * an obstruction-generator support language;
    * a recollection trace loop;
    * a strong support isomorphism between the generator support and the
      recollection act of that loop.

  From those ingredients, maximal silent domains, presentation uniqueness,
  pointwise nonempty support, and trace-installation all follow.  This is still
  not a proof that every runtime obstruction has such a bridge, but it is the
  abstract theorem that any future runtime bridge must instantiate.
-/

import H0mework.Realization.Memory.GraphGenerator

/-! ## Generic support maximality and presentations -/

/-- A state is silent for a support language when no atom is produced there. -/
def SupportSilentAt {State Atom : Type*}
    (support : State -> Atom -> Prop) (x : State) : Prop :=
  forall atom, support x atom -> False

/-- A domain is silent when every point in it is support-silent. -/
def SupportSilentDomain {State Atom : Type*}
    (support : State -> Atom -> Prop) (D : State -> Prop) : Prop :=
  forall x, D x -> SupportSilentAt support x

/-- A domain is greatest support-silent when it is silent and contains every
other silent domain. -/
def IsGreatestSupportSilentDomain {State Atom : Type*}
    (support : State -> Atom -> Prop) (C : State -> Prop) : Prop :=
  SupportSilentDomain support C /\
    forall D : State -> Prop, SupportSilentDomain support D -> PredSubset D C

/-- THEOREM 1: support-silent states form the greatest no-production domain for
any support language. -/
theorem supportSilentStates_greatest {State Atom : Type*}
    (support : State -> Atom -> Prop) :
    IsGreatestSupportSilentDomain support (SupportSilentAt support) := by
  constructor
  · intro x hx
    exact hx
  · intro D hD x hx
    exact hD x hx

/-- A presentation of a support language by an arbitrary representation `O`. -/
structure SupportPresentation {State Atom : Type*}
    (support : State -> Atom -> Prop) (O : Type*) where
  classify : State -> O
  decodes : O -> Atom -> Prop
  sound : forall x atom, decodes (classify x) atom -> support x atom
  complete : forall x atom, support x atom -> decodes (classify x) atom

/-- THEOREM 2: every sound-and-complete support presentation decodes to exactly
the support predicate. -/
theorem supportPresentation_unique_support {State Atom O : Type*}
    (support : State -> Atom -> Prop)
    (pres : SupportPresentation support O)
    (x : State) (atom : Atom) :
    pres.decodes (pres.classify x) atom <-> support x atom := by
  constructor
  · exact pres.sound x atom
  · exact pres.complete x atom

/-- THEOREM 3: any two sound-and-complete support presentations are equivalent
after decoding. -/
theorem supportPresentations_equivalent {State Atom O₁ O₂ : Type*}
    (support : State -> Atom -> Prop)
    (pres₁ : SupportPresentation support O₁)
    (pres₂ : SupportPresentation support O₂)
    (x : State) (atom : Atom) :
    pres₁.decodes (pres₁.classify x) atom <->
      pres₂.decodes (pres₂.classify x) atom := by
  calc
    pres₁.decodes (pres₁.classify x) atom <-> support x atom :=
      supportPresentation_unique_support support pres₁ x atom
    _ <-> pres₂.decodes (pres₂.classify x) atom :=
      (supportPresentation_unique_support support pres₂ x atom).symm

namespace StrongSupportIsomorphism

variable {State LeftAtom RightAtom O : Type*}
variable {left : State -> LeftAtom -> Prop}
variable {right : State -> RightAtom -> Prop}

/-- Transport a support presentation across a strong support isomorphism. -/
def transportRightPresentation
    (I : StrongSupportIsomorphism State LeftAtom RightAtom left right)
    (pres : SupportPresentation left O) :
    SupportPresentation right O where
  classify := pres.classify
  decodes := fun o b => pres.decodes o (I.atomEquiv.symm b)
  sound := by
    intro x b hdec
    let a := I.atomEquiv.symm b
    have hleft : left x a := pres.sound x a hdec
    have hright : right x (I.atomEquiv a) := (I.support_iff x a).mp hleft
    simpa [a] using hright
  complete := by
    intro x b hright
    let a := I.atomEquiv.symm b
    have hright' : right x (I.atomEquiv a) := by
      simpa [a] using hright
    exact pres.complete x a ((I.support_iff x a).mpr hright')

/-- THEOREM 4: transported presentations are sound and complete for the right
support language. -/
theorem transportedPresentation_unique_support
    (I : StrongSupportIsomorphism State LeftAtom RightAtom left right)
    (pres : SupportPresentation left O)
    (x : State) (b : RightAtom) :
    (I.transportRightPresentation pres).decodes
        ((I.transportRightPresentation pres).classify x) b <->
      right x b := by
  exact supportPresentation_unique_support right
    (I.transportRightPresentation pres) x b

end StrongSupportIsomorphism

/-! ## Generator-to-recollection bridge -/

/-- A bridge from an independently specified obstruction-generator support
language to a recollection trace loop. -/
structure GeneratorTraceBridge
    (State Observation GeneratorAtom ActAtom TraceAtom : Type*) where
  loop : RecollectionTraceLoop State Observation ActAtom TraceAtom
  generatorSupport : State -> GeneratorAtom -> Prop
  iso :
    StrongSupportIsomorphism State GeneratorAtom ActAtom
      generatorSupport loop.act.fires

namespace GeneratorTraceBridge

variable {State Observation GeneratorAtom ActAtom TraceAtom O : Type*}

/-- THEOREM 5: generator support is nonempty exactly when the recollection act
has recollectable potential. -/
theorem generatorNonempty_iff_recollectable
    (B : GeneratorTraceBridge State Observation GeneratorAtom ActAtom TraceAtom)
    (x : State) :
    (exists atom, B.generatorSupport x atom) <->
      RecollectableMemoryPotential B.loop.act x := by
  exact B.iso.pointwiseNonemptyEquivalent x

/-- THEOREM 6: generator silence is exactly recollection-act silence. -/
theorem generatorSilent_iff_recollectionSilent
    (B : GeneratorTraceBridge State Observation GeneratorAtom ActAtom TraceAtom)
    (x : State) :
    SupportSilentAt B.generatorSupport x <->
      SupportSilentAt B.loop.act.fires x := by
  exact B.iso.silent_iff x

/-- THEOREM 7: both sides inherit greatest silent domains from the same support
isomorphism shape. -/
theorem greatestSilentDomains
    (B : GeneratorTraceBridge State Observation GeneratorAtom ActAtom TraceAtom) :
    IsGreatestSupportSilentDomain B.generatorSupport
        (SupportSilentAt B.generatorSupport) /\
      IsGreatestSupportSilentDomain B.loop.act.fires
        (SupportSilentAt B.loop.act.fires) := by
  exact ⟨supportSilentStates_greatest B.generatorSupport,
    supportSilentStates_greatest B.loop.act.fires⟩

/-- THEOREM 8: any generator-side presentation transports to a
recollection-act presentation. -/
def transportGeneratorPresentationToRecollection
    (B : GeneratorTraceBridge State Observation GeneratorAtom ActAtom TraceAtom)
    (pres : SupportPresentation B.generatorSupport O) :
    SupportPresentation B.loop.act.fires O :=
  B.iso.transportRightPresentation pres

/-- THEOREM 9: a firing generator installs future trace through the
recollection loop. -/
theorem generator_installs_future_trace
    (B : GeneratorTraceBridge State Observation GeneratorAtom ActAtom TraceAtom)
    (x : State) (atom : GeneratorAtom)
    (hgen : B.generatorSupport x atom) :
    TracePotential B.loop (B.loop.query.write x) := by
  have hfire : B.loop.act.fires x (B.iso.atomEquiv atom) :=
    (B.iso.support_iff x atom).mp hgen
  exact RecollectionTraceLoop.firing_creates_future_trace_potential
    B.loop x (B.iso.atomEquiv atom) hfire

end GeneratorTraceBridge

/-! ## Instantiation: the Proposition 53 graph generator bridge -/

/-- The Proposition 53 graph-generator/recollection witness as an instance of
the abstract bridge. -/
def twoPointGraphGeneratorTraceBridge :
    GeneratorTraceBridge TwoPointTraceState TwoPointObservation
      GraphBoundaryAtom IndependentRecollectionAtom IndependentTraceAtom where
  loop := twoPointRecollectionTraceLoop
  generatorSupport := twoPointGraphBoundarySupport
  iso := twoPointGraphGeneratorRecollectionIso

/-- THEOREM 10: the abstract bridge recovers the Proposition 53 pointwise
generator/recollection equivalence. -/
theorem twoPointBridge_generatorNonempty_iff_recollectable
    (x : TwoPointTraceState) :
    (exists atom, twoPointGraphBoundarySupport x atom) <->
      RecollectableMemoryPotential twoPointRecollectionTraceLoop.act x := by
  exact GeneratorTraceBridge.generatorNonempty_iff_recollectable
    twoPointGraphGeneratorTraceBridge x

/-- THEOREM 11: the abstract bridge recovers the Proposition 53 trace
installation theorem. -/
theorem twoPointBridge_generator_installs_future_trace
    (x : TwoPointTraceState) (atom : GraphBoundaryAtom)
    (hgen : twoPointGraphBoundarySupport x atom) :
    TracePotential twoPointRecollectionTraceLoop
      (twoPointRecollectionTraceLoop.query.write x) := by
  exact GeneratorTraceBridge.generator_installs_future_trace
    twoPointGraphGeneratorTraceBridge x atom hgen

/-!
  Summary:
  - `GeneratorTraceBridge` is the abstract structure behind Proposition 53:
    an obstruction-generator support language plus a recollection trace loop,
    connected by strong support isomorphism.
  - The bridge simultaneously yields nonempty-support equivalence, silent
    domain maximality on both sides, presentation transport/uniqueness, and
    future-trace installation.
  - `twoPointGraphGeneratorTraceBridge` instantiates this theorem for the
    graph cross-critical-pair generator from Proposition 53.
-/
