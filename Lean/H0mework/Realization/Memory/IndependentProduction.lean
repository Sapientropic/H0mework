/-
  Proposition 40: independent memory-production contracts.

  Proposition 36 transported obstruction structure into the memory layer through
  the already-defined equivalence between `MemoryEpistemicType` and
  `SemanticAtom`.  That is useful, but it is still a transport theorem.

  This file adds the missing memory-side contract shape.  A memory production
  layer is specified independently by:

    * `produces : State -> MemoryAtom -> Prop`;
    * `memorySilent : State -> Prop`;
    * product shape: silence means no memory atom is produced;
    * memory-atom independence: any production truth assignment is realizable.

  If such an independently specified memory layer is then related to the
  obstruction layer by an equivalence certificate, the usual maximality,
  nonempty-production, and singleton/primitive-memory conclusions follow.

  This still does not prove the concrete runtime supplies the contract.  It
  states exactly the contract the runtime must instantiate to move beyond
  mere relabeling.
-/

import H0mework.Realization.Memory.SilentMaximality

/-! ## Independent memory-production side -/

/-- A memory production layer specified on its own terms. -/
structure MemoryProductionContract (State MemoryAtom : Type*) where
  produces : State -> MemoryAtom -> Prop
  memorySilent : State -> Prop
  product_shape :
    forall x, memorySilent x <->
      forall m, produces x m -> False
  independent :
    forall assignment : MemoryAtom -> Prop,
      exists x, forall m, produces x m <-> assignment m

/-- A state produces exactly one memory atom. -/
def SingletonMemoryProduction {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom)
    (x : State) (m : MemoryAtom) : Prop :=
  M.produces x m /\ forall m', M.produces x m' -> m' = m

/-- A memory atom is primitive when it can appear as the sole production. -/
def PrimitiveMemoryProduction {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) (m : MemoryAtom) : Prop :=
  exists x, SingletonMemoryProduction M x m

/-- THEOREM 1: product shape makes non-silence exactly nonempty production. -/
theorem memoryContract_production_nonempty_iff_not_silent
    {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) (x : State) :
    (exists m, M.produces x m) <-> (M.memorySilent x -> False) := by
  constructor
  · rintro ⟨m, hm⟩ hsilent
    exact ((M.product_shape x).mp hsilent m hm)
  · intro hnotSilent
    by_contra hnone
    have hnoProduction : forall m, M.produces x m -> False := by
      intro m hm
      exact hnone ⟨m, hm⟩
    exact hnotSilent ((M.product_shape x).mpr hnoProduction)

/-- THEOREM 2: memory-atom independence makes every memory atom primitive. -/
theorem primitiveMemoryProduction_of_independent {State MemoryAtom : Type*}
    [DecidableEq MemoryAtom]
    (M : MemoryProductionContract State MemoryAtom) :
    forall m, PrimitiveMemoryProduction M m := by
  intro m
  let assignment : MemoryAtom -> Prop := fun m' => m' = m
  rcases M.independent assignment with ⟨x, hx⟩
  refine ⟨x, ?_, ?_⟩
  · exact (hx m).mpr rfl
  · intro m' hm'
    exact (hx m').mp hm'

/-! ## Equivalence certificate to obstruction semantics -/

/-- An independently specified memory layer corresponds to the obstruction
layer when silence matches `C_safe` and each produced memory atom matches the
corresponding semantic obstruction atom. -/
structure MemoryObstructionEquivalence {State : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryEpistemicType) where
  silent_iff_csafe : forall x, M.memorySilent x <-> CSafe P x
  produces_iff_obstruction :
    forall x m, M.produces x m <->
      AtomFailure (semanticObligationSemantics P) x (memoryToSemanticAtom m)

/-- A domain is silent for an independently specified memory contract. -/
def MemoryContractSilentDomain {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom)
    (D : State -> Prop) : Prop :=
  forall x, D x -> M.memorySilent x

/-- Greatest silent-domain predicate for an independently specified memory
contract. -/
def IsGreatestMemoryContractSilentDomain {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom)
    (C : State -> Prop) : Prop :=
  MemoryContractSilentDomain M C /\
    forall D : State -> Prop, MemoryContractSilentDomain M D -> PredSubset D C

/-- THEOREM 3: under a memory-obstruction equivalence, memory production is
exactly canonical `MemoryProduction`. -/
theorem independentProduces_iff_canonicalMemoryProduction {State : Type*}
    {P : CSafePredicates State}
    {M : MemoryProductionContract State MemoryEpistemicType}
    (E : MemoryObstructionEquivalence P M)
    (x : State) (m : MemoryEpistemicType) :
    M.produces x m <-> MemoryProduction P x m := by
  exact E.produces_iff_obstruction x m

/-- THEOREM 4: under equivalence, nonempty independent memory production is
exactly `¬ C_safe`. -/
theorem independentMemoryProduction_nonempty_iff_not_csafe {State : Type*}
    {P : CSafePredicates State}
    {M : MemoryProductionContract State MemoryEpistemicType}
    (E : MemoryObstructionEquivalence P M) (x : State) :
    (exists m, M.produces x m) <-> (CSafe P x -> False) := by
  constructor
  · intro hprod hsafe
    have hsilent : M.memorySilent x := (E.silent_iff_csafe x).mpr hsafe
    exact (memoryContract_production_nonempty_iff_not_silent M x).mp hprod hsilent
  · intro hnotSafe
    exact (memoryContract_production_nonempty_iff_not_silent M x).mpr
      (fun hsilent => hnotSafe ((E.silent_iff_csafe x).mp hsilent))

/-- THEOREM 5: under equivalence, `C_safe` is the greatest domain that is
silent for the independently specified memory production layer. -/
theorem cSafe_greatest_independent_memory_silent_domain {State : Type*}
    {P : CSafePredicates State}
    {M : MemoryProductionContract State MemoryEpistemicType}
    (E : MemoryObstructionEquivalence P M) :
    IsGreatestMemoryContractSilentDomain M (CSafe P) := by
  constructor
  · intro x hx
    exact (E.silent_iff_csafe x).mpr hx
  · intro D hD x hx
    exact (E.silent_iff_csafe x).mp (hD x hx)

/-- THEOREM 6: the independent memory contract plus equivalence yields the
same final-mile structure as obstruction support, but now from the memory side:
nonempty production detects unsafety, `C_safe` is the greatest silent domain,
and every memory epistemic type is primitive. -/
theorem independent_memory_obstruction_correspondence {State : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryEpistemicType)
    (E : MemoryObstructionEquivalence P M) :
    (forall x, (exists m, M.produces x m) <-> (CSafe P x -> False)) /\
      IsGreatestMemoryContractSilentDomain M (CSafe P) /\
      (forall m, PrimitiveMemoryProduction M m) := by
  constructor
  · exact independentMemoryProduction_nonempty_iff_not_csafe E
  constructor
  · exact cSafe_greatest_independent_memory_silent_domain E
  · exact primitiveMemoryProduction_of_independent M

/-!
  Boundary:
  - This is stronger than Proposition 36's pure transport: memory production is
    introduced as an independent contract, then related to obstruction by an
    explicit equivalence certificate.
  - It is still conditional.  A concrete runtime must instantiate
    `MemoryProductionContract` and `MemoryObstructionEquivalence`; otherwise the
    theorem does not claim that memory ontology was independently discovered.
-/
