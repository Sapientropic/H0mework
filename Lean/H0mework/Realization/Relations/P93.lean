/-
  Proposition 93: concrete finite semantic-assignment P92 certificate.

  Proposition 92 gave the runtime-facing certificate shape for an exhaustive
  finite support table.  This file instantiates that shape for the declared
  seven lower semantic atoms themselves: a state is a Boolean assignment to the
  seven obligations, memory atoms are the same primitive semantic atoms, and a
  memory atom is produced exactly when its obligation fails.

  This closes the Lean side of the current finite semantic-product slice.  The
  runtime still has to justify that an arbitrary production state projects into
  this declared semantic slice; but the `2^7` slice itself is now a checked Lean
  object, not only a Python report.
-/

import H0mework.Realization.QuerySupport.P92

/-! ## A concrete 2^7 semantic assignment state space -/

/-- A Boolean state for the seven lower semantic obligations. -/
structure SemanticBoolState where
  sourceReachability : Bool
  authorityMonotonicity : Bool
  graphConfluence : Bool
  gaugeInvariance : Bool
  contractionCertification : Bool
  omegaGluing : Bool
  freshnessValidity : Bool
  deriving DecidableEq, Repr

/-- Interpret a `SemanticBoolState` as the seven `C_safe` predicates. -/
def semanticBoolPredicates : CSafePredicates SemanticBoolState where
  sourceBacked := fun x => x.sourceReachability = true
  authoritySafe := fun x => x.authorityMonotonicity = true
  graphConfluent := fun x => x.graphConfluence = true
  gaugeNonleaking := fun x => x.gaugeInvariance = true
  contractionSafe := fun x => x.contractionCertification = true
  omegaConsistent := fun x => x.omegaGluing = true
  freshnessSafe := fun x => x.freshnessValidity = true

/-- Read one lower semantic atom from a Boolean state. -/
def semanticBoolValue (x : SemanticBoolState) : SemanticAtom → Bool
  | SemanticAtom.sourceReachability => x.sourceReachability
  | SemanticAtom.authorityMonotonicity => x.authorityMonotonicity
  | SemanticAtom.graphConfluence => x.graphConfluence
  | SemanticAtom.gaugeInvariance => x.gaugeInvariance
  | SemanticAtom.contractionCertification => x.contractionCertification
  | SemanticAtom.omegaGluing => x.omegaGluing
  | SemanticAtom.freshnessValidity => x.freshnessValidity

/-- THEOREM 1: the Boolean reader agrees with the lower obligation semantics. -/
theorem semanticBoolHolds_iff_value
    (x : SemanticBoolState) (a : SemanticAtom) :
    (semanticObligationSemantics semanticBoolPredicates).holds a x <->
      semanticBoolValue x a = true := by
  cases a <;> rfl

/-- A Boolean cannot be true exactly when it is false.  Keeping this tiny
lemma explicit makes the concrete semantic-product proof independent of
whether `simp` unfolds the lower obligation semantics aggressively enough. -/
theorem bool_not_true_iff_false (b : Bool) :
    (b = true -> False) <-> b = false := by
  cases b <;> simp

/-- THEOREM 2: primitive semantic failure is exactly a false Boolean value in
the concrete semantic-product slice. -/
theorem semanticBoolFailure_iff_value_false
    (x : SemanticBoolState) (a : SemanticAtom) :
    AtomFailure (semanticObligationSemantics semanticBoolPredicates) x a <->
      semanticBoolValue x a = false := by
  cases x with
  | mk source authority graph gauge contraction omega freshness =>
      cases a with
      | sourceReachability =>
          change (source = true -> False) <-> source = false
          exact bool_not_true_iff_false source
      | authorityMonotonicity =>
          change (authority = true -> False) <-> authority = false
          exact bool_not_true_iff_false authority
      | graphConfluence =>
          change (graph = true -> False) <-> graph = false
          exact bool_not_true_iff_false graph
      | gaugeInvariance =>
          change (gauge = true -> False) <-> gauge = false
          exact bool_not_true_iff_false gauge
      | contractionCertification =>
          change (contraction = true -> False) <-> contraction = false
          exact bool_not_true_iff_false contraction
      | omegaGluing =>
          change (omega = true -> False) <-> omega = false
          exact bool_not_true_iff_false omega
      | freshnessValidity =>
          change (freshness = true -> False) <-> freshness = false
          exact bool_not_true_iff_false freshness

/-- A raw memory atom for this slice: one support atom per primitive semantic
failure atom. -/
abbrev SemanticBoolMemoryAtom := SemanticAtom

/-- Memory production is primitive failure support. -/
noncomputable def semanticBoolMemoryContract :
    MemoryProductionContract SemanticBoolState SemanticBoolMemoryAtom where
  produces := fun x a =>
    semanticBoolValue x a = false
  memorySilent := fun x =>
    forall a, semanticBoolValue x a = false -> False
  product_shape := by
    intro x
    rfl
  independent := by
    classical
    intro assignment
    let x : SemanticBoolState :=
      { sourceReachability :=
          if assignment SemanticAtom.sourceReachability then false else true
        authorityMonotonicity :=
          if assignment SemanticAtom.authorityMonotonicity then false else true
        graphConfluence :=
          if assignment SemanticAtom.graphConfluence then false else true
        gaugeInvariance :=
          if assignment SemanticAtom.gaugeInvariance then false else true
        contractionCertification :=
          if assignment SemanticAtom.contractionCertification then false else true
        omegaGluing :=
          if assignment SemanticAtom.omegaGluing then false else true
        freshnessValidity :=
          if assignment SemanticAtom.freshnessValidity then false else true }
    refine ⟨x, ?_⟩
    intro m
    cases m with
    | sourceReachability =>
        by_cases h : assignment SemanticAtom.sourceReachability <;>
          simp [x, semanticBoolValue, h]
    | authorityMonotonicity =>
        by_cases h : assignment SemanticAtom.authorityMonotonicity <;>
          simp [x, semanticBoolValue, h]
    | graphConfluence =>
        by_cases h : assignment SemanticAtom.graphConfluence <;>
          simp [x, semanticBoolValue, h]
    | gaugeInvariance =>
        by_cases h : assignment SemanticAtom.gaugeInvariance <;>
          simp [x, semanticBoolValue, h]
    | contractionCertification =>
        by_cases h : assignment SemanticAtom.contractionCertification <;>
          simp [x, semanticBoolValue, h]
    | omegaGluing =>
        by_cases h : assignment SemanticAtom.omegaGluing <;>
          simp [x, semanticBoolValue, h]
    | freshnessValidity =>
        by_cases h : assignment SemanticAtom.freshnessValidity <;>
          simp [x, semanticBoolValue, h]

/-! ## Exhaustive finite universes -/

def boolUniverse : List Bool := [false, true]

def semanticBoolStateUniverse : List SemanticBoolState :=
  List.flatMap (fun source =>
  List.flatMap (fun authority =>
  List.flatMap (fun graph =>
  List.flatMap (fun gauge =>
  List.flatMap (fun contraction =>
  List.flatMap (fun omega =>
  List.map (fun freshness =>
    { sourceReachability := source
      authorityMonotonicity := authority
      graphConfluence := graph
      gaugeInvariance := gauge
      contractionCertification := contraction
      omegaGluing := omega
      freshnessValidity := freshness }) boolUniverse)
    boolUniverse) boolUniverse) boolUniverse) boolUniverse) boolUniverse) boolUniverse

/-- THEOREM 2: the Boolean universe contains every Boolean value. -/
theorem bool_mem_universe (b : Bool) : b ∈ boolUniverse := by
  cases b <;> simp [boolUniverse]

/-- THEOREM 3: the 2^7 semantic Boolean universe is exhaustive. -/
theorem semanticBoolState_mem_universe (x : SemanticBoolState) :
    x ∈ semanticBoolStateUniverse := by
  cases x with
  | mk source authority graph gauge contraction omega freshness =>
      unfold semanticBoolStateUniverse
      apply List.mem_flatMap.mpr
      refine ⟨source, bool_mem_universe source, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨authority, bool_mem_universe authority, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨graph, bool_mem_universe graph, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨gauge, bool_mem_universe gauge, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨contraction, bool_mem_universe contraction, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨omega, bool_mem_universe omega, ?_⟩
      apply List.mem_map.mpr
      exact ⟨freshness, bool_mem_universe freshness, rfl⟩

/-- Runtime rows for the concrete finite support table: each memory atom
represents the matching primitive semantic atom. -/
def semanticBoolSupportRows : List (SemanticBoolMemoryAtom × SemanticAtom) :=
  semanticAtomUniverse.map fun a => (a, a)

/-- THEOREM 4: every concrete memory atom is covered by a table row. -/
theorem semanticBoolMemoryRows_cover
    (m : SemanticBoolMemoryAtom) :
    ∃ a, (m, a) ∈ semanticBoolSupportRows := by
  refine ⟨m, ?_⟩
  simp [semanticBoolSupportRows, semanticAtom_mem_universe m]

/-- THEOREM 5: every lower semantic atom has a concrete memory representative. -/
theorem semanticBoolSemanticRows_cover
    (a : SemanticAtom) :
    ∃ m, (m, a) ∈ semanticBoolSupportRows := by
  refine ⟨a, ?_⟩
  simp [semanticBoolSupportRows, semanticAtom_mem_universe a]

/-- THEOREM 6: rows in the concrete table are diagonal. -/
theorem semanticBoolSupportRows_mem_eq
    {m : SemanticBoolMemoryAtom} {a : SemanticAtom}
    (h : (m, a) ∈ semanticBoolSupportRows) :
    m = a := by
  rcases List.mem_map.mp h with ⟨b, hb, hpair⟩
  have hm : b = m := congrArg Prod.fst hpair
  have ha : b = a := congrArg Prod.snd hpair
  exact hm.symm.trans ha

/-! ## P92 certificate instance -/

/-- THEOREM 7: the concrete semantic-product slice emits a P92 decided finite
support certificate. -/
noncomputable def semanticBoolP92Certificate :
    DecidedFiniteRawAtomicSupportDiscoveryCheck
      semanticBoolPredicates semanticBoolMemoryContract where
  states := semanticBoolStateUniverse
  memoryAtoms := semanticAtomUniverse
  rows := semanticBoolSupportRows
  state_total := semanticBoolState_mem_universe
  memory_total := semanticAtom_mem_universe
  row_support_decidable := by
    intro m a x
    classical
    exact Classical.propDecidable _
  row_support_decided := by
    intro m a hrow x _hx
    classical
    have hma : m = a := semanticBoolSupportRows_mem_eq hrow
    have hp :
        semanticBoolMemoryContract.produces x m <->
          BoolQuery.eval (semanticObligationSemantics semanticBoolPredicates)
            (singletonFailureQuery a) x := by
      rw [hma]
      calc
        semanticBoolMemoryContract.produces x a <->
            semanticBoolValue x a = false := Iff.rfl
        _ <-> AtomFailure (semanticObligationSemantics semanticBoolPredicates) x a :=
            (semanticBoolFailure_iff_value_false x a).symm
        _ <-> BoolQuery.eval (semanticObligationSemantics semanticBoolPredicates)
              (singletonFailureQuery a) x :=
            (singletonFailureQuery_eval_iff semanticBoolPredicates a x).symm
    exact @decide_eq_true
      (semanticBoolMemoryContract.produces x m <->
        BoolQuery.eval (semanticObligationSemantics semanticBoolPredicates)
          (singletonFailureQuery a) x)
      (Classical.propDecidable _)
      hp
  memory_rows_cover := by
    intro m _hm
    exact semanticBoolMemoryRows_cover m
  semantic_rows_cover := by
    intro a _ha
    exact semanticBoolSemanticRows_cover a

/-- THEOREM 8: the concrete P92 certificate reconstructs the P91 finite check. -/
noncomputable def semanticBoolFiniteSupportCheck :
    FiniteRawAtomicSupportDiscoveryCheck
      semanticBoolPredicates semanticBoolMemoryContract :=
  semanticBoolP92Certificate.toFiniteRawAtomicSupportDiscoveryCheck

/-- THEOREM 9: the concrete P92 certificate reconstructs the P90 table. -/
noncomputable def semanticBoolSupportDiscoveryTable :
    RawAtomicSupportDiscoveryTable
      semanticBoolPredicates semanticBoolMemoryContract :=
  semanticBoolP92Certificate.toRawAtomicSupportDiscoveryTable

/-!
  Summary:
  - The declared seven-atom semantic assignment product is now a concrete
    finite Lean state space.
  - The P92 support certificate is instantiated for that state space with
    memory atoms equal to primitive semantic failure atoms.
  - Runtime mechanism-faithfulness still has to project real production states
    into this semantic slice; this file only closes the finite slice itself.
-/
