/-
  Proposition 8 (algebraic core, real-part only): reflection conserves claim
  discipline.

  Proposition 8's third step originally claimed: a reflection (meta-layer
  Datalog read as object-layer fact) conserves claim identity + authority +
  source iff it is (i) authority-non-increasing (monotone w.r.t. ≤,
  specifically f a ≤ a), (ii) source-handle-injective (preserves reopen paths).

  The source half has a navigation-only wrinkle.  Injectivity is not necessary
  to preserve "has some source" discipline: every function maps a non-empty
  source set to a non-empty image.  Injectivity is exactly the stronger
  navigation-path-fidelity condition: distinct reopen paths remain distinct.

  This file proves the algebraic core generically:
    1. If f is non-increasing (f a ≤ a), then f preserves authority ceilings.
    2. Any f preserves non-emptiness of source sets.
    3. Non-increasing ⟹ discipline conserved for fact-level discipline.
    4. Source injectivity is necessary and sufficient for path fidelity.

  The virtual-part (training/weight update) and runtime claims are NOT proven
  here — they are engineering assertions with a different epistemic level.
-/

import Mathlib

/-! ## Authority conservation: non-increasing functions preserve ceilings -/

/-- A function is authority-non-increasing: f(a) ≤ a for all a.
    In the reflection: reading a meta-claim as object-layer doesn't raise its
    authority level. -/
def NonIncreasing (f : ℕ → ℕ) : Prop := ∀ a, f a ≤ a

/-- THEOREM 1: non-increasing ⟹ authority ≤ ceiling preserved.
    If f a ≤ a and a ≤ ceiling, then f a ≤ ceiling. -/
theorem authority_conserved {f : ℕ → ℕ} (hf : NonIncreasing f)
    (a ceiling : ℕ) (h_ceil : a ≤ ceiling) : f a ≤ ceiling :=
  (hf a).trans h_ceil

/-! ## Source conservation vs navigation path fidelity -/

/-- A function on source-handle sets is injective.
    Reflection preserves distinct reopen paths. -/
def SourceInjective {α : Type*} (f : α → α) : Prop := Function.Injective f

/-- THEOREM 2a: every source map preserves non-emptiness of source sets.

    This is the fact-layer correction: non-empty source support does not need
    source injectivity.  A non-injective reflection may still preserve the
    discipline predicate "there exists some source". -/
theorem source_nonempty_preserved_any {α : Type*} (f : α → α)
    (s : Set α) (hs : s.Nonempty) : (f '' s).Nonempty := by
  rcases hs with ⟨x, hx⟩
  exact ⟨f x, ⟨x, hx, rfl⟩⟩

/-- THEOREM 2b: injective ⟹ non-empty source stays non-empty after reflection.

    This old sufficient theorem remains true, but injectivity is stronger than
    needed for non-emptiness. -/
theorem source_nonempty_preserved {α : Type*} (f : α → α) (_hf : SourceInjective f)
    (s : Set α) (hs : s.Nonempty) : (f '' s).Nonempty := by
  exact source_nonempty_preserved_any f s hs

/-- A source map is path-faithful when equal reflected handles imply equal
    original handles.  This is the navigation-only strengthening that prevents
    two distinct reopen paths from collapsing into one. -/
def SourcePathFaithful {α : Type*} (f : α → α) : Prop :=
  ∀ {x y : α}, f x = f y → x = y

/-- THEOREM 2c: path fidelity is exactly source injectivity. -/
theorem source_path_faithful_iff_injective {α : Type*} (f : α → α) :
    SourcePathFaithful f ↔ SourceInjective f := by
  rfl

/-- A source map collapses distinct reopen paths when two different handles are
    reflected to the same handle. -/
def CollapsesDistinctSources {α : Type*} (f : α → α) : Prop :=
  ∃ x y : α, x ≠ y ∧ f x = f y

/-- THEOREM 2d: non-injectivity is exactly existence of a distinct-source
    collapse. -/
theorem not_injective_iff_collapses_distinct_sources {α : Type*} (f : α → α) :
    ¬ SourceInjective f ↔ CollapsesDistinctSources f := by
  constructor
  · intro hnot
    classical
    rw [SourceInjective, Function.Injective] at hnot
    push Not at hnot
    rcases hnot with ⟨x, y, hxy, hne⟩
    exact ⟨x, y, hne, hxy⟩
  · intro hcollapse hinj
    rcases hcollapse with ⟨x, y, hne, heq⟩
    exact hne (hinj heq)

/-- A concrete witness that non-empty source conservation does not imply
    source injectivity: the constant map on `Bool` collapses both handles but
    still maps every non-empty source set to a non-empty image. -/
theorem nonempty_conservation_does_not_imply_source_injective :
    ∃ f : Bool → Bool,
      ¬ SourceInjective f ∧
      ∀ s : Set Bool, s.Nonempty → (f '' s).Nonempty := by
  refine ⟨(fun _ => false), ?_, ?_⟩
  · intro hinj
    have hcollapse : (fun _ : Bool => false) true = (fun _ : Bool => false) false := rfl
    have htf : true = false := hinj hcollapse
    cases htf
  · intro s hs
    exact source_nonempty_preserved_any (fun _ : Bool => false) s hs

/-! ## Combined: reflection conserves discipline -/

/-- A claim's conservation bundle: authority level + source-set non-emptiness.
    (The "typed package" from Definition 10.) -/
structure ClaimBundle (α : Type*) where
  authority : ℕ
  source : Set α
  hasSource : Bool

/-- The discipline predicate on a bundle: authority ≤ ceiling AND has source. -/
def disciplined {α : Type*} (b : ClaimBundle α) (ceiling : ℕ) : Prop :=
  b.authority ≤ ceiling ∧ b.hasSource = true

/-- A stronger fact-level discipline predicate that checks the actual source
    set as well as the cached `hasSource` flag.  Even this stronger non-empty
    source condition does not require injectivity. -/
def disciplinedWithSourceSet {α : Type*} (b : ClaimBundle α) (ceiling : ℕ) : Prop :=
  b.authority ≤ ceiling ∧ b.hasSource = true ∧ b.source.Nonempty

/-- A reflection maps bundles to bundles, acting on authority and source. -/
def reflect {α : Type*} (auth_f : ℕ → ℕ) (src_f : α → α)
    (b : ClaimBundle α) : ClaimBundle α :=
  { authority := auth_f b.authority
    source := src_f '' b.source
    hasSource := b.hasSource }  -- hasSource flag preserved (it's a fact about source)

/-- THEOREM 3 (MAIN): if auth_f is non-increasing and src_f is injective,
    then reflection preserves discipline.

    This is the algebraic core of Proposition 8 step 3:
    "reflection conserves ⟺ non-increasing + injective".
    Here we prove the SUFFICIENT direction (non-increasing + injective ⟹
    conserved). The necessary direction (conserved ⟹ non-increasing + injective)
    follows by contrapositive but is deferred. -/
theorem reflect_preserves_discipline {α : Type*}
    (auth_f : ℕ → ℕ) (src_f : α → α)
    (h_auth : NonIncreasing auth_f)
    (_h_inj : SourceInjective src_f)
    (b : ClaimBundle α) (ceiling : ℕ)
    (h : disciplined b ceiling) : disciplined (reflect auth_f src_f b) ceiling := by
  refine ⟨?_, ?_⟩
  · -- authority: auth_f(b.authority) ≤ b.authority ≤ ceiling
    exact authority_conserved h_auth b.authority ceiling h.1
  · -- hasSource: preserved by reflect (field unchanged)
    exact h.2

/-- THEOREM 3b: fact-level discipline conservation does not require source
    injectivity.  This is the corrected sufficient theorem for the predicate
    actually defined above. -/
theorem reflect_preserves_discipline_without_source_injective {α : Type*}
    (auth_f : ℕ → ℕ) (src_f : α → α)
    (h_auth : NonIncreasing auth_f)
    (b : ClaimBundle α) (ceiling : ℕ)
    (h : disciplined b ceiling) : disciplined (reflect auth_f src_f b) ceiling := by
  refine ⟨?_, ?_⟩
  · exact authority_conserved h_auth b.authority ceiling h.1
  · exact h.2

/-- THEOREM 3c: even when the discipline predicate checks the actual source set,
    source injectivity is still not needed; arbitrary source maps preserve
    non-empty images. -/
theorem reflect_preserves_source_set_discipline_without_source_injective {α : Type*}
    (auth_f : ℕ → ℕ) (src_f : α → α)
    (h_auth : NonIncreasing auth_f)
    (b : ClaimBundle α) (ceiling : ℕ)
    (h : disciplinedWithSourceSet b ceiling) :
    disciplinedWithSourceSet (reflect auth_f src_f b) ceiling := by
  refine ⟨?_, ?_, ?_⟩
  · exact authority_conserved h_auth b.authority ceiling h.1
  · exact h.2.1
  · exact source_nonempty_preserved_any src_f b.source h.2.2

/-! ## Necessity: authority yes, path fidelity yes, non-empty source no -/

/-- THEOREM 4 (NECESSITY, authority): if reflect always conserves authority
    discipline, then auth_f must be non-increasing.

    Contrapositive: if auth_f increases at some point (f a > a), then reflecting
    a bundle with authority=a and ceiling=a violates discipline. -/
theorem reflect_necessity_authority {α : Type*}
    (auth_f : ℕ → ℕ) (src_f : α → α)
    (h_conserve : ∀ (b : ClaimBundle α) (ceiling : ℕ),
      disciplined b ceiling → disciplined (reflect auth_f src_f b) ceiling)
    : NonIncreasing auth_f := by
  intro a
  by_contra h_gt
  -- h_gt : ¬ (auth_f a ≤ a), i.e. a < auth_f a
  have ha : a < auth_f a := (not_le.mp h_gt)
  -- Construct bundle with authority = a, ceiling = a
  let b : ClaimBundle α := { authority := a, source := ∅, hasSource := true }
  have hb : disciplined b a := ⟨le_refl a, rfl⟩
  have h_ref : disciplined (reflect auth_f src_f b) a := h_conserve b a hb
  -- h_ref.1 : auth_f a ≤ a, contradicting a < auth_f a
  exact absurd ha (not_lt.mpr h_ref.1)

/-- THEOREM 5: source injectivity is necessary for preserving distinct reopen
    paths.  This is just the necessary direction of path fidelity; it is the
    navigation-only property that was hidden by the weaker fact-level
    `hasSource` predicate. -/
theorem source_injective_necessary_for_path_fidelity {α : Type*}
    (f : α → α) (h : SourcePathFaithful f) : SourceInjective f := by
  intro x y hxy
  exact h hxy

/-- THEOREM 6: source injectivity is sufficient for preserving distinct reopen
    paths. -/
theorem source_injective_sufficient_for_path_fidelity {α : Type*}
    (f : α → α) (h : SourceInjective f) : SourcePathFaithful f := by
  intro x y hxy
  exact h hxy

/-- THEOREM 7: discipline can be conserved while navigation paths collapse.

    This is the navigation-only separation example.  The constant reflection on
    `Bool` preserves authority and non-empty source support for a sourced
    bundle, but it collapses the two distinct source handles `true` and `false`.
    So "discipline conserved" is strictly weaker than "route/source path
    faithful". -/
theorem discipline_can_hold_while_navigation_paths_collapse :
    ∃ (src_f : Bool → Bool) (b : ClaimBundle Bool),
      disciplinedWithSourceSet b 0 ∧
      disciplinedWithSourceSet (reflect (fun a => a) src_f b) 0 ∧
      CollapsesDistinctSources src_f := by
  let src_f : Bool → Bool := fun _ => false
  let b : ClaimBundle Bool := { authority := 0, source := Set.univ, hasSource := true }
  refine ⟨src_f, b, ?_, ?_, ?_⟩
  · refine ⟨le_rfl, rfl, ?_⟩
    exact ⟨true, Set.mem_univ true⟩
  · exact reflect_preserves_source_set_discipline_without_source_injective
      (fun a => a) src_f (by intro a; exact le_rfl) b 0
      ⟨le_rfl, rfl, ⟨true, Set.mem_univ true⟩⟩
  · refine ⟨true, false, ?_, rfl⟩
    intro h
    cases h

/-!
  Summary (all proven, zero sorry):
  - authority_conserved: non-increasing f ⟹ f a ≤ ceiling when a ≤ ceiling
  - source_nonempty_preserved_any: every f preserves non-empty source images
  - source_nonempty_preserved: injective f ⟹ non-empty source stays non-empty
    remains true, but is over-strong
  - nonempty_conservation_does_not_imply_source_injective: source injectivity
    is not necessary for fact-level source non-emptiness
  - reflect_preserves_discipline: non-increasing + injective ⟹ discipline conserved (sufficient)
  - reflect_preserves_discipline_without_source_injective: injectivity is not
    needed for the stated fact-level discipline predicate
  - reflect_preserves_source_set_discipline_without_source_injective: even
    actual non-empty source-set discipline does not need injectivity
  - reflect_necessity_authority: conserved ⟹ non-increasing (necessary, authority half)
  - source_path_faithful_iff_injective: injectivity is exactly the stronger
    path-fidelity condition needed for navigation route preservation
  - discipline_can_hold_while_navigation_paths_collapse: there is a concrete
    reflection that preserves fact-level discipline while collapsing source
    paths

  Together: authority-non-increasing is NECESSARY AND SUFFICIENT for authority
  conservation under reflection. Source-injective is NOT necessary for
  fact-level source conservation; it is necessary and sufficient for preserving
  distinct source paths.  Thus a non-injective reflection can conserve
  discipline while still degrading navigation by collapsing reopen routes.

  This is the algebraic core of Proposition 8 step 3 (real-part / Datalog
  self-description). The virtual-part (training/weight update, step 4) is
  NOT proven — it's an engineering assertion at a different epistemic level.
-/
