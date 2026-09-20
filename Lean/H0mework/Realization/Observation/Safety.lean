/-
  Proposition 10: C_safe closure, Lemma 3 sufficient domain, and reopen taxonomy.

  This file proves the next abstract acceptance slice after Proposition 9:

    * C_safe is closed under safety-preserving steps, and its morphisms close
      under identity and composition.
    * Lemma 3's Lyapunov/contraction certificate gives eventual observable
      bisimulation on its declared domain.
    * The complement of C_safe is exactly classified by a finite reopen
      taxonomy, and a C_safe-partial λ exposes that taxonomy as its obstruction.

  It does NOT prove that the concrete AIppocampus runtime produces these
  certificates.  That is the mechanism-faithfulness obligation.
-/

import H0mework.Realization.Observation.Cells
import H0mework.Realization.Reflexive.PartialLambda

open scoped BigOperators

/-! ## C_safe as a conjunction of auditable safety predicates -/

/-- The safety facets that jointly define the certified λ domain. -/
structure CSafePredicates (State : Type*) where
  sourceBacked : State → Prop
  authoritySafe : State → Prop
  graphConfluent : State → Prop
  gaugeNonleaking : State → Prop
  contractionSafe : State → Prop
  omegaConsistent : State → Prop
  freshnessSafe : State → Prop

/-- `C_safe`: all safety facets hold at once. -/
def CSafe {State : Type*} (P : CSafePredicates State) (x : State) : Prop :=
  P.sourceBacked x ∧
  P.authoritySafe x ∧
  P.graphConfluent x ∧
  P.gaugeNonleaking x ∧
  P.contractionSafe x ∧
  P.omegaConsistent x ∧
  P.freshnessSafe x

instance cSafeDecidable {State : Type*} (P : CSafePredicates State) (x : State)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)] : Decidable (CSafe P x) := by
  unfold CSafe
  infer_instance

/-- A step preserves one safety facet. -/
def Preserves {State : Type*} (step : State → State) (p : State → Prop) : Prop :=
  ∀ x, p x → p (step x)

/-- A runtime step is safe when it preserves every facet of `C_safe`. -/
structure CSafeStep {State : Type*} (P : CSafePredicates State)
    (step : State → State) where
  sourceBacked : Preserves step P.sourceBacked
  authoritySafe : Preserves step P.authoritySafe
  graphConfluent : Preserves step P.graphConfluent
  gaugeNonleaking : Preserves step P.gaugeNonleaking
  contractionSafe : Preserves step P.contractionSafe
  omegaConsistent : Preserves step P.omegaConsistent
  freshnessSafe : Preserves step P.freshnessSafe

/-- THEOREM 1: `C_safe` is closed under any step that preserves all facets. -/
theorem cSafe_closed_under_safe_step {State : Type*}
    (P : CSafePredicates State) (step : State → State)
    (hstep : CSafeStep P step) :
    Preserves step (CSafe P) := by
  intro x hx
  exact ⟨
    hstep.sourceBacked x hx.1,
    hstep.authoritySafe x hx.2.1,
    hstep.graphConfluent x hx.2.2.1,
    hstep.gaugeNonleaking x hx.2.2.2.1,
    hstep.contractionSafe x hx.2.2.2.2.1,
    hstep.omegaConsistent x hx.2.2.2.2.2.1,
    hstep.freshnessSafe x hx.2.2.2.2.2.2
  ⟩

/-- Safety-preserving maps are the morphisms of the certified safe subcategory. -/
def SafeMorphism {State : Type*} (P : CSafePredicates State)
    (f : State → State) : Prop :=
  ∀ ⦃x⦄, CSafe P x → CSafe P (f x)

/-- THEOREM 2: identity is a safe morphism. -/
theorem safeMorphism_id {State : Type*} (P : CSafePredicates State) :
    SafeMorphism P id := by
  intro x hx
  exact hx

/-- THEOREM 3: safe morphisms compose. -/
theorem safeMorphism_comp {State : Type*} (P : CSafePredicates State)
    {f g : State → State}
    (hf : SafeMorphism P f) (hg : SafeMorphism P g) :
    SafeMorphism P (fun x => g (f x)) := by
  intro x hx
  exact hg (hf hx)

/-- THEOREM 4: repeated safe steps stay in `C_safe`. -/
theorem cSafe_closed_under_safe_step_iterate {State : Type*}
    (P : CSafePredicates State) (step : State → State)
    (hstep : CSafeStep P step) :
    ∀ n x, CSafe P x → CSafe P ((step^[n]) x) := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa using hx
  | succ n ih =>
      intro x hx
      have hn : CSafe P ((step^[n]) x) := ih x hx
      have hclosed := cSafe_closed_under_safe_step P step hstep ((step^[n]) x) hn
      simpa [Function.iterate_succ_apply'] using hclosed

/-! ## Lemma 3 as a sufficient observable-bisimulation domain -/

/-- Eventual equality of observations under a shared future dynamics. -/
def ObservableBisimilarEventually {X Y : Type*} (T : X → X)
    (obs : X → Y) (x y : X) : Prop :=
  ∃ N, ∀ n, N ≤ n → obs ((T^[n]) x) = obs ((T^[n]) y)

/-- A declared domain on which the Lyapunov/contraction hypotheses of Lemma 3
    are sufficient for eventual observable bisimulation. -/
structure ObservableContractionDomain (X Y : Type*) where
  V : X → X → ℝ
  T : X → X
  obs : X → Y
  inDomain : X → Prop
  r : ℝ
  eps : ℝ
  z : X
  r_nonneg : 0 ≤ r
  contract : LyapunovContraction V T r
  fixed : T z = z
  obs_margin : ∀ a : X, V a z < eps → obs a = obs z
  tail : ∀ x : X, inDomain x → ∃ N, ∀ n, N ≤ n → r ^ n * V x z < eps

/-- THEOREM 5: Lemma 3 gives observable bisimulation on the declared
    Lyapunov/contraction domain. -/
theorem lemma3_domain_gives_observable_bisimulation {X Y : Type*}
    (D : ObservableContractionDomain X Y)
    {x y : X} (hx : D.inDomain x) (hy : D.inDomain y) :
    ObservableBisimilarEventually D.T D.obs x y := by
  exact eventual_obs_eq_of_lyapunov_margin
    D.r_nonneg D.contract D.fixed D.obs_margin
    (D.tail x hx) (D.tail y hy)

/-! ## Reopen taxonomy as the exact complement classifier of C_safe -/

/-- The finite reopen taxonomy for leaving `C_safe`. -/
inductive ReopenTaxonomy where
  | sourceMissing
  | authorityOverreach
  | graphNonconfluent
  | gaugeLeak
  | contractionUncertified
  | omegaConflict
  | freshnessStale
  deriving DecidableEq, Repr

/-- A taxonomy case is a witness for the corresponding failed safety facet. -/
def taxonomyWitness {State : Type*} (P : CSafePredicates State) (x : State) :
    ReopenTaxonomy → Prop
  | ReopenTaxonomy.sourceMissing => ¬ P.sourceBacked x
  | ReopenTaxonomy.authorityOverreach => ¬ P.authoritySafe x
  | ReopenTaxonomy.graphNonconfluent => ¬ P.graphConfluent x
  | ReopenTaxonomy.gaugeLeak => ¬ P.gaugeNonleaking x
  | ReopenTaxonomy.contractionUncertified => ¬ P.contractionSafe x
  | ReopenTaxonomy.omegaConflict => ¬ P.omegaConsistent x
  | ReopenTaxonomy.freshnessStale => ¬ P.freshnessSafe x

/-- A deterministic classifier that returns the first failed reopen cause. -/
def classifyUnsafe {State : Type*} (P : CSafePredicates State) (x : State)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)] : Option ReopenTaxonomy :=
  if P.sourceBacked x then
    if P.authoritySafe x then
      if P.graphConfluent x then
        if P.gaugeNonleaking x then
          if P.contractionSafe x then
            if P.omegaConsistent x then
              if P.freshnessSafe x then
                none
              else
                some ReopenTaxonomy.freshnessStale
            else
              some ReopenTaxonomy.omegaConflict
          else
            some ReopenTaxonomy.contractionUncertified
        else
          some ReopenTaxonomy.gaugeLeak
      else
        some ReopenTaxonomy.graphNonconfluent
    else
      some ReopenTaxonomy.authorityOverreach
  else
    some ReopenTaxonomy.sourceMissing

/-- THEOREM 6: the classifier returns `none` exactly on `C_safe`. -/
theorem classifyUnsafe_none_iff_csafe {State : Type*}
    (P : CSafePredicates State) (x : State)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)] :
    classifyUnsafe P x = none ↔ CSafe P x := by
  by_cases h1 : P.sourceBacked x <;>
  by_cases h2 : P.authoritySafe x <;>
  by_cases h3 : P.graphConfluent x <;>
  by_cases h4 : P.gaugeNonleaking x <;>
  by_cases h5 : P.contractionSafe x <;>
  by_cases h6 : P.omegaConsistent x <;>
  by_cases h7 : P.freshnessSafe x <;>
  simp [classifyUnsafe, CSafe, h1, h2, h3, h4, h5, h6, h7]

/-- THEOREM 7: every taxonomy witness proves `¬ C_safe`. -/
theorem taxonomyWitness_not_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) {r : ReopenTaxonomy}
    (hw : taxonomyWitness P x r) : ¬ CSafe P x := by
  intro hs
  cases r with
  | sourceMissing => exact hw hs.1
  | authorityOverreach => exact hw hs.2.1
  | graphNonconfluent => exact hw hs.2.2.1
  | gaugeLeak => exact hw hs.2.2.2.1
  | contractionUncertified => exact hw hs.2.2.2.2.1
  | omegaConflict => exact hw hs.2.2.2.2.2.1
  | freshnessStale => exact hw hs.2.2.2.2.2.2

/-- THEOREM 8: any classifier hit is sound for its taxonomy case. -/
theorem taxonomyWitness_of_classifyUnsafe_some {State : Type*}
    (P : CSafePredicates State) (x : State)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)]
    {r : ReopenTaxonomy} (h : classifyUnsafe P x = some r) :
    taxonomyWitness P x r := by
  by_cases h1 : P.sourceBacked x
  · by_cases h2 : P.authoritySafe x
    · by_cases h3 : P.graphConfluent x
      · by_cases h4 : P.gaugeNonleaking x
        · by_cases h5 : P.contractionSafe x
          · by_cases h6 : P.omegaConsistent x
            · by_cases h7 : P.freshnessSafe x
              · simp [classifyUnsafe, h1, h2, h3, h4, h5, h6, h7] at h
              · have hr : ReopenTaxonomy.freshnessStale = r := by
                  simpa [classifyUnsafe, h1, h2, h3, h4, h5, h6, h7] using h
                cases hr
                simp [taxonomyWitness, h7]
            · have hr : ReopenTaxonomy.omegaConflict = r := by
                simpa [classifyUnsafe, h1, h2, h3, h4, h5, h6] using h
              cases hr
              simp [taxonomyWitness, h6]
          · have hr : ReopenTaxonomy.contractionUncertified = r := by
              simpa [classifyUnsafe, h1, h2, h3, h4, h5] using h
            cases hr
            simp [taxonomyWitness, h5]
        · have hr : ReopenTaxonomy.gaugeLeak = r := by
            simpa [classifyUnsafe, h1, h2, h3, h4] using h
          cases hr
          simp [taxonomyWitness, h4]
      · have hr : ReopenTaxonomy.graphNonconfluent = r := by
          simpa [classifyUnsafe, h1, h2, h3] using h
        cases hr
        simp [taxonomyWitness, h3]
    · have hr : ReopenTaxonomy.authorityOverreach = r := by
        simpa [classifyUnsafe, h1, h2] using h
      cases hr
      simp [taxonomyWitness, h2]
  · have hr : ReopenTaxonomy.sourceMissing = r := by
      simpa [classifyUnsafe, h1] using h
    cases hr
    simp [taxonomyWitness, h1]

/-- THEOREM 9: outside `C_safe`, the classifier returns a precise taxonomy
    witness. -/
theorem classifyUnsafe_some_of_not_csafe {State : Type*}
    (P : CSafePredicates State) (x : State)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)]
    (hnot : ¬ CSafe P x) :
    ∃ r, classifyUnsafe P x = some r ∧ taxonomyWitness P x r := by
  cases hclass : classifyUnsafe P x with
  | none =>
      have hsafe : CSafe P x := (classifyUnsafe_none_iff_csafe P x).mp hclass
      exact False.elim (hnot hsafe)
  | some r =>
      exact ⟨r, rfl, taxonomyWitness_of_classifyUnsafe_some P x hclass⟩

/-- THEOREM 10: `¬ C_safe` is equivalent to the existence of a reopen taxonomy
    witness. -/
theorem not_csafe_iff_exists_taxonomy {State : Type*}
    (P : CSafePredicates State) (x : State)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)] :
    ¬ CSafe P x ↔ ∃ r, taxonomyWitness P x r := by
  constructor
  · intro hnot
    rcases classifyUnsafe_some_of_not_csafe P x hnot with ⟨r, _hclass, hw⟩
    exact ⟨r, hw⟩
  · rintro ⟨r, hw⟩
    exact taxonomyWitness_not_csafe P x hw

/-- THEOREM 11: the concrete classifier has a `some` result exactly outside
    `C_safe`. -/
theorem classifyUnsafe_some_iff_not_csafe {State : Type*}
    (P : CSafePredicates State) (x : State)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)] :
    (∃ r, classifyUnsafe P x = some r) ↔ ¬ CSafe P x := by
  constructor
  · rintro ⟨r, hclass⟩
    exact taxonomyWitness_not_csafe P x
      (taxonomyWitness_of_classifyUnsafe_some P x hclass)
  · intro hnot
    rcases classifyUnsafe_some_of_not_csafe P x hnot with ⟨r, hclass, _hw⟩
    exact ⟨r, hclass⟩

/-! ## C_safe partial λ whose obstruction is the reopen taxonomy -/

/-- A C_safe-domain partial λ with obstruction computed by the reopen taxonomy
    classifier. -/
def cSafePartialLambda {State Observation : Type*}
    (P : CSafePredicates State) (FG GF : State → Observation)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)]
    (hcomm : ∀ x, CSafe P x → FG x = GF x) :
    CertifiedPartialLambda State Observation (Option ReopenTaxonomy) where
  O := CSafe P
  FG := FG
  GF := GF
  obstruction := fun x => classifyUnsafe P x
  commute_on_O := hcomm

/-- The total attempt for the C_safe partial λ, with the `C_safe` decidability
    instance made explicit so downstream statements do not rely on unfolding
    the structure field `O`. -/
def tryCSafePartialLambda {State Observation : Type*}
    (P : CSafePredicates State) (FG GF : State → Observation)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)]
    (hcomm : ∀ x, CSafe P x → FG x = GF x) (x : State) :
    LambdaAttempt State Observation (Option ReopenTaxonomy) := by
  haveI : Decidable ((cSafePartialLambda P FG GF hcomm).O x) := by
    change Decidable (CSafe P x)
    infer_instance
  exact tryLambda (cSafePartialLambda P FG GF hcomm) x

/-- THEOREM 12: for the C_safe partial λ, every off-domain obstruction is
    characterized by a reopen-taxonomy case. -/
theorem cSafe_partial_lambda_obstruction_characterized {State Observation : Type*}
    (P : CSafePredicates State) (FG GF : State → Observation)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)]
    (hcomm : ∀ x, CSafe P x → FG x = GF x)
    (x : State) (hnot : ¬ CSafe P x) :
    ∃ r,
      tryCSafePartialLambda P FG GF hcomm x =
        LambdaAttempt.obstructed x (some r) ∧
      taxonomyWitness P x r := by
  rcases classifyUnsafe_some_of_not_csafe P x hnot with ⟨r, hclass, hw⟩
  refine ⟨r, ?_, hw⟩
  simp [tryCSafePartialLambda, tryLambda, cSafePartialLambda, hnot, hclass]

/-!
  Summary:
  - `cSafe_closed_under_safe_step` and
    `cSafe_closed_under_safe_step_iterate` prove closure of `C_safe`.
  - `safeMorphism_id` / `safeMorphism_comp` give the subcategory skeleton.
  - `lemma3_domain_gives_observable_bisimulation` packages Lemma 3 as the
    sufficient observable-bisimulation domain.
  - `classifyUnsafe_*` proves the complement of `C_safe` is exactly the finite
    reopen taxonomy.
  - `cSafe_partial_lambda_obstruction_characterized` connects that taxonomy to
    the obstruction branch of the certified partial λ.
-/
