/-
  Proposition 148: feedback-sign theorem for reflexive memory production.

  P51 calibrated the ontology: memory is recollectable potential, not passive
  storage.  This file adds the small signed-feedback layer requested in the
  memory-language notes:

      positive support  = saturation fired (η > 0 in a coordinate model)
      negative support  = obstruction fired (λ ≠ 0 in a coordinate model)
      zero sign         = neither support fired

  The theorem proved here is deliberately modest and exact:

    * `sign = zero` iff the signed recollection act has no recollectable memory
      potential.
    * an F-only/predictive system, modeled as one with neither write-back
      support, has zero sign everywhere and produces no recollectable memory.

  Boundary: the stronger claim that stable understanding requires both
  positive and negative feedback on an open neighborhood is not proved here.
  This module supplies the algebraic sign layer and the F-only impossibility
  theorem that such a conjecture would build on.
-/

import H0mework.Realization.Memory.StorageDistinction

/-! ## Signed feedback support -/

/-- The pointwise sign of feedback production.  `positive` means a saturation
write fired; `negative` means an obstruction write fired; `zero` means no
feedback write fired. -/
inductive FeedbackSign where
  | positive
  | negative
  | zero
  deriving DecidableEq, Repr

/-- The two write-back atoms used by the signed recollection act. -/
inductive FeedbackAtom where
  | saturationStrengthened
  | obstructionMarked
  deriving DecidableEq, Repr

/-- A signed feedback layer over states.  The two predicates are support
predicates, not scalar contents: instantiate them as `η > 0` and `λ ≠ 0` when
a concrete coordinate model is available. -/
structure FeedbackSupport (State : Type*) where
  positive : State -> Prop
  negative : State -> Prop

/-- Feedback memory is produced exactly when either write-back channel fires. -/
def FeedbackMemoryProduced {State : Type*}
    (S : FeedbackSupport State) (x : State) : Prop :=
  S.positive x \/ S.negative x

/-- The canonical signed recollection act induced by feedback support. -/
def feedbackRecollectionAct {State : Type*}
    (S : FeedbackSupport State) : RecollectionAct State FeedbackAtom where
  fires := fun x atom =>
    match atom with
    | FeedbackAtom.saturationStrengthened => S.positive x
    | FeedbackAtom.obstructionMarked => S.negative x

/-- Pointwise feedback sign.  If both channels fire at the same point, the
sign records the positive saturation event; the zero theorem below is
independent of that tie-break. -/
noncomputable def feedbackSign {State : Type*}
    (S : FeedbackSupport State) (x : State) : FeedbackSign :=
  by
    classical
    exact
      if S.positive x then
        FeedbackSign.positive
      else if S.negative x then
        FeedbackSign.negative
      else
        FeedbackSign.zero

/-- THEOREM 1: signed feedback memory production is exactly recollectable
potential for the signed recollection act. -/
theorem feedbackMemoryProduced_iff_recollectablePotential
    {State : Type*} (S : FeedbackSupport State) (x : State) :
    FeedbackMemoryProduced S x <->
      RecollectableMemoryPotential (feedbackRecollectionAct S) x := by
  constructor
  · intro h
    rcases h with hpos | hneg
    · exact ⟨FeedbackAtom.saturationStrengthened, hpos⟩
    · exact ⟨FeedbackAtom.obstructionMarked, hneg⟩
  · rintro ⟨atom, hfire⟩
    cases atom with
    | saturationStrengthened =>
        exact Or.inl hfire
    | obstructionMarked =>
        exact Or.inr hfire

/-- THEOREM 2: zero feedback sign is exactly zero memory production. -/
theorem feedbackSign_zero_iff_no_memoryProduction
    {State : Type*} (S : FeedbackSupport State) (x : State) :
    feedbackSign S x = FeedbackSign.zero <->
      ¬ FeedbackMemoryProduced S x := by
  classical
  by_cases hpos : S.positive x
  · simp [feedbackSign, FeedbackMemoryProduced, hpos]
  · by_cases hneg : S.negative x
    · simp [feedbackSign, FeedbackMemoryProduced, hpos, hneg]
    · simp [feedbackSign, FeedbackMemoryProduced, hpos, hneg]

/-- THEOREM 3: zero feedback sign is exactly absence of recollectable memory
potential for the signed recollection act.  This is P51 specialized to the
positive/negative feedback pair. -/
theorem feedbackSign_zero_iff_not_recollectablePotential
    {State : Type*} (S : FeedbackSupport State) (x : State) :
    feedbackSign S x = FeedbackSign.zero <->
      ¬ RecollectableMemoryPotential (feedbackRecollectionAct S) x := by
  rw [feedbackSign_zero_iff_no_memoryProduction]
  exact not_congr (feedbackMemoryProduced_iff_recollectablePotential S x)

/-! ## F-only systems -/

/-- A predictive/F-only system has no write-back channel into either
saturation or obstruction support. -/
def FOnlyFeedback {State : Type*} (S : FeedbackSupport State) : Prop :=
  forall x, ¬ FeedbackMemoryProduced S x

/-- THEOREM 4: F-only systems have zero feedback sign everywhere. -/
theorem fOnly_feedbackSign_zero
    {State : Type*} (S : FeedbackSupport State)
    (hF : FOnlyFeedback S) (x : State) :
    feedbackSign S x = FeedbackSign.zero := by
  exact (feedbackSign_zero_iff_no_memoryProduction S x).mpr (hF x)

/-- THEOREM 5: F-only systems produce no recollectable memory potential. -/
theorem fOnly_no_recollectablePotential
    {State : Type*} (S : FeedbackSupport State)
    (hF : FOnlyFeedback S) (x : State) :
    ¬ RecollectableMemoryPotential (feedbackRecollectionAct S) x := by
  exact (feedbackMemoryProduced_iff_recollectablePotential S x).not.mp (hF x)

/-! ## η / λ coordinate instance -/

/-- Coordinate form of the signed-feedback layer.  `eta` is the saturation
rate and `lambda` is an obstruction/residual coordinate. -/
structure FeedbackCoordinates (State Rate Residual : Type*) where
  eta : State -> Rate
  lambda : State -> Residual

/-- Coordinate support: positive memory when `η > 0`, negative memory when
`λ ≠ 0`. -/
def coordinateFeedbackSupport
    {State Rate Residual : Type*} [Zero Rate] [LT Rate] [Zero Residual]
    (C : FeedbackCoordinates State Rate Residual) :
    FeedbackSupport State where
  positive := fun x => (0 : Rate) < C.eta x
  negative := fun x => C.lambda x ≠ 0

/-- Coordinate feedback sign. -/
noncomputable def coordinateFeedbackSign
    {State Rate Residual : Type*} [Zero Rate] [LT Rate] [Zero Residual]
    (C : FeedbackCoordinates State Rate Residual) (x : State) :
    FeedbackSign :=
  feedbackSign (coordinateFeedbackSupport C) x

/-- THEOREM 6: in η/λ coordinates, zero sign means exactly
`¬ η > 0` and `λ = 0`. -/
theorem coordinateFeedbackSign_zero_iff
    {State Rate Residual : Type*}
    [Zero Rate] [LT Rate] [Zero Residual]
    (C : FeedbackCoordinates State Rate Residual) (x : State) :
    coordinateFeedbackSign C x = FeedbackSign.zero <->
      ¬ (0 : Rate) < C.eta x /\ C.lambda x = 0 := by
  classical
  unfold coordinateFeedbackSign
  rw [feedbackSign_zero_iff_no_memoryProduction]
  unfold FeedbackMemoryProduced coordinateFeedbackSupport
  constructor
  · intro h
    constructor
    · intro heta
      exact h (Or.inl heta)
    · by_contra hlambda
      exact h (Or.inr hlambda)
  · intro h hprod
    rcases hprod with heta | hlambda
    · exact h.1 heta
    · exact hlambda h.2

/-! ## Stable signed-memory certificate shape -/

/-- A local certificate that both feedback polarities occur in a region.  This
is the formal shape of the stronger conjecture: stable understanding should
require both positive reinforcement and negative gap-marking locally.  The
runtime/semantic theorem that this certificate is necessary is intentionally
not claimed here. -/
structure BipolarFeedbackRegion {State : Type*}
    (S : FeedbackSupport State) (Region : Set State) : Prop where
  positive_witness : exists x, x ∈ Region /\ S.positive x
  negative_witness : exists x, x ∈ Region /\ S.negative x

/-- THEOREM 7: a bipolar region cannot be F-only on that region. -/
theorem bipolarRegion_not_locally_fOnly
    {State : Type*} {S : FeedbackSupport State} {Region : Set State}
    (B : BipolarFeedbackRegion S Region) :
    ¬ (forall x, x ∈ Region -> ¬ FeedbackMemoryProduced S x) := by
  intro hF
  rcases B.positive_witness with ⟨x, hxRegion, hxPos⟩
  exact hF x hxRegion (Or.inl hxPos)

/-!
  Summary:
  - `FeedbackSupport` abstracts the two write-back supports: saturation and
    obstruction.
  - `feedbackSign_zero_iff_not_recollectablePotential` proves the sign-zero
    theorem against P51's recollectable-memory ontology.
  - `fOnly_feedbackSign_zero` proves the F-only impossibility statement:
    prediction without write-back has zero sign everywhere.
  - `BipolarFeedbackRegion` records the next conjectural acceptance shape
    without smuggling it in as a proved theorem.
-/
