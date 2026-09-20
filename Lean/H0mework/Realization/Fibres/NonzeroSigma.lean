import H0mework.Realization.Fibres.P550
import H0mework.Realization.Residual.Producer

/-!
# NonzeroSigmaFiberSemantics

The zero fiber is the annealed specialization.  A nonzero sigma fiber is not
another copy of the base object; it is a fibration over the base with a live
headroom coordinate.  This file packages that active-fiber semantics directly.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

set_option linter.checkUnivs false

/-! ## Active sigma fibers as trivial fibrations -/

/-- A minimal fibration object: total space, base, fiber, projection, and a
trivialization witnessing that the projection is the first coordinate. -/
structure ActiveSigmaFibration where
  Total : Type u
  Base : Type v
  Fiber : Type w
  projection : Total -> Base
  trivialization : Total ≃ Base × Fiber
  projection_eq :
    ∀ z : Total, projection z = (trivialization z).1

/-- For `σ ≠ 0`, the relaxed sigma fiber is the total space of a trivial
fibration over the carrier with fiber `H`. -/
def activeSigmaFibration
    {K : Type u} [Zero K] (X : Type v) (H : Type w)
    {σ : K} (hσ : σ ≠ 0) :
    ActiveSigmaFibration where
  Total := SigmaRelaxedObject K X H σ
  Base := X
  Fiber := H
  projection := sigmaActiveForget (K := K) (X := X) (H := H) hσ
  trivialization :=
    sigmaActiveRelaxedEquivRaw (K := K) (X := X) (H := H) hσ
  projection_eq := by
    intro z
    rfl

/-- Active sigma points with the same carrier coordinate but distinct
headrooms are distinct points of the active fiber. -/
theorem activeSigmaFiber_vertical_points_distinct
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0) (x : X)
    {h₁ h₂ : H} (hh : h₁ ≠ h₂) :
    sigmaRelaxedMk (K := K) (σ := σ) x h₁ ≠
      sigmaRelaxedMk (K := K) (σ := σ) x h₂ := by
  intro hz
  have hp :
      (x, h₁) = (x, h₂) := by
    simpa using
      congrArg
        (sigmaActiveRelaxedEquivRaw
          (K := K) (X := X) (H := H) hσ)
        hz
  exact hh (congrArg Prod.snd hp)

/-- At `σ = 0`, the same vertical pair collapses.  This is the boundary
between active fibration semantics and annealed standard-object semantics. -/
theorem zeroSigmaFiber_vertical_points_collapse
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    (x : X) (h₁ h₂ : H) :
    sigmaRelaxedMk (K := K) (σ := (0 : K)) x h₁ =
      sigmaRelaxedMk (K := K) (σ := (0 : K)) x h₂ :=
  sigmaZero_headroom_irrelevant (K := K) x h₁ h₂

/-- If the headroom has two values, the active fibration has a nontrivial
vertical fiber over every base point. -/
theorem activeSigmaFibration_has_nontrivial_vertical
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0) (x : X)
    {h₁ h₂ : H} (hh : h₁ ≠ h₂) :
    sigmaActiveForget (K := K) (X := X) (H := H) hσ
        (sigmaRelaxedMk (K := K) (σ := σ) x h₁) =
      sigmaActiveForget (K := K) (X := X) (H := H) hσ
        (sigmaRelaxedMk (K := K) (σ := σ) x h₂) ∧
    sigmaRelaxedMk (K := K) (σ := σ) x h₁ ≠
      sigmaRelaxedMk (K := K) (σ := σ) x h₂ := by
  exact ⟨rfl, activeSigmaFiber_vertical_points_distinct hσ x hh⟩

/-! ## Active sections preserve headroom fields -/

/-- A section of the active sigma fibration: one relaxed point over each base
point, with projection returning that base point. -/
abbrev ActiveSigmaSection
    {K : Type u} [Zero K] (X : Type v) (H : Type w)
    {σ : K} (hσ : σ ≠ 0) :
    Type (max v w) :=
  {s : X -> SigmaRelaxedObject K X H σ //
    ∀ x : X, sigmaActiveForget (K := K) (X := X) (H := H) hσ (s x) = x}

/-- A headroom field determines an active sigma section. -/
def activeSigmaSectionOfHeadroom
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0) (η : X -> H) :
    ActiveSigmaSection (K := K) X H hσ :=
  ⟨fun x => sigmaRelaxedMk (K := K) (σ := σ) x (η x), by
    intro x
    rfl⟩

/-- An active sigma section has a well-defined headroom field. -/
def activeSigmaSectionHeadroom
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0)
    (S : ActiveSigmaSection (K := K) X H hσ) : X -> H :=
  fun x =>
    (sigmaActiveRelaxedEquivRaw
      (K := K) (X := X) (H := H) hσ (S.1 x)).2

/-- Active sigma sections are exactly headroom fields over the base.  This is
the category-level content of the nonzero fiber: it carries a field of vertical
data, while the zero fiber forgets that field. -/
def activeSigmaSectionEquivHeadroom
    {K : Type u} [Zero K] (X : Type v) (H : Type w)
    {σ : K} (hσ : σ ≠ 0) :
    ActiveSigmaSection (K := K) X H hσ ≃ (X -> H) where
  toFun := activeSigmaSectionHeadroom (K := K) (X := X) (H := H) hσ
  invFun := activeSigmaSectionOfHeadroom (K := K) (X := X) (H := H) hσ
  left_inv := by
    intro S
    apply Subtype.ext
    funext x
    apply
      (sigmaActiveRelaxedEquivRaw
        (K := K) (X := X) (H := H) hσ).injective
    let p :=
      sigmaActiveRelaxedEquivRaw
        (K := K) (X := X) (H := H) hσ (S.1 x)
    have hp : p.1 = x := S.2 x
    change (x, p.2) = p
    exact Prod.ext hp.symm rfl
  right_inv := by
    intro η
    funext x
    rfl

@[simp] theorem activeSigmaSectionEquivHeadroom_apply
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0) (η : X -> H) :
    activeSigmaSectionHeadroom (K := K) (X := X) (H := H) hσ
        (activeSigmaSectionOfHeadroom
          (K := K) (X := X) (H := H) hσ η) =
      η :=
  (activeSigmaSectionEquivHeadroom X H hσ).right_inv η

/-- The active section constructor is faithful to its headroom field.  A
nonzero sigma section therefore does not add quotient noise on top of the
vertical coordinate. -/
theorem activeSigmaSectionOfHeadroom_injective
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0) :
    Function.Injective
      (activeSigmaSectionOfHeadroom
        (K := K) (X := X) (H := H) hσ) := by
  intro η₁ η₂ hsection
  have hfields :
      activeSigmaSectionHeadroom
          (K := K) (X := X) (H := H) hσ
          (activeSigmaSectionOfHeadroom
            (K := K) (X := X) (H := H) hσ η₁) =
        activeSigmaSectionHeadroom
          (K := K) (X := X) (H := H) hσ
          (activeSigmaSectionOfHeadroom
            (K := K) (X := X) (H := H) hσ η₂) :=
    congrArg
      (activeSigmaSectionHeadroom
        (K := K) (X := X) (H := H) hσ)
      hsection
  simpa using hfields

/-- Active sigma sections are extensionally equal exactly when their headroom
fields are equal.  This is the categorical faithfulness of the nonzero fiber
section semantics. -/
theorem activeSigmaSection_eq_iff_headroom_eq
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0)
    (S T : ActiveSigmaSection (K := K) X H hσ) :
    S = T ↔
      activeSigmaSectionHeadroom
          (K := K) (X := X) (H := H) hσ S =
        activeSigmaSectionHeadroom
          (K := K) (X := X) (H := H) hσ T := by
  constructor
  · intro h
    exact congrArg
      (activeSigmaSectionHeadroom
        (K := K) (X := X) (H := H) hσ) h
  · intro h
    exact (activeSigmaSectionEquivHeadroom X H hσ).injective h

/-- At `σ = 0`, headroom fields no longer determine distinct sections: every
field collapses to the same zero-fiber section over the base. -/
theorem zeroSigmaHeadroomField_sections_collapse
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    (η₁ η₂ : X -> H) :
    (fun x : X => sigmaRelaxedMk (K := K) (σ := (0 : K)) x (η₁ x)) =
      (fun x : X =>
        sigmaRelaxedMk (K := K) (σ := (0 : K)) x (η₂ x)) := by
  funext x
  exact sigmaZero_headroom_irrelevant (K := K) x (η₁ x) (η₂ x)

/-! ## Active sections as residual-producer trace carriers -/

/-- Any residual-carrier system producer determines an active sigma section:
the base point is the producer state, and the vertical coordinate is the trace
forced by Truth Formula Core from the producer's own keep/residual pair. -/
def activeSigmaSystemProducerTraceSection
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State) :
    ActiveSigmaSection (K := K) State E hσ :=
  activeSigmaSectionOfHeadroom
    (K := K) (X := State) (H := E) hσ
    (fun s => linearResidualTrace P.keep (P.residual s))

/-- The headroom of the producer trace section is exactly the forced trace of
the producer's residual carrier; no independent headroom field is supplied. -/
theorem activeSigmaSystemProducerTraceSection_headroom_eq_trace
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (s : State) :
    activeSigmaSectionHeadroom
        (K := K) (X := State) (H := E) hσ
        (activeSigmaSystemProducerTraceSection hσ P) s =
      linearResidualTrace P.keep (P.residual s) := by
  rfl

/-- The producer's residual split can be read with the active-sigma headroom as
the complementary trace term.  Thus the active section is forced by Truth
Formula Core's residual split, not supplied as a semantic shell. -/
theorem activeSigmaSystemProducerTraceSection_residual_split
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (s : State) :
    P.residual s =
      P.keep (P.residual s) +
        activeSigmaSectionHeadroom
          (K := K) (X := State) (H := E) hσ
          (activeSigmaSystemProducerTraceSection hσ P) s := by
  rw [activeSigmaSystemProducerTraceSection_headroom_eq_trace]
  exact truthFormula_residual_split P.keep (P.residual s)

/-- Any proposed headroom field satisfying the producer's Truth Formula
residual split is theorem-equal to the active trace-section headroom. -/
theorem activeSigmaSystemProducerTraceSection_headroom_eq_of_residual_split
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (η : State -> E)
    (hsplit :
      ∀ s : State, P.residual s = P.keep (P.residual s) + η s) :
    η =
      activeSigmaSectionHeadroom
        (K := K) (X := State) (H := E) hσ
        (activeSigmaSystemProducerTraceSection hσ P) := by
  funext s
  rw [activeSigmaSystemProducerTraceSection_headroom_eq_trace]
  exact truthFormula_trace_eq_of_split P.keep (P.residual s) (η s)
    (hsplit s)

/-- A section whose headroom satisfies the producer residual split is the
producer trace section itself.  This is the no-free theorem for nonzero sigma
sections: the section is generated by the producer trace. -/
theorem activeSigmaSectionOfHeadroom_eq_systemProducerTraceSection_of_residual_split
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (η : State -> E)
    (hsplit :
      ∀ s : State, P.residual s = P.keep (P.residual s) + η s) :
    activeSigmaSectionOfHeadroom
        (K := K) (X := State) (H := E) hσ η =
      activeSigmaSystemProducerTraceSection hσ P := by
  apply
    (activeSigmaSection_eq_iff_headroom_eq
      (K := K) (X := State) (H := E) hσ
      (activeSigmaSectionOfHeadroom
        (K := K) (X := State) (H := E) hσ η)
      (activeSigmaSystemProducerTraceSection hσ P)).mpr
  rw [activeSigmaSectionEquivHeadroom_apply]
  exact activeSigmaSystemProducerTraceSection_headroom_eq_of_residual_split
    hσ P η hsplit

/-- Any active section whose own headroom satisfies the producer residual split
is the producer trace section.  This removes the last possible external section
shell: the theorem does not assume the section was originally constructed by
`activeSigmaSectionOfHeadroom`. -/
theorem activeSigmaSection_eq_systemProducerTraceSection_of_residual_split
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (S : ActiveSigmaSection (K := K) State E hσ)
    (hsplit :
      ∀ s : State,
        P.residual s =
          P.keep (P.residual s) +
            activeSigmaSectionHeadroom
              (K := K) (X := State) (H := E) hσ S s) :
    S = activeSigmaSystemProducerTraceSection hσ P := by
  apply
    (activeSigmaSection_eq_iff_headroom_eq
      (K := K) (X := State) (H := E) hσ
      S (activeSigmaSystemProducerTraceSection hσ P)).mpr
  exact
    activeSigmaSystemProducerTraceSection_headroom_eq_of_residual_split
      hσ P
      (activeSigmaSectionHeadroom
        (K := K) (X := State) (H := E) hσ S)
      hsplit

/-- The active trace-section construction is faithful to the Truth Formula Core
trace field of a producer.  Two producer trace sections in the same nonzero
sigma fiber are equal exactly when their forced residual-trace fields are
equal pointwise. -/
theorem activeSigmaSystemProducerTraceSection_eq_iff_trace_field_eq
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P Q : ResidualProjection.ResidualCarrierSystemProducer K E State) :
    activeSigmaSystemProducerTraceSection hσ P =
        activeSigmaSystemProducerTraceSection hσ Q ↔
      (fun s : State => linearResidualTrace P.keep (P.residual s)) =
        (fun s : State => linearResidualTrace Q.keep (Q.residual s)) := by
  constructor
  · intro hsection
    funext s
    have hhead :
        activeSigmaSectionHeadroom
            (K := K) (X := State) (H := E) hσ
            (activeSigmaSystemProducerTraceSection hσ P) =
          activeSigmaSectionHeadroom
            (K := K) (X := State) (H := E) hσ
            (activeSigmaSystemProducerTraceSection hσ Q) :=
      congrArg
        (activeSigmaSectionHeadroom
          (K := K) (X := State) (H := E) hσ)
        hsection
    simpa [activeSigmaSystemProducerTraceSection_headroom_eq_trace]
      using congrFun hhead s
  · intro htrace
    apply
      (activeSigmaSection_eq_iff_headroom_eq
        (K := K) (X := State) (H := E) hσ
        (activeSigmaSystemProducerTraceSection hσ P)
        (activeSigmaSystemProducerTraceSection hσ Q)).mpr
    funext s
    simpa [activeSigmaSystemProducerTraceSection_headroom_eq_trace]
      using congrFun htrace s

/-- Nonzero active headroom is the same event as residual-memory potential on
the producer's own residual carrier.  This lowers arbitrary domain producers
into the active sigma section semantics rather than keeping sigma geometry as
only a scalar-affine special case. -/
theorem activeSigmaSystemProducerTraceSection_headroom_ne_zero_iff_memoryPotential
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (s : State) :
    activeSigmaSectionHeadroom
        (K := K) (X := State) (H := E) hσ
        (activeSigmaSystemProducerTraceSection hσ P) s ≠ 0 ↔
      RecollectableMemoryPotential
        (ResidualProjection.residualMemoryAct P.keep) (P.residual s) := by
  rw [activeSigmaSystemProducerTraceSection_headroom_eq_trace]
  simpa [ResidualProjection.residualInformationReadout] using
    (ResidualProjection.residualMemoryPotential_iff_informationTrace_nonzero
      P.keep (P.residual s)).symm

/-- If the producer's keep operator is active/faithful, nonzero active
headroom is exactly nonzero producer residual. -/
theorem activeSigmaSystemProducerTraceSection_headroom_ne_zero_iff_residual_ne_zero
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (hactive : ResidualTransportActive P.keep) (s : State) :
    activeSigmaSectionHeadroom
        (K := K) (X := State) (H := E) hσ
        (activeSigmaSystemProducerTraceSection hσ P) s ≠ 0 ↔
      P.residual s ≠ 0 := by
  rw [activeSigmaSystemProducerTraceSection_headroom_eq_trace]
  have htrace_zero_iff_residual_zero :
      linearResidualTrace P.keep (P.residual s) = 0 ↔
        P.residual s = 0 := by
    exact
      (residualTransport_fixed_iff_zero_trace
        P.keep hactive (P.residual s)).symm.trans
        (residualTransport_fixed_iff_zero_residual
          P.keep hactive (P.residual s))
  exact not_congr htrace_zero_iff_residual_zero

/-- If the producer's keep operator is active/faithful, zero active headroom is
exactly zero producer residual.  This is the zero side of the same Truth
Formula Core boundary as the nonzero detector above. -/
theorem activeSigmaSystemProducerTraceSection_headroom_eq_zero_iff_residual_zero
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (hactive : ResidualTransportActive P.keep) (s : State) :
    activeSigmaSectionHeadroom
        (K := K) (X := State) (H := E) hσ
        (activeSigmaSystemProducerTraceSection hσ P) s = 0 ↔
      P.residual s = 0 := by
  rw [activeSigmaSystemProducerTraceSection_headroom_eq_trace]
  exact
    (residualTransport_fixed_iff_zero_trace
      P.keep hactive (P.residual s)).symm.trans
      (residualTransport_fixed_iff_zero_residual
        P.keep hactive (P.residual s))

/-- Truth Formula Core fixedness is equivalent to zero active-sigma headroom for
the same residual-system producer.  The active section therefore carries the
producer's fixed boundary, not an independent semantic receipt. -/
theorem activeSigmaSystemProducerTraceSection_fixed_iff_headroom_eq_zero
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (hactive : ResidualTransportActive P.keep) (s : State) :
    ResidualTransportFixed P.keep (P.residual s) ↔
      activeSigmaSectionHeadroom
        (K := K) (X := State) (H := E) hσ
        (activeSigmaSystemProducerTraceSection hσ P) s = 0 := by
  exact
    (residualTransport_fixed_iff_zero_residual
      P.keep hactive (P.residual s)).trans
      (activeSigmaSystemProducerTraceSection_headroom_eq_zero_iff_residual_zero
        hσ P hactive s).symm

/-- The full fixed/zero/trace/energy boundary can be read with active-sigma
headroom as the zero-residual component. -/
theorem activeSigmaSystemProducerTraceSection_fixed_iff_zero_headroom_trace_energy
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (hactive : ResidualTransportActive P.keep)
    (energy : E -> ℝ) (henergy : ∀ r : E, energy r = 0 ↔ r = 0)
    (s : State) :
    ResidualTransportFixed P.keep (P.residual s) ↔
      activeSigmaSectionHeadroom
          (K := K) (X := State) (H := E) hσ
          (activeSigmaSystemProducerTraceSection hσ P) s = 0 ∧
        linearResidualTrace P.keep (P.residual s) = 0 ∧
          energy (P.residual s) = 0 := by
  constructor
  · intro hfixed
    have hcore :=
      (truthFormula_fixed_iff_zero_residual_trace_energy
        P.keep energy hactive henergy (P.residual s)).mp hfixed
    exact
      ⟨(activeSigmaSystemProducerTraceSection_headroom_eq_zero_iff_residual_zero
          hσ P hactive s).mpr hcore.1,
        hcore.2.1, hcore.2.2⟩
  · intro h
    exact
      (truthFormula_fixed_iff_zero_residual_trace_energy
        P.keep energy hactive henergy (P.residual s)).mpr
        ⟨(activeSigmaSystemProducerTraceSection_headroom_eq_zero_iff_residual_zero
            hσ P hactive s).mp h.1,
          h.2.1, h.2.2⟩

/-- The active headroom field inherits the producer's residual transport law:
after the producer update, headroom is transported by the same keep operator.
This is the categorical content of the generic bridge, not a separate receipt
field attached to the sigma fiber. -/
theorem activeSigmaSystemProducerTraceSection_headroom_update_eq_keep_headroom
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (s : State) :
    activeSigmaSectionHeadroom
        (K := K) (X := State) (H := E) hσ
        (activeSigmaSystemProducerTraceSection hσ P) (P.update s) =
      P.keep
        (activeSigmaSectionHeadroom
          (K := K) (X := State) (H := E) hσ
          (activeSigmaSystemProducerTraceSection hσ P) s) := by
  rw [activeSigmaSystemProducerTraceSection_headroom_eq_trace,
    activeSigmaSystemProducerTraceSection_headroom_eq_trace]
  rw [P.residual_transport_law s]
  dsimp [linearResidualTrace]
  simp

/-- A producer update is residual-action-zero exactly when the active sigma
headroom at that state is zero.  This is the concrete zero-action boundary
forced by the producer's own residual transport law. -/
theorem activeSigmaSystemProducerTraceSection_update_residual_eq_self_iff_headroom_eq_zero
    {K : Type u} {E : Type v} {State : Type w}
    [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0)
    (P : ResidualProjection.ResidualCarrierSystemProducer K E State)
    (s : State) :
    P.residual (P.update s) = P.residual s ↔
      activeSigmaSectionHeadroom
        (K := K) (X := State) (H := E) hσ
        (activeSigmaSystemProducerTraceSection hσ P) s = 0 := by
  rw [P.residual_transport_law s,
    activeSigmaSystemProducerTraceSection_headroom_eq_trace]
  constructor
  · intro hkeep
    dsimp [linearResidualTrace]
    rw [hkeep]
    abel
  · intro htrace
    have hsplit := truthFormula_residual_split P.keep (P.residual s)
    rw [htrace, add_zero] at hsplit
    exact hsplit.symm

/-- The active sigma section whose vertical coordinate is the trace forced by
the scalar affine residual producer. -/
def activeSigmaProducerTraceSection
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0) (target : E) :
    ActiveSigmaSection (K := K) E E hσ :=
  activeSigmaSystemProducerTraceSection hσ
    (ResidualProjection.scalarAffineSystemProducer target σ)

/-- In a nonzero active sigma fiber, the vertical headroom of the producer
trace section is exactly the scalar affine producer's update displacement.
This is the bridge from Truth Formula Core trace to active fiber geometry. -/
theorem activeSigmaProducerTraceSection_headroom_eq_update_displacement
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {σ : K} (hσ : σ ≠ 0) (target x : E) :
    activeSigmaSectionHeadroom
        (K := K) (X := E) (H := E) hσ
        (activeSigmaProducerTraceSection hσ target) x =
      (ResidualProjection.scalarAffineSystemProducer target σ).update x - x := by
  change
    linearResidualTrace
        (scalarKeepLinearMap (K := K) (E := E) σ)
        (target - x) =
      relaxModule target σ x - x
  rw [truthFormula_scalar_trace]
  unfold relaxModule
  abel

/-- Over a faithful vector-space fiber, the active producer-trace headroom is
nonzero exactly when the scalar affine residual is nonzero.  Thus the nonzero
sigma fiber detects genuine residual displacement instead of adding a receipt
layer over the zero fiber. -/
theorem activeSigmaProducerTraceSection_headroom_ne_zero_iff_residual_ne_zero
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [NoZeroSMulDivisors K E]
    {σ : K} (hσ : σ ≠ 0) (target x : E) :
    activeSigmaSectionHeadroom
        (K := K) (X := E) (H := E) hσ
        (activeSigmaProducerTraceSection hσ target) x ≠ 0 ↔
      (ResidualProjection.scalarAffineSystemProducer target σ).residual x ≠
        0 := by
  rw [activeSigmaProducerTraceSection_headroom_eq_update_displacement]
  change relaxModule target σ x - x ≠ 0 ↔ target - x ≠ 0
  unfold relaxModule
  have hdisp : x + σ • (target - x) - x = σ • (target - x) := by
    abel
  rw [hdisp]
  constructor
  · intro h hres
    exact h (by rw [hres, smul_zero])
  · intro hres
    exact smul_ne_zero hσ hres

/-- Equivalently, the active producer-trace headroom vanishes exactly at the
scalar affine producer's target fiber. -/
theorem activeSigmaProducerTraceSection_headroom_ne_zero_iff_ne_target
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [NoZeroSMulDivisors K E]
    {σ : K} (hσ : σ ≠ 0) (target x : E) :
    activeSigmaSectionHeadroom
        (K := K) (X := E) (H := E) hσ
        (activeSigmaProducerTraceSection hσ target) x ≠ 0 ↔
      target ≠ x := by
  rw [activeSigmaProducerTraceSection_headroom_ne_zero_iff_residual_ne_zero
    hσ target x]
  change target - x ≠ 0 ↔ target ≠ x
  exact sub_ne_zero

/-- In a nonzero sigma fiber, scalar affine producer-trace sections faithfully
remember the target.  This is the categorical side of the active geometry:
the trace-section construction embeds the target space into the section space
instead of collapsing it as the zero fiber does. -/
theorem activeSigmaProducerTraceSection_target_injective
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [NoZeroSMulDivisors K E]
    {σ : K} (hσ : σ ≠ 0) :
    Function.Injective
      (fun target : E => activeSigmaProducerTraceSection
        (K := K) (E := E) hσ target) := by
  intro target₁ target₂ hsections
  have hhead :
      activeSigmaSectionHeadroom
          (K := K) (X := E) (H := E) hσ
          (activeSigmaProducerTraceSection hσ target₁) 0 =
        activeSigmaSectionHeadroom
          (K := K) (X := E) (H := E) hσ
          (activeSigmaProducerTraceSection hσ target₂) 0 := by
    exact
      congrFun
        (congrArg
          (activeSigmaSectionHeadroom
            (K := K) (X := E) (H := E) hσ)
          hsections)
        0
  rw [activeSigmaProducerTraceSection_headroom_eq_update_displacement,
    activeSigmaProducerTraceSection_headroom_eq_update_displacement] at hhead
  change relaxModule target₁ σ 0 - 0 = relaxModule target₂ σ 0 - 0 at hhead
  unfold relaxModule at hhead
  have hsmul : σ • target₁ = σ • target₂ := by
    simpa using hhead
  exact (smul_right_injective E hσ) hsmul

end AffineRelaxation

open AffineRelaxation

/-! ## Core-object active sigma semantics -/

/-- Every listed core object has an active nonzero-sigma fibration over its
standard carrier. -/
def coreObjectActiveSigmaFibration
    (O : CoreMathematicalObject18) {σ : ℝ} (hσ : σ ≠ 0) :
    ActiveSigmaFibration :=
  activeSigmaFibration
    (K := ℝ) (CoreObjectCarrier O) CoreObjectHeadroom hσ

/-- Every listed core object has nontrivial active vertical structure in every
nonzero sigma fiber. -/
theorem coreObjectActiveSigmaFibration_nontrivial
    (O : CoreMathematicalObject18) {σ : ℝ} (hσ : σ ≠ 0) :
    ∃ z₁ z₂ : SigmaRelaxedObject ℝ (CoreObjectCarrier O)
        CoreObjectHeadroom σ,
      sigmaActiveForget
          (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)
          hσ z₁ =
        sigmaActiveForget
          (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)
          hσ z₂ ∧
      z₁ ≠ z₂ := by
  let x : CoreObjectCarrier O := default
  refine ⟨sigmaRelaxedMk (K := ℝ) (σ := σ) x (0 : CoreObjectHeadroom),
    sigmaRelaxedMk (K := ℝ) (σ := σ) x (1 : CoreObjectHeadroom), ?_⟩
  exact
    activeSigmaFibration_has_nontrivial_vertical
      (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)
      hσ x (by norm_num : (0 : CoreObjectHeadroom) ≠ 1)

/-- For every listed core object, active nonzero-sigma sections are exactly
headroom fields on the object's standard carrier. -/
def coreObjectActiveSigmaSectionEquivHeadroom
    (O : CoreMathematicalObject18) {σ : ℝ} (hσ : σ ≠ 0) :
    ActiveSigmaSection
        (K := ℝ) (CoreObjectCarrier O) CoreObjectHeadroom hσ ≃
      (CoreObjectCarrier O -> CoreObjectHeadroom) :=
  activeSigmaSectionEquivHeadroom
    (K := ℝ) (CoreObjectCarrier O) CoreObjectHeadroom hσ

/-- Each listed core object's active section space is nontrivial whenever
`σ ≠ 0`: the constant-zero and constant-one headroom fields give different
sections. -/
theorem coreObjectActiveSigmaSection_space_nontrivial
    (O : CoreMathematicalObject18) {σ : ℝ} (hσ : σ ≠ 0) :
    ∃ S₀ S₁ :
        ActiveSigmaSection
          (K := ℝ) (CoreObjectCarrier O) CoreObjectHeadroom hσ,
      S₀ ≠ S₁ := by
  let S₀ :=
    activeSigmaSectionOfHeadroom
      (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)
      hσ (fun _ => (0 : CoreObjectHeadroom))
  let S₁ :=
    activeSigmaSectionOfHeadroom
      (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)
      hσ (fun _ => (1 : CoreObjectHeadroom))
  refine ⟨S₀, S₁, ?_⟩
  intro h
  have hfields :
      (fun _ : CoreObjectCarrier O => (0 : CoreObjectHeadroom)) =
        (fun _ : CoreObjectCarrier O => (1 : CoreObjectHeadroom)) := by
    simpa [S₀, S₁] using
      congrArg
        (activeSigmaSectionHeadroom
          (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)
          hσ)
        h
  have hpoint := congrFun hfields (default : CoreObjectCarrier O)
  norm_num at hpoint


end SaturationMonoid
