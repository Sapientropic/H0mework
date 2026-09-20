import H0mework.Realization.Residual.P736

/-!
# Proposition 737: operator-level residual complement

P736 proves the scalar split is forced.

This file removes the scalar restriction.  For an arbitrary keep operator
`K : E -> E`, the trace side compatible with residual conservation is forced:

`trace r = r - K r`.

Thus every residual process has the same operator-level skeleton:

`r = K r + (r - K r)`.

Composition has the same trace accounting:

`trace(K₂ ∘ K₁) r = trace(K₁) r + trace(K₂) (K₁ r)`.

The scalar formula `r = (1-sigma)r + sigma r` is the one-dimensional scalar
reading of this operator complement law.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u v

variable {K : Type u} [Field K]
variable {E : Type v} [AddCommGroup E] [Module K E]

/-- The trace/spent side forced by a keep operator. -/
def complementTrace (keep : E -> E) : E -> E :=
  fun r : E => r - keep r

/-- The keep side forced by a trace operator. -/
def complementKeep (trace : E -> E) : E -> E :=
  fun r : E => r - trace r

/-- THEOREM 1: every keep operator has a canonical conservative complement
trace. -/
theorem keep_complementTrace_conserve
    (keep : E -> E) (r : E) :
    r = keep r + complementTrace keep r := by
  unfold complementTrace
  abel

/-- THEOREM 2: every keep operator therefore defines a residual split. -/
theorem complementTrace_residualSplit
    (keep : E -> E) :
    ResidualSplit keep (complementTrace keep) where
  conserve := keep_complementTrace_conserve keep

/-- THEOREM 3: residual conservation forces the trace side to be the
complement of keep. -/
theorem residualSplit_trace_eq_complement
    {keep trace : E -> E}
    (hsplit : ResidualSplit keep trace)
    (r : E) :
    trace r = complementTrace keep r := by
  unfold complementTrace
  calc
    trace r = keep r + trace r - keep r := by abel
    _ = r - keep r := by rw [← hsplit.conserve r]

/-- THEOREM 4: residual split is equivalent to trace being the complement of
keep. -/
theorem residualSplit_iff_trace_complement
    (keep trace : E -> E) :
    ResidualSplit keep trace ↔
      (∀ r : E, trace r = complementTrace keep r) := by
  constructor
  · intro hsplit r
    exact residualSplit_trace_eq_complement hsplit r
  · intro htrace
    constructor
    intro r
    rw [htrace r]
    exact keep_complementTrace_conserve keep r

/-- THEOREM 5: residual conservation also forces the keep side to be the
complement of trace. -/
theorem residualSplit_keep_eq_complement
    {keep trace : E -> E}
    (hsplit : ResidualSplit keep trace)
    (r : E) :
    keep r = complementKeep trace r := by
  unfold complementKeep
  calc
    keep r = keep r + trace r - trace r := by abel
    _ = r - trace r := by rw [← hsplit.conserve r]

/-- THEOREM 6: residual split is equivalent to keep being the complement of
trace. -/
theorem residualSplit_iff_keep_complement
    (keep trace : E -> E) :
    ResidualSplit keep trace ↔
      (∀ r : E, keep r = complementKeep trace r) := by
  constructor
  · intro hsplit r
    exact residualSplit_keep_eq_complement hsplit r
  · intro hkeep
    constructor
    intro r
    rw [hkeep r]
    unfold complementKeep
    abel

/-- THEOREM 7: for a fixed keep operator, any two conservative traces are
extensionally equal. -/
theorem residualSplit_trace_extensional_unique
    {keep trace₁ trace₂ : E -> E}
    (h₁ : ResidualSplit keep trace₁)
    (h₂ : ResidualSplit keep trace₂) :
    trace₁ = trace₂ := by
  funext r
  rw [residualSplit_trace_eq_complement h₁ r,
    residualSplit_trace_eq_complement h₂ r]

/-- THEOREM 8: for a fixed trace operator, any two conservative keeps are
extensionally equal. -/
theorem residualSplit_keep_extensional_unique
    {keep₁ keep₂ trace : E -> E}
    (h₁ : ResidualSplit keep₁ trace)
    (h₂ : ResidualSplit keep₂ trace) :
    keep₁ = keep₂ := by
  funext r
  rw [residualSplit_keep_eq_complement h₁ r,
    residualSplit_keep_eq_complement h₂ r]

/-- THEOREM 9: residual transport is the affine display of the complement
trace. -/
theorem residualTransportUpdate_eq_state_plus_complementTrace
    (keep : E -> E) (target x : E) :
    residualTransportUpdate keep target x =
      x + complementTrace keep (target - x) := by
  unfold residualTransportUpdate complementTrace
  abel

/-- THEOREM 10: the trace of composed keeps is first trace plus second trace
evaluated on the kept residual. -/
theorem complementTrace_compose
    (keep₁ keep₂ : E -> E) (r : E) :
    complementTrace (keep₂ ∘ keep₁) r =
      complementTrace keep₁ r + complementTrace keep₂ (keep₁ r) := by
  unfold complementTrace
  simp

/-- THEOREM 11: after two arbitrary keep steps, the original residual is the
final kept residual plus the accumulated trace. -/
theorem complementTrace_twoStep_conservation
    (keep₁ keep₂ : E -> E) (r : E) :
    r =
      (keep₂ ∘ keep₁) r +
        (complementTrace keep₁ r + complementTrace keep₂ (keep₁ r)) := by
  rw [← complementTrace_compose keep₁ keep₂ r]
  exact keep_complementTrace_conserve (keep₂ ∘ keep₁) r

/-- THEOREM 12: identity keep leaves no trace. -/
theorem complementTrace_id
    (r : E) :
    complementTrace (fun x : E => x) r = 0 := by
  unfold complementTrace
  simp

/-- THEOREM 13: zero keep turns the whole residual into trace. -/
theorem complementTrace_zero_keep
    (r : E) :
    complementTrace (fun _ : E => 0) r = r := by
  unfold complementTrace
  simp

/-- P737 certificate: operator-level residual complement, uniqueness, affine
display, and trace composition. -/
structure ResidualOperatorComplementCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  complement_trace_split :
    ∀ keep : E -> E,
      ResidualSplit keep (complementTrace keep)
  split_iff_trace_complement :
    ∀ keep trace : E -> E,
      ResidualSplit keep trace ↔
        (∀ r : E, trace r = complementTrace keep r)
  split_iff_keep_complement :
    ∀ keep trace : E -> E,
      ResidualSplit keep trace ↔
        (∀ r : E, keep r = complementKeep trace r)
  trace_unique_for_keep :
    ∀ keep trace₁ trace₂ : E -> E,
      ResidualSplit keep trace₁ ->
      ResidualSplit keep trace₂ ->
        trace₁ = trace₂
  keep_unique_for_trace :
    ∀ keep₁ keep₂ trace : E -> E,
      ResidualSplit keep₁ trace ->
      ResidualSplit keep₂ trace ->
        keep₁ = keep₂
  affine_display :
    ∀ keep : E -> E, ∀ target x : E,
      residualTransportUpdate keep target x =
        x + complementTrace keep (target - x)
  composition_trace_law :
    ∀ keep₁ keep₂ : E -> E, ∀ r : E,
      complementTrace (keep₂ ∘ keep₁) r =
        complementTrace keep₁ r + complementTrace keep₂ (keep₁ r)
  two_step_conservation :
    ∀ keep₁ keep₂ : E -> E, ∀ r : E,
      r =
        (keep₂ ∘ keep₁) r +
          (complementTrace keep₁ r + complementTrace keep₂ (keep₁ r))
  id_keep_zero_trace :
    ∀ r : E, complementTrace (fun x : E => x) r = 0
  zero_keep_full_trace :
    ∀ r : E, complementTrace (fun _ : E => 0) r = r
  residual_split_uniqueness :
    ResidualConservationSplitUniquenessCertificate K

/-- THEOREM 14: every module carrier supports operator-level residual
complement. -/
theorem residualOperatorComplementCertificate :
    ResidualOperatorComplementCertificate K E where
  complement_trace_split :=
    complementTrace_residualSplit
  split_iff_trace_complement :=
    residualSplit_iff_trace_complement
  split_iff_keep_complement :=
    residualSplit_iff_keep_complement
  trace_unique_for_keep := by
    intro keep trace₁ trace₂ h₁ h₂
    exact residualSplit_trace_extensional_unique h₁ h₂
  keep_unique_for_trace := by
    intro keep₁ keep₂ trace h₁ h₂
    exact residualSplit_keep_extensional_unique h₁ h₂
  affine_display :=
    residualTransportUpdate_eq_state_plus_complementTrace
  composition_trace_law :=
    complementTrace_compose
  two_step_conservation :=
    complementTrace_twoStep_conservation
  id_keep_zero_trace :=
    complementTrace_id
  zero_keep_full_trace :=
    complementTrace_zero_keep
  residual_split_uniqueness :=
    residualConservationSplitUniquenessCertificate

end AffineRelaxation
end SaturationMonoid
