import H0mework.Realization.Residual.P738

/-!
# Proposition 739: natural residual processes are exactly scalar rates

P737 proves that trace is the complement of keep.
P738 proves that carrier-natural keep is scalar.

This file packages the next throat: a carrier-natural residual process is
classified by one scalar rate

`sigma = complementTrace keepR 1`.

Every such process is extensionally the canonical scalar process at that rate,
and process composition sends rates to noisy-OR:

`sigma(p₂ ∘ p₁) = satOrField sigma(p₁) sigma(p₂)`.

So the scalar noisy-OR monoid is not merely a convenient coordinate.  It is the
process algebra forced by scalar-line naturality plus residual complement.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- A scalar-line natural residual process consists of a scalar keep readout
and a carrier keep operator, with naturality on both the scalar carrier and the
target carrier. -/
structure ScalarLineNaturalResidualProcess
    (E : Type u) [AddCommGroup E] [Module ℝ E] where
  keepR : ℝ -> ℝ
  keepE : E -> E
  real_naturality : ScalarLineNaturality (E := ℝ) keepR keepR
  carrier_naturality : ScalarLineNaturality keepR keepE

namespace ScalarLineNaturalResidualProcess

/-- The scalar rate read out by a natural residual process. -/
def rate (p : ScalarLineNaturalResidualProcess E) : ℝ :=
  complementTrace p.keepR 1

/-- THEOREM 1: the scalar keep at unit residual is `1-rate`. -/
theorem keepR_one_eq_one_sub_rate
    (p : ScalarLineNaturalResidualProcess E) :
    p.keepR 1 = 1 - p.rate := by
  unfold rate complementTrace
  ring

/-- THEOREM 2: the scalar keep readout is multiplication by `1-rate`. -/
theorem keepR_forced
    (p : ScalarLineNaturalResidualProcess E) (a : ℝ) :
    p.keepR a = (1 - p.rate) * a := by
  calc
    p.keepR a = (p.keepR 1) • a :=
      scalarLineNaturality_real_keep_forced_scalar
        p.real_naturality a
    _ = (1 - p.rate) * a := by
      rw [keepR_one_eq_one_sub_rate p]
      rfl

/-- THEOREM 3: the carrier keep is multiplication by `1-rate`. -/
theorem keepE_forced
    (p : ScalarLineNaturalResidualProcess E) (r : E) :
    p.keepE r = (1 - p.rate) • r := by
  exact scalarLineNaturality_keep_forced_by_traceReadout
    p.carrier_naturality (rfl : complementTrace p.keepR 1 = p.rate) r

/-- THEOREM 4: the carrier trace is multiplication by `rate`. -/
theorem traceE_forced
    (p : ScalarLineNaturalResidualProcess E) (r : E) :
    complementTrace p.keepE r = p.rate • r := by
  exact scalarLineNaturality_trace_forced_by_traceReadout
    p.carrier_naturality (rfl : complementTrace p.keepR 1 = p.rate) r

/-- THEOREM 5: the process update display is forced to `relaxModule`. -/
theorem update_forced_relaxModule
    (p : ScalarLineNaturalResidualProcess E) (target x : E) :
    residualTransportUpdate p.keepE target x =
      relaxModule target p.rate x := by
  exact scalarLineNaturality_residualTransportUpdate_forced_relaxModule
    p.carrier_naturality (rfl : complementTrace p.keepR 1 = p.rate)
    target x

/-- THEOREM 6: on the scalar target-one face, the process display is
`bumpSatField`. -/
theorem targetOne_forced_bumpSat
    (p : ScalarLineNaturalResidualProcess ℝ) (x : ℝ) :
    residualTransportUpdate p.keepR 1 x =
      bumpSatField x p.rate := by
  exact scalarLineNaturality_targetOne_forced_bumpSat
    p.real_naturality (rfl : complementTrace p.keepR 1 = p.rate) x

/-- The canonical process for a scalar rate. -/
def canonical (sigma : ℝ) : ScalarLineNaturalResidualProcess E where
  keepR := scalarKeep (K := ℝ) (E := ℝ) sigma
  keepE := scalarKeep (K := ℝ) (E := E) sigma
  real_naturality := by
    intro x a
    unfold scalarKeep
    simp
    ring
  carrier_naturality := by
    intro x a
    unfold scalarKeep
    module

/-- THEOREM 7: canonical process rate readout is the input rate. -/
theorem canonical_rate
    (sigma : ℝ) :
    (canonical (E := E) sigma).rate = sigma := by
  unfold rate canonical complementTrace scalarKeep
  ring

/-- THEOREM 8: every natural process has the same scalar keep as its canonical
rate process. -/
theorem keepR_eq_canonical
    (p : ScalarLineNaturalResidualProcess E) :
    p.keepR = (canonical (E := E) p.rate).keepR := by
  funext a
  simpa [canonical, scalarKeep] using keepR_forced p a

/-- THEOREM 9: every natural process has the same carrier keep as its canonical
rate process. -/
theorem keepE_eq_canonical
    (p : ScalarLineNaturalResidualProcess E) :
    p.keepE = (canonical (E := E) p.rate).keepE := by
  funext r
  simpa [canonical, scalarKeep] using keepE_forced p r

/-- THEOREM 10: two natural processes with the same rate are extensionally the
same on scalar and carrier keep. -/
theorem extensional_eq_of_same_rate
    (p q : ScalarLineNaturalResidualProcess E)
    (h : p.rate = q.rate) :
    p.keepR = q.keepR ∧ p.keepE = q.keepE := by
  constructor
  · funext a
    rw [keepR_forced p a, keepR_forced q a, h]
  · funext r
    rw [keepE_forced p r, keepE_forced q r, h]

/-- Composition of natural residual processes.  The second process acts after
the first one. -/
def compose
    (p₂ p₁ : ScalarLineNaturalResidualProcess E) :
    ScalarLineNaturalResidualProcess E where
  keepR := p₂.keepR ∘ p₁.keepR
  keepE := p₂.keepE ∘ p₁.keepE
  real_naturality := by
    intro x a
    simp
    have h₁ : p₁.keepR (a * x) = p₁.keepR a * x := by
      simpa using p₁.real_naturality x a
    rw [h₁]
    simpa using p₂.real_naturality x (p₁.keepR a)
  carrier_naturality := by
    intro x a
    simp
    rw [p₁.carrier_naturality x a]
    exact p₂.carrier_naturality x (p₁.keepR a)

/-- THEOREM 11: composing two natural processes composes rates by noisy-OR. -/
theorem compose_rate
    (p₂ p₁ : ScalarLineNaturalResidualProcess E) :
    (compose p₂ p₁).rate = satOrField p₁.rate p₂.rate := by
  have hkeep :
      (compose p₂ p₁).keepR 1 =
        (1 - p₂.rate) * (1 - p₁.rate) := by
    simp [compose]
    rw [keepR_forced p₂ (p₁.keepR 1),
      keepR_one_eq_one_sub_rate p₁]
  calc
    (compose p₂ p₁).rate =
        1 - (compose p₂ p₁).keepR 1 := by
          rfl
    _ = 1 - ((1 - p₂.rate) * (1 - p₁.rate)) := by
          rw [hkeep]
    _ = satOrField p₁.rate p₂.rate := by
          unfold satOrField
          ring

/-- THEOREM 12: the composed carrier keep is the canonical keep at the
noisy-OR composed rate. -/
theorem compose_keepE_forced
    (p₂ p₁ : ScalarLineNaturalResidualProcess E) (r : E) :
    (compose p₂ p₁).keepE r =
      (1 - satOrField p₁.rate p₂.rate) • r := by
  rw [keepE_forced (compose p₂ p₁) r, compose_rate p₂ p₁]

/-- THEOREM 13: the composed trace is the canonical trace at the noisy-OR
composed rate. -/
theorem compose_traceE_forced
    (p₂ p₁ : ScalarLineNaturalResidualProcess E) (r : E) :
    complementTrace (compose p₂ p₁).keepE r =
      satOrField p₁.rate p₂.rate • r := by
  rw [traceE_forced (compose p₂ p₁) r, compose_rate p₂ p₁]

/-- Identity natural residual process. -/
def identity : ScalarLineNaturalResidualProcess E where
  keepR := fun x => x
  keepE := fun x => x
  real_naturality := by intro x a; rfl
  carrier_naturality := by intro x a; rfl

/-- THEOREM 14: identity process has rate zero. -/
theorem identity_rate :
    (identity (E := E)).rate = 0 := by
  unfold identity rate complementTrace
  simp

/-- Zero-keep natural residual process. -/
def zeroKeep : ScalarLineNaturalResidualProcess E where
  keepR := fun _ => 0
  keepE := fun _ => 0
  real_naturality := by intro x a; simp
  carrier_naturality := by intro x a; simp

/-- THEOREM 15: zero keep has rate one. -/
theorem zeroKeep_rate :
    (zeroKeep (E := E)).rate = 1 := by
  unfold zeroKeep rate complementTrace
  simp

end ScalarLineNaturalResidualProcess

open ScalarLineNaturalResidualProcess

/-- P739 certificate: carrier-natural residual processes are classified by
scalar rates, and their composition law is noisy-OR. -/
structure ScalarLineNaturalProcessClassificationCertificate
    (E : Type u) [AddCommGroup E] [Module ℝ E] : Prop where
  keepR_forced :
    ∀ p : ScalarLineNaturalResidualProcess E,
      ∀ a : ℝ, p.keepR a = (1 - p.rate) * a
  keepE_forced :
    ∀ p : ScalarLineNaturalResidualProcess E,
      ∀ r : E, p.keepE r = (1 - p.rate) • r
  traceE_forced :
    ∀ p : ScalarLineNaturalResidualProcess E,
      ∀ r : E, complementTrace p.keepE r = p.rate • r
  update_forced_relaxModule :
    ∀ p : ScalarLineNaturalResidualProcess E,
      ∀ target x : E,
        residualTransportUpdate p.keepE target x =
          relaxModule target p.rate x
  canonical_rate :
    ∀ sigma : ℝ, (canonical (E := E) sigma).rate = sigma
  process_extensional_by_rate :
    ∀ p q : ScalarLineNaturalResidualProcess E,
      p.rate = q.rate -> p.keepR = q.keepR ∧ p.keepE = q.keepE
  compose_rate :
    ∀ p₂ p₁ : ScalarLineNaturalResidualProcess E,
      (compose p₂ p₁).rate = satOrField p₁.rate p₂.rate
  compose_keepE_forced :
    ∀ p₂ p₁ : ScalarLineNaturalResidualProcess E,
      ∀ r : E,
        (compose p₂ p₁).keepE r =
          (1 - satOrField p₁.rate p₂.rate) • r
  compose_traceE_forced :
    ∀ p₂ p₁ : ScalarLineNaturalResidualProcess E,
      ∀ r : E,
        complementTrace (compose p₂ p₁).keepE r =
          satOrField p₁.rate p₂.rate • r
  identity_rate_zero :
    (identity (E := E)).rate = 0
  zero_keep_rate_one :
    (zeroKeep (E := E)).rate = 1
  scalar_line_natural_keep :
    ScalarLineNaturalKeepCertificate E

/-- THEOREM 16: every real module carrier has the natural-process
classification certificate. -/
theorem scalarLineNaturalProcessClassificationCertificate :
    ScalarLineNaturalProcessClassificationCertificate E where
  keepR_forced := keepR_forced
  keepE_forced := keepE_forced
  traceE_forced := traceE_forced
  update_forced_relaxModule := update_forced_relaxModule
  canonical_rate := canonical_rate
  process_extensional_by_rate := extensional_eq_of_same_rate
  compose_rate := compose_rate
  compose_keepE_forced := compose_keepE_forced
  compose_traceE_forced := compose_traceE_forced
  identity_rate_zero := identity_rate
  zero_keep_rate_one := zeroKeep_rate
  scalar_line_natural_keep := scalarLineNaturalKeepCertificate

end AffineRelaxation
end SaturationMonoid
