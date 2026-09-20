import H0mework.Realization.Residual.P737

/-!
# Proposition 738: scalar-line naturality forces scalar keep

P737 proves that, once a keep operator `K` is given, the conservative trace is
forced to be `r - K r`.

This file removes the next degree of freedom.  If a keep operator on an
arbitrary carrier is natural with respect to every scalar line

`a ↦ a • x`,

then it is not an arbitrary operator at all.  It is forced by the one-dimensional
scalar readout `keepR 1`:

`keepE r = (keepR 1) • r`.

If the scalar trace readout is `sigma`, i.e.

`complementTrace keepR 1 = sigma`,

then the keep is forced to be `(1-sigma) • r`, the trace is forced to be
`sigma • r`, and the affine display is forced back to `relaxModule` and
target-one `bumpSatField`.

Thus P737 says trace has no choice once keep is known; P738 says keep has no
operator-level freedom once carrier-naturality and scalar rate readout are
known.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- A keep operator on `E` is scalar-line natural over a scalar keep `keepR`
when every line probe `a ↦ a • x` commutes with keep. -/
def ScalarLineNaturality
    (keepR : ℝ -> ℝ) (keepE : E -> E) : Prop :=
  ∀ (x : E) (a : ℝ), keepE (a • x) = (keepR a) • x

/-- THEOREM 1: scalar-line naturality forces every keep operator to be scalar,
with scalar coefficient read from the one-dimensional carrier. -/
theorem scalarLineNaturality_keep_forced_scalar
    {keepR : ℝ -> ℝ} {keepE : E -> E}
    (hnat : ScalarLineNaturality keepR keepE)
    (r : E) :
    keepE r = (keepR 1) • r := by
  have h := hnat r 1
  simpa using h

/-- THEOREM 2: on the scalar carrier itself, scalar-line naturality forces
`keepR` to be multiplication by `keepR 1`. -/
theorem scalarLineNaturality_real_keep_forced_scalar
    {keepR : ℝ -> ℝ}
    (hnat : ScalarLineNaturality (E := ℝ) keepR keepR)
    (a : ℝ) :
    keepR a = (keepR 1) • a := by
  have h := hnat a 1
  simpa using h

/-- THEOREM 3: the P737 complement trace is therefore forced to be scalar
trace with coefficient `1 - keepR 1`. -/
theorem scalarLineNaturality_trace_forced_scalar
    {keepR : ℝ -> ℝ} {keepE : E -> E}
    (hnat : ScalarLineNaturality keepR keepE)
    (r : E) :
    complementTrace keepE r = (1 - keepR 1) • r := by
  unfold complementTrace
  rw [scalarLineNaturality_keep_forced_scalar hnat r]
  module

/-- THEOREM 4: if the scalar trace readout is `sigma`, the keep factor is
forced to be `1 - sigma`. -/
theorem scalarLineNaturality_keep_forced_by_traceReadout
    {keepR : ℝ -> ℝ} {keepE : E -> E}
    (hnat : ScalarLineNaturality keepR keepE)
    {sigma : ℝ}
    (hrate : complementTrace keepR (1 : ℝ) = sigma)
    (r : E) :
    keepE r = (1 - sigma) • r := by
  have hk : keepR 1 = 1 - sigma := by
    rw [← hrate]
    unfold complementTrace
    ring
  calc
    keepE r = (keepR 1) • r :=
      scalarLineNaturality_keep_forced_scalar hnat r
    _ = (1 - sigma) • r := by rw [hk]

/-- THEOREM 5: if the scalar trace readout is `sigma`, the trace side is
forced to be `sigma • r`. -/
theorem scalarLineNaturality_trace_forced_by_traceReadout
    {keepR : ℝ -> ℝ} {keepE : E -> E}
    (hnat : ScalarLineNaturality keepR keepE)
    {sigma : ℝ}
    (hrate : complementTrace keepR (1 : ℝ) = sigma)
    (r : E) :
    complementTrace keepE r = sigma • r := by
  unfold complementTrace
  rw [scalarLineNaturality_keep_forced_by_traceReadout hnat hrate r]
  module

/-- THEOREM 6: scalar-line naturality plus scalar trace readout forces the
operator residual-transport display to be the standard affine relaxation. -/
theorem scalarLineNaturality_residualTransportUpdate_forced_relaxModule
    {keepR : ℝ -> ℝ} {keepE : E -> E}
    (hnat : ScalarLineNaturality keepR keepE)
    {sigma : ℝ}
    (hrate : complementTrace keepR (1 : ℝ) = sigma)
    (target x : E) :
    residualTransportUpdate keepE target x =
      relaxModule target sigma x := by
  unfold residualTransportUpdate relaxModule
  rw [scalarLineNaturality_keep_forced_by_traceReadout
    hnat hrate (target - x)]
  module

/-- THEOREM 7: on the target-one scalar face, the same forced update is exactly
`bumpSatField`. -/
theorem scalarLineNaturality_targetOne_forced_bumpSat
    {keepR : ℝ -> ℝ}
    (hnat : ScalarLineNaturality (E := ℝ) keepR keepR)
    {sigma : ℝ}
    (hrate : complementTrace keepR (1 : ℝ) = sigma)
    (x : ℝ) :
    residualTransportUpdate keepR (1 : ℝ) x =
      bumpSatField x sigma := by
  rw [scalarLineNaturality_residualTransportUpdate_forced_relaxModule
    (E := ℝ) hnat hrate (1 : ℝ) x]
  unfold relaxModule bumpSatField
  ring

/-- P738 certificate: scalar-line naturality forces arbitrary keep operators to
collapse to scalar keep, and scalar trace readout recovers the P736/P737
canonical split. -/
structure ScalarLineNaturalKeepCertificate
    (E : Type u) [AddCommGroup E] [Module ℝ E] : Prop where
  keep_forced_by_scalar_readout :
    ∀ (keepR : ℝ -> ℝ) (keepE : E -> E),
      ScalarLineNaturality keepR keepE ->
      ∀ r : E, keepE r = (keepR 1) • r
  real_keep_forced_by_scalar_readout :
    ∀ keepR : ℝ -> ℝ,
      ScalarLineNaturality (E := ℝ) keepR keepR ->
      ∀ a : ℝ, keepR a = (keepR 1) • a
  trace_forced_by_scalar_readout :
    ∀ (keepR : ℝ -> ℝ) (keepE : E -> E),
      ScalarLineNaturality keepR keepE ->
      ∀ r : E, complementTrace keepE r = (1 - keepR 1) • r
  keep_forced_by_trace_readout :
    ∀ (keepR : ℝ -> ℝ) (keepE : E -> E) (sigma : ℝ),
      ScalarLineNaturality keepR keepE ->
      complementTrace keepR (1 : ℝ) = sigma ->
      ∀ r : E, keepE r = (1 - sigma) • r
  trace_forced_by_trace_readout :
    ∀ (keepR : ℝ -> ℝ) (keepE : E -> E) (sigma : ℝ),
      ScalarLineNaturality keepR keepE ->
      complementTrace keepR (1 : ℝ) = sigma ->
      ∀ r : E, complementTrace keepE r = sigma • r
  update_forced_relaxModule :
    ∀ (keepR : ℝ -> ℝ) (keepE : E -> E) (sigma : ℝ),
      ScalarLineNaturality keepR keepE ->
      complementTrace keepR (1 : ℝ) = sigma ->
      ∀ target x : E,
        residualTransportUpdate keepE target x =
          relaxModule target sigma x
  target_one_forced_bumpSat :
    ∀ (keepR : ℝ -> ℝ) (sigma x : ℝ),
      ScalarLineNaturality (E := ℝ) keepR keepR ->
      complementTrace keepR (1 : ℝ) = sigma ->
        residualTransportUpdate keepR (1 : ℝ) x =
          bumpSatField x sigma
  operator_complement :
    ResidualOperatorComplementCertificate ℝ E

/-- THEOREM 8: every real module carrier supports the scalar-line naturality
collapse certificate. -/
theorem scalarLineNaturalKeepCertificate :
    ScalarLineNaturalKeepCertificate E where
  keep_forced_by_scalar_readout := by
    intro keepR keepE hnat r
    exact scalarLineNaturality_keep_forced_scalar hnat r
  real_keep_forced_by_scalar_readout := by
    intro keepR hnat a
    exact scalarLineNaturality_real_keep_forced_scalar hnat a
  trace_forced_by_scalar_readout := by
    intro keepR keepE hnat r
    exact scalarLineNaturality_trace_forced_scalar hnat r
  keep_forced_by_trace_readout := by
    intro keepR keepE sigma hnat hrate r
    exact scalarLineNaturality_keep_forced_by_traceReadout hnat hrate r
  trace_forced_by_trace_readout := by
    intro keepR keepE sigma hnat hrate r
    exact scalarLineNaturality_trace_forced_by_traceReadout hnat hrate r
  update_forced_relaxModule := by
    intro keepR keepE sigma hnat hrate target x
    exact scalarLineNaturality_residualTransportUpdate_forced_relaxModule
      hnat hrate target x
  target_one_forced_bumpSat := by
    intro keepR sigma x hnat hrate
    exact scalarLineNaturality_targetOne_forced_bumpSat hnat hrate x
  operator_complement :=
    residualOperatorComplementCertificate

end AffineRelaxation
end SaturationMonoid
