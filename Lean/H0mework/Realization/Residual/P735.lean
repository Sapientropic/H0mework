import H0mework.Realization.Residual.P734

/-!
# Proposition 735: residual conservation split

P734 states residual transport:

`r ↦ K r`.

This file lowers the root one step further.  A real effective process is a
conservative split of one residual into what is kept and what becomes trace:

`r = r_keep + r_trace`.

For scalar saturation:

`r_keep = (1 - sigma) • r`

`r_trace = sigma • r`.

The transport reading `r' = (1-sigma)r`, the affine reading
`x' = x + sigma(target-x)`, and the noisy-OR composition reading are all
projections of this conservation split.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u v

variable {K : Type u} [Field K]
variable {E : Type v} [AddCommGroup E] [Module K E]

/-- A residual split is a conservative decomposition of one residual into its
kept part and its trace/spent part. -/
structure ResidualSplit (keep trace : E -> E) : Prop where
  conserve : ∀ r : E, r = keep r + trace r

/-- The scalar trace/spent operator paired with `scalarKeep`. -/
def scalarTrace (sigma : K) : E -> E :=
  fun r : E => sigma • r

/-- THEOREM 1: scalar keep and scalar trace exactly conserve the residual. -/
theorem scalarKeep_scalarTrace_conserve
    (sigma : K) (r : E) :
    r = scalarKeep (K := K) (E := E) sigma r +
        scalarTrace (K := K) (E := E) sigma r := by
  unfold scalarKeep scalarTrace
  module

/-- THEOREM 2: scalar keep/trace form a residual split. -/
theorem scalarResidualSplit
    (sigma : K) :
    ResidualSplit
      (scalarKeep (K := K) (E := E) sigma)
      (scalarTrace (K := K) (E := E) sigma) where
  conserve := scalarKeep_scalarTrace_conserve sigma

/-- THEOREM 3: if a keep/trace pair conserves residual, then after the keep
transport update the original residual is the new residual plus the trace. -/
theorem residualSplit_update_conserves_trace
    {keep trace : E -> E}
    (hsplit : ResidualSplit keep trace)
    (target x : E) :
    target - x =
      (target - residualTransportUpdate keep target x) +
        trace (target - x) := by
  rw [residualTransportUpdate_residual]
  exact hsplit.conserve (target - x)

/-- THEOREM 4: scalar relaxation conserves the residual as
new-residual plus trace. -/
theorem scalarResidualSplit_relaxation_conserves_trace
    (target x : E) (sigma : K) :
    target - x =
      (target -
        residualTransportUpdate
          (scalarKeep (K := K) (E := E) sigma) target x) +
        scalarTrace (K := K) (E := E) sigma (target - x) := by
  exact residualSplit_update_conserves_trace
    (scalarResidualSplit (K := K) (E := E) sigma) target x

/-- THEOREM 5: the affine display of scalar residual splitting is current
state plus the trace. -/
theorem residualSplit_scalar_affine_trace_display
    (target x : E) (sigma : K) :
    residualTransportUpdate
        (scalarKeep (K := K) (E := E) sigma) target x =
      x + scalarTrace (K := K) (E := E) sigma (target - x) := by
  unfold residualTransportUpdate scalarKeep scalarTrace
  module

/-- THEOREM 6: therefore the scalar split display is exactly `relaxModule`. -/
theorem residualSplit_scalar_affine_trace_display_eq_relaxModule
    (target x : E) (sigma : K) :
    x + scalarTrace (K := K) (E := E) sigma (target - x) =
      relaxModule target sigma x := by
  unfold scalarTrace relaxModule
  rfl

/-- THEOREM 7: on the target-one scalar carrier, the trace display is exactly
`bumpSatField`. -/
theorem residualSplit_targetOne_trace_display_eq_bumpSat
    (h sigma : K) :
    h + scalarTrace (K := K) (E := K) sigma (1 - h) =
      bumpSatField h sigma := by
  unfold scalarTrace bumpSatField
  ring

/-- THEOREM 8: the target-one trace amount is exactly the increment. -/
theorem bumpSat_increment_eq_scalarTrace
    (h sigma : K) :
    bumpSatField h sigma - h =
      scalarTrace (K := K) (E := K) sigma (1 - h) := by
  unfold bumpSatField scalarTrace
  ring

/-- THEOREM 9: two scalar split steps compose by adding the first trace and
the second trace evaluated on the kept residual.  This is the split-level
origin of noisy-OR. -/
theorem scalarTrace_satOr_split
    (sigma₁ sigma₂ : K) (r : E) :
    scalarTrace (K := K) (E := E) (satOrField sigma₁ sigma₂) r =
      scalarTrace (K := K) (E := E) sigma₁ r +
        scalarTrace (K := K) (E := E) sigma₂
          (scalarKeep (K := K) (E := E) sigma₁ r) := by
  unfold scalarTrace scalarKeep satOrField
  module

/-- THEOREM 10: after two scalar steps, the original residual is the final
kept residual plus the accumulated trace. -/
theorem scalarResidualSplit_twoStep_conservation
    (sigma₁ sigma₂ : K) (r : E) :
    r =
      scalarKeep (K := K) (E := E) (satOrField sigma₁ sigma₂) r +
        (scalarTrace (K := K) (E := E) sigma₁ r +
          scalarTrace (K := K) (E := E) sigma₂
            (scalarKeep (K := K) (E := E) sigma₁ r)) := by
  rw [← scalarTrace_satOr_split (K := K) (E := E) sigma₁ sigma₂ r]
  exact scalarKeep_scalarTrace_conserve
    (K := K) (E := E) (satOrField sigma₁ sigma₂) r

/-- P735 certificate: the residual conservation split and its transport,
affine, target-one, and composition readings. -/
structure ResidualConservationSplitCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  scalar_split :
    ∀ sigma : K,
      ResidualSplit
        (scalarKeep (K := K) (E := E) sigma)
        (scalarTrace (K := K) (E := E) sigma)
  scalar_residual_conservation :
    ∀ sigma : K, ∀ r : E,
      r = scalarKeep (K := K) (E := E) sigma r +
          scalarTrace (K := K) (E := E) sigma r
  update_conserves_trace :
    ∀ keep trace : E -> E,
      ResidualSplit keep trace ->
        ∀ target x : E,
          target - x =
            (target - residualTransportUpdate keep target x) +
              trace (target - x)
  scalar_update_trace_conservation :
    ∀ target x : E, ∀ sigma : K,
      target - x =
        (target -
          residualTransportUpdate
            (scalarKeep (K := K) (E := E) sigma) target x) +
          scalarTrace (K := K) (E := E) sigma (target - x)
  scalar_affine_trace_display :
    ∀ target x : E, ∀ sigma : K,
      residualTransportUpdate
          (scalarKeep (K := K) (E := E) sigma) target x =
        x + scalarTrace (K := K) (E := E) sigma (target - x)
  scalar_trace_display_is_relaxModule :
    ∀ target x : E, ∀ sigma : K,
      x + scalarTrace (K := K) (E := E) sigma (target - x) =
        relaxModule target sigma x
  target_one_trace_display_is_bumpSat :
    ∀ h sigma : K,
      h + scalarTrace (K := K) (E := K) sigma (1 - h) =
        bumpSatField h sigma
  target_one_trace_is_increment :
    ∀ h sigma : K,
      bumpSatField h sigma - h =
        scalarTrace (K := K) (E := K) sigma (1 - h)
  composed_trace_law :
    ∀ sigma₁ sigma₂ : K, ∀ r : E,
      scalarTrace (K := K) (E := E)
          (satOrField sigma₁ sigma₂) r =
        scalarTrace (K := K) (E := E) sigma₁ r +
          scalarTrace (K := K) (E := E) sigma₂
            (scalarKeep (K := K) (E := E) sigma₁ r)
  two_step_conservation :
    ∀ sigma₁ sigma₂ : K, ∀ r : E,
      r =
        scalarKeep (K := K) (E := E)
            (satOrField sigma₁ sigma₂) r +
          (scalarTrace (K := K) (E := E) sigma₁ r +
            scalarTrace (K := K) (E := E) sigma₂
              (scalarKeep (K := K) (E := E) sigma₁ r))
  residual_transport_principle :
    ResidualTransportPrincipleCertificate K E

/-- THEOREM 11: every module carrier supports the residual conservation split;
`r = keep + trace` is the conservative root whose readings are P734 residual
transport, P731/P724 affine relaxation, target-one bumpSat, and noisy-OR
composition. -/
theorem residualConservationSplitCertificate :
    ResidualConservationSplitCertificate K E where
  scalar_split :=
    scalarResidualSplit
  scalar_residual_conservation :=
    scalarKeep_scalarTrace_conserve
  update_conserves_trace :=
    by
      intro keep trace hsplit target x
      exact residualSplit_update_conserves_trace hsplit target x
  scalar_update_trace_conservation :=
    scalarResidualSplit_relaxation_conserves_trace
  scalar_affine_trace_display :=
    residualSplit_scalar_affine_trace_display
  scalar_trace_display_is_relaxModule :=
    residualSplit_scalar_affine_trace_display_eq_relaxModule
  target_one_trace_display_is_bumpSat :=
    residualSplit_targetOne_trace_display_eq_bumpSat
  target_one_trace_is_increment :=
    bumpSat_increment_eq_scalarTrace
  composed_trace_law :=
    scalarTrace_satOr_split
  two_step_conservation :=
    scalarResidualSplit_twoStep_conservation
  residual_transport_principle :=
    residualTransportPrincipleCertificate

end AffineRelaxation
end SaturationMonoid
