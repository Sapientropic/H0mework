import H0mework.Realization.Relaxation.P241

/-!
# Proposition 242: bundled certificate for the unified affine relaxation spine

The earlier proposition files prove the affine relaxation law piece by piece:

* same-target noisy-OR composition,
* active cross-target obstruction,
* explicit affine translation transport between target charts.

This file does not add a new physical interpretation.  It packages those
pieces into one small certificate so downstream notes can cite the certified
unified affine core without flattening every proof receipt into the foreground.

Boundary: this certificate is still about module-valued affine relaxation.  It
does not certify gauge/parallel transport, tensor geometry, Hamiltonian
generators, or Standard Model structure.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Unified affine relaxation certificate -/

/-- The certified algebraic spine of the unified affine relaxation equation
over an arbitrary module carrier.

The fields deliberately separate:

* local same-target composition,
* raw cross-target obstruction,
* the positive law that restores same-target composition after explicit target
  transport.

That separation is the important discipline: raw cross-target composition is
not silently collapsed; it must either expose the obstruction or pass through a
transport/gluing law. -/
structure UnifiedAffineRelaxationModuleCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  residual_law :
    ∀ target : E, ∀ sigma : K, ∀ x : E,
      target - relaxModule target sigma x = (1 - sigma) • (target - x)
  same_target_noisy_or :
    ∀ target x : E, ∀ sigma1 sigma2 : K,
      relaxModule target sigma2 (relaxModule target sigma1 x) =
        relaxModule target (satOrField sigma1 sigma2) x
  same_target_commutes :
    ∀ target x : E, ∀ sigma1 sigma2 : K,
      relaxModule target sigma2 (relaxModule target sigma1 x) =
        relaxModule target sigma1 (relaxModule target sigma2 x)
  same_target_associates :
    ∀ target x : E, ∀ sigma1 sigma2 sigma3 : K,
      relaxModule target sigma3
          (relaxModule target sigma2 (relaxModule target sigma1 x)) =
        relaxModule target (satOrField sigma1 (satOrField sigma2 sigma3)) x
  zero_rate_noop :
    ∀ target x : E,
      relaxModule target (0 : K) x = x
  one_rate_hits_target :
    ∀ target x : E,
      relaxModule target (1 : K) x = target
  target_absorbing :
    ∀ target : E, ∀ sigma : K,
      relaxModule target sigma target = target
  cross_target_commutator :
    ∀ target1 target2 x : E, ∀ sigma1 sigma2 : K,
      relaxModule target2 sigma2 (relaxModule target1 sigma1 x) -
          relaxModule target1 sigma1 (relaxModule target2 sigma2 x) =
        (sigma1 * sigma2) • (target2 - target1)
  transport_conjugates :
    ∀ target1 target2 x : E, ∀ sigma : K,
      translateModule (target2 - target1)
          (relaxModule target1 sigma
            (translateModule (target1 - target2) x)) =
        relaxModule target2 sigma x
  noisy_or_after_transport :
    ∀ target1 target2 x : E, ∀ sigma1 sigma2 : K,
      translateModule (target2 - target1)
          (relaxModule target1 sigma2
            (relaxModule target1 sigma1
              (translateModule (target1 - target2) x))) =
        relaxModule target2 (satOrField sigma1 sigma2) x

/-- The module-valued unified affine relaxation law supplies the bundled
certificate. -/
theorem unifiedAffineRelaxationModuleCertificate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    UnifiedAffineRelaxationModuleCertificate K E where
  residual_law := target_sub_relaxModule
  same_target_noisy_or := relaxModule_compose
  same_target_commutes := relaxModule_compose_comm
  same_target_associates := relaxModule_compose_assoc
  zero_rate_noop := relaxModule_zero
  one_rate_hits_target := relaxModule_one
  target_absorbing := relaxModule_target_absorbing
  cross_target_commutator := relaxModule_cross_target_commutator
  transport_conjugates := relaxModule_transport_conjugate
  noisy_or_after_transport := relaxModule_transport_compose


end AffineRelaxation
end SaturationMonoid
