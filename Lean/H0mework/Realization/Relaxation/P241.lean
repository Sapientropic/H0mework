import H0mework.Realization.RelaxationFlow.P240

/-!
# Proposition 241: target transport for module-valued relaxation

P228/P231 identify the obstruction for raw cross-target composition.  This file
adds the corresponding positive law: changing targets is legitimate when it is
done by an explicit translation transport.

For module-valued relaxation,

`relaxModule target sigma x = x + sigma • (target - x)`,

translation by `target₂ - target₁` conjugates the `target₁` dynamics to the
`target₂` dynamics.  Thus cross-target steps do not commute by default, but
same-target noisy-OR composition is preserved after transporting into a common
target chart.

Boundary: this is affine translation transport in a module carrier.  It is not
yet gauge transport, parallel transport on a bundle, tensor geometry, or a
physical connection.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Translation transport -/

/-- Translate a module-valued state by a carrier displacement. -/
def translateModule {E : Type*} [AddCommGroup E] (delta : E) (x : E) : E :=
  x + delta

@[simp]
theorem translateModule_zero
    {E : Type*} [AddCommGroup E] (x : E) :
    translateModule (0 : E) x = x := by
  simp [translateModule]

/-- Translations compose by adding displacements. -/
theorem translateModule_comp
    {E : Type*} [AddCommGroup E] (delta1 delta2 x : E) :
    translateModule delta2 (translateModule delta1 x) =
      translateModule (delta1 + delta2) x := by
  simp [translateModule, add_assoc]

/-- Translating by the opposite displacement is inverse to translation. -/
theorem translateModule_left_inverse
    {E : Type*} [AddCommGroup E] (delta x : E) :
    translateModule (-delta) (translateModule delta x) = x := by
  simp [translateModule, add_assoc]

/-- The symmetric inverse law for translations. -/
theorem translateModule_right_inverse
    {E : Type*} [AddCommGroup E] (delta x : E) :
    translateModule delta (translateModule (-delta) x) = x := by
  simp [translateModule, add_assoc]

/-! ## Transporting relaxation between target charts -/

/-- Explicit target transport: translation by `target₂ - target₁` conjugates
relaxation toward `target₁` to relaxation toward `target₂`. -/
theorem relaxModule_transport_conjugate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target1 target2 x : E) (sigma : K) :
    translateModule (target2 - target1)
        (relaxModule target1 sigma
          (translateModule (target1 - target2) x)) =
      relaxModule target2 sigma x := by
  unfold translateModule relaxModule
  module

/-- The same transport identity, oriented from `target₂` back to `target₁`. -/
theorem relaxModule_transport_conjugate_symm
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target1 target2 x : E) (sigma : K) :
    translateModule (target1 - target2)
        (relaxModule target2 sigma
          (translateModule (target2 - target1) x)) =
      relaxModule target1 sigma x := by
  exact relaxModule_transport_conjugate target2 target1 x sigma

/-- After transporting into a common target chart, two same-target relaxations
again compose by noisy-OR. -/
theorem relaxModule_transport_compose
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target1 target2 x : E) (sigma1 sigma2 : K) :
    translateModule (target2 - target1)
        (relaxModule target1 sigma2
          (relaxModule target1 sigma1
            (translateModule (target1 - target2) x))) =
      relaxModule target2 (satOrField sigma1 sigma2) x := by
  rw [relaxModule_compose]
  exact relaxModule_transport_conjugate target1 target2 x
    (satOrField sigma1 sigma2)

/-- Transporting a target-local relaxation into a shared chart yields the same
result as relaxing directly toward the transported target. -/
theorem relaxModule_transport_then_direct
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sourceTarget target x : E) (sigma : K) :
    relaxModule target sigma x =
      translateModule (target - sourceTarget)
        (relaxModule sourceTarget sigma
          (translateModule (sourceTarget - target) x)) := by
  exact (relaxModule_transport_conjugate sourceTarget target x sigma).symm

/-- A named certificate for the affine target-transport law.

This keeps the positive transport law separate from the raw cross-target
commutator obstruction in P228/P231. -/
structure ModuleTargetTransportCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  conjugates :
    ∀ target1 target2 x : E, ∀ sigma : K,
      translateModule (target2 - target1)
          (relaxModule target1 sigma
            (translateModule (target1 - target2) x)) =
        relaxModule target2 sigma x
  composes_after_transport :
    ∀ target1 target2 x : E, ∀ sigma1 sigma2 : K,
      translateModule (target2 - target1)
          (relaxModule target1 sigma2
            (relaxModule target1 sigma1
              (translateModule (target1 - target2) x))) =
        relaxModule target2 (satOrField sigma1 sigma2) x

/-- Module-valued affine relaxation supplies the target-transport certificate. -/
theorem moduleTargetTransportCertificate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    ModuleTargetTransportCertificate K E where
  conjugates := relaxModule_transport_conjugate
  composes_after_transport := relaxModule_transport_compose


end AffineRelaxation
end SaturationMonoid
