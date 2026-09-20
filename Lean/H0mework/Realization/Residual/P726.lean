import H0mework.Realization.Relaxation.P725

/-!
# Proposition 726: a common residual projection core forces all face dynamics

P701-P703 identify finite diagonal/readout surfaces.  P722-P725 identify the
affine relaxation, target-chart, and Hamiltonian/SAT energy spine.

This file adds the abstract bridge that was still missing for the slogan
"information = energy = matter = mathematics = consciousness": it is not a
new singleton/readout theorem.  It is a common-core theorem.

If a family of faces projects to one core carrier and every face step commutes
with the same `relaxModule` step on that core, then every face has the same
projected residual normal form:

`target - core(step sigma x) = (1-sigma) • (target - core(x))`.

Two states on different faces with the same core projection stay synchronized
under the same rate.  Same-face composition is noisy-OR on the core, and when
the face projection is injective it is noisy-OR on the face itself.  On a real
scalar core, the projected residual energy scales by `(1-sigma)^2`.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

universe u v w z

/-- A family of faces shares a residual projection core when every face has a
projection into a common module carrier and each face-local step is transported
by the same `relaxModule` step on the core. -/
structure CommonResidualProjectionCore
    (K : Type u) (Core : Type v) (Face : Type w)
    [Field K] [AddCommGroup Core] [Module K Core] where
  Carrier : Face -> Type z
  target : Core
  toCore : ∀ face : Face, Carrier face -> Core
  step : ∀ face : Face, K -> Carrier face -> Carrier face
  step_commutes :
    ∀ (face : Face) (sigma : K) (x : Carrier face),
      toCore face (step face sigma x) =
        relaxModule target sigma (toCore face x)

variable {K : Type u} {Core : Type v} {Face : Type w}
variable [Field K] [AddCommGroup Core] [Module K Core]

/-! ## Linear projections naturally commute with relaxation -/

/-- THEOREM 0a: every linear projection transports affine relaxation to affine
relaxation of the projected target and projected state. -/
theorem linearMap_relaxModule_commute
    {E F : Type*} [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F]
    (π : E →ₗ[K] F) (target x : E) (sigma : K) :
    π (relaxModule target sigma x) =
      relaxModule (π target) sigma (π x) := by
  unfold relaxModule
  simp

/-- THEOREM 0b: the zero-target residual face is preserved by every linear
projection. -/
theorem linearMap_zeroTarget_relaxModule_commute
    {E F : Type*} [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F]
    (π : E →ₗ[K] F) (x : E) (sigma : K) :
    π (relaxModule 0 sigma x) =
      relaxModule 0 sigma (π x) := by
  simpa using linearMap_relaxModule_commute (K := K) π (0 : E) x sigma

/-- P726 base certificate: linear projections are producers of common
relaxation charts. -/
structure LinearProjectionRelaxModuleCommuteCertificate
    (K : Type u) [Field K] : Prop where
  linear_projection_commutes :
    ∀ {E F : Type*} [AddCommGroup E] [Module K E]
      [AddCommGroup F] [Module K F],
      ∀ (π : E →ₗ[K] F) (target x : E) (sigma : K),
        π (relaxModule target sigma x) =
          relaxModule (π target) sigma (π x)
  zero_target_linear_projection_commutes :
    ∀ {E F : Type*} [AddCommGroup E] [Module K E]
      [AddCommGroup F] [Module K F],
      ∀ (π : E →ₗ[K] F) (x : E) (sigma : K),
        π (relaxModule 0 sigma x) =
          relaxModule 0 sigma (π x)

/-- THEOREM 0c: every field supplies the linear projection commute
certificate. -/
theorem linearProjectionRelaxModuleCommuteCertificate :
    LinearProjectionRelaxModuleCommuteCertificate K where
  linear_projection_commutes := by
    intro E F _ _ _ _ π target x sigma
    exact linearMap_relaxModule_commute (K := K) π target x sigma
  zero_target_linear_projection_commutes := by
    intro E F _ _ _ _ π x sigma
    exact linearMap_zeroTarget_relaxModule_commute (K := K) π x sigma

/-- The residual read on a face through the common core projection. -/
def commonProjectedResidual
    (C : CommonResidualProjectionCore K Core Face)
    (face : Face) (x : C.Carrier face) : Core :=
  C.target - C.toCore face x

/-- THEOREM 1: every face has the same projected residual normal form. -/
theorem commonProjectedResidual_step_eq
    (C : CommonResidualProjectionCore K Core Face)
    (face : Face) (sigma : K) (x : C.Carrier face) :
    commonProjectedResidual C face (C.step face sigma x) =
      (1 - sigma) • commonProjectedResidual C face x := by
  unfold commonProjectedResidual
  rw [C.step_commutes face sigma x]
  exact target_sub_relaxModule C.target sigma (C.toCore face x)

/-- THEOREM 2: if two face states have the same core projection, the same rate
keeps them synchronized on the core. -/
theorem commonCore_same_projection_step
    (C : CommonResidualProjectionCore K Core Face)
    {face₁ face₂ : Face}
    (sigma : K)
    (x₁ : C.Carrier face₁) (x₂ : C.Carrier face₂)
    (hcore : C.toCore face₁ x₁ = C.toCore face₂ x₂) :
    C.toCore face₁ (C.step face₁ sigma x₁) =
      C.toCore face₂ (C.step face₂ sigma x₂) := by
  rw [C.step_commutes face₁ sigma x₁,
    C.step_commutes face₂ sigma x₂,
    hcore]

/-- THEOREM 3: on the common core, same-face two-step composition is noisy-OR. -/
theorem commonCore_sameFace_noisyOr
    (C : CommonResidualProjectionCore K Core Face)
    (face : Face) (x : C.Carrier face) (sigma₁ sigma₂ : K) :
    C.toCore face (C.step face sigma₂ (C.step face sigma₁ x)) =
      C.toCore face (C.step face (satOrField sigma₁ sigma₂) x) := by
  calc
    C.toCore face (C.step face sigma₂ (C.step face sigma₁ x))
        = relaxModule C.target sigma₂
            (C.toCore face (C.step face sigma₁ x)) := by
          rw [C.step_commutes face sigma₂ (C.step face sigma₁ x)]
    _ = relaxModule C.target sigma₂
            (relaxModule C.target sigma₁ (C.toCore face x)) := by
          rw [C.step_commutes face sigma₁ x]
    _ = relaxModule C.target (satOrField sigma₁ sigma₂)
            (C.toCore face x) := by
          exact relaxModule_compose C.target (C.toCore face x) sigma₁ sigma₂
    _ = C.toCore face (C.step face (satOrField sigma₁ sigma₂) x) := by
          rw [C.step_commutes face (satOrField sigma₁ sigma₂) x]

/-- THEOREM 4: on the common core, same-face steps commute. -/
theorem commonCore_sameFace_commutes
    (C : CommonResidualProjectionCore K Core Face)
    (face : Face) (x : C.Carrier face) (sigma₁ sigma₂ : K) :
    C.toCore face (C.step face sigma₂ (C.step face sigma₁ x)) =
      C.toCore face (C.step face sigma₁ (C.step face sigma₂ x)) := by
  calc
    C.toCore face (C.step face sigma₂ (C.step face sigma₁ x))
        = relaxModule C.target sigma₂
            (relaxModule C.target sigma₁ (C.toCore face x)) := by
          rw [C.step_commutes face sigma₂ (C.step face sigma₁ x),
            C.step_commutes face sigma₁ x]
    _ = relaxModule C.target sigma₁
            (relaxModule C.target sigma₂ (C.toCore face x)) := by
          exact relaxModule_compose_comm C.target (C.toCore face x) sigma₁ sigma₂
    _ = C.toCore face (C.step face sigma₁ (C.step face sigma₂ x)) := by
          rw [C.step_commutes face sigma₁ (C.step face sigma₂ x),
            C.step_commutes face sigma₂ x]

/-- THEOREM 5: if a face projection is injective, noisy-OR composition holds
on the face carrier itself. -/
theorem commonFace_noisyOr_of_injective
    (C : CommonResidualProjectionCore K Core Face)
    (face : Face)
    (hinj : Function.Injective (C.toCore face))
    (x : C.Carrier face) (sigma₁ sigma₂ : K) :
    C.step face sigma₂ (C.step face sigma₁ x) =
      C.step face (satOrField sigma₁ sigma₂) x :=
  hinj (commonCore_sameFace_noisyOr C face x sigma₁ sigma₂)

/-- THEOREM 6: if a face projection is injective, same-target steps commute on
the face carrier itself. -/
theorem commonFace_commutes_of_injective
    (C : CommonResidualProjectionCore K Core Face)
    (face : Face)
    (hinj : Function.Injective (C.toCore face))
    (x : C.Carrier face) (sigma₁ sigma₂ : K) :
    C.step face sigma₂ (C.step face sigma₁ x) =
      C.step face sigma₁ (C.step face sigma₂ x) :=
  hinj (commonCore_sameFace_commutes C face x sigma₁ sigma₂)

/-! ## Real scalar common-core energy -/

/-- Squared residual energy read through a real scalar common core. -/
def commonScalarProjectedResidualEnergy
    {Face : Type w}
    (C : CommonResidualProjectionCore ℝ ℝ Face)
    (face : Face) (x : C.Carrier face) : ℝ :=
  (commonProjectedResidual C face x) ^ 2

/-- THEOREM 7: on a real scalar common core, every face has the same projected
residual-energy scaling law. -/
theorem commonScalarProjectedResidualEnergy_step_eq
    {Face : Type w}
    (C : CommonResidualProjectionCore ℝ ℝ Face)
    (face : Face) (sigma : ℝ) (x : C.Carrier face) :
    commonScalarProjectedResidualEnergy C face (C.step face sigma x) =
      (1 - sigma) ^ 2 * commonScalarProjectedResidualEnergy C face x := by
  unfold commonScalarProjectedResidualEnergy
  rw [commonProjectedResidual_step_eq C face sigma x]
  ring

/-! ## Certificates -/

/-- P726 generic certificate for a fixed common residual projection core. -/
structure CommonResidualProjectionCoreCertificate
    (C : CommonResidualProjectionCore K Core Face) : Prop where
  projected_residual_normal_form :
    ∀ (face : Face) (sigma : K) (x : C.Carrier face),
      commonProjectedResidual C face (C.step face sigma x) =
        (1 - sigma) • commonProjectedResidual C face x
  same_projection_steps_together :
    ∀ {face₁ face₂ : Face}
      (sigma : K)
      (x₁ : C.Carrier face₁) (x₂ : C.Carrier face₂),
      C.toCore face₁ x₁ = C.toCore face₂ x₂ ->
        C.toCore face₁ (C.step face₁ sigma x₁) =
          C.toCore face₂ (C.step face₂ sigma x₂)
  same_face_noisy_or_on_core :
    ∀ (face : Face) (x : C.Carrier face) (sigma₁ sigma₂ : K),
      C.toCore face (C.step face sigma₂ (C.step face sigma₁ x)) =
        C.toCore face (C.step face (satOrField sigma₁ sigma₂) x)
  same_face_commutes_on_core :
    ∀ (face : Face) (x : C.Carrier face) (sigma₁ sigma₂ : K),
      C.toCore face (C.step face sigma₂ (C.step face sigma₁ x)) =
        C.toCore face (C.step face sigma₁ (C.step face sigma₂ x))
  same_face_noisy_or_of_injective :
    ∀ (face : Face)
      (_ : Function.Injective (C.toCore face))
      (x : C.Carrier face) (sigma₁ sigma₂ : K),
      C.step face sigma₂ (C.step face sigma₁ x) =
        C.step face (satOrField sigma₁ sigma₂) x
  same_face_commutes_of_injective :
    ∀ (face : Face)
      (_ : Function.Injective (C.toCore face))
      (x : C.Carrier face) (sigma₁ sigma₂ : K),
      C.step face sigma₂ (C.step face sigma₁ x) =
        C.step face sigma₁ (C.step face sigma₂ x)

/-- THEOREM 8: every common residual projection core supplies the generic
certificate. -/
theorem commonResidualProjectionCoreCertificate
    (C : CommonResidualProjectionCore K Core Face) :
    CommonResidualProjectionCoreCertificate C where
  projected_residual_normal_form :=
    commonProjectedResidual_step_eq C
  same_projection_steps_together := by
    intro face₁ face₂ sigma x₁ x₂ hcore
    exact commonCore_same_projection_step C sigma x₁ x₂ hcore
  same_face_noisy_or_on_core :=
    commonCore_sameFace_noisyOr C
  same_face_commutes_on_core :=
    commonCore_sameFace_commutes C
  same_face_noisy_or_of_injective :=
    commonFace_noisyOr_of_injective C
  same_face_commutes_of_injective :=
    commonFace_commutes_of_injective C

/-- P726 scalar certificate for a fixed real common residual projection core. -/
structure CommonScalarResidualProjectionCoreCertificate
    {Face : Type w}
    (C : CommonResidualProjectionCore ℝ ℝ Face) : Prop where
  generic_common_core :
    CommonResidualProjectionCoreCertificate C
  scalar_projected_energy_step :
    ∀ (face : Face) (sigma : ℝ) (x : C.Carrier face),
      commonScalarProjectedResidualEnergy C face (C.step face sigma x) =
        (1 - sigma) ^ 2 *
          commonScalarProjectedResidualEnergy C face x

/-- THEOREM 9: every real scalar common residual projection core supplies the
projected energy certificate. -/
theorem commonScalarResidualProjectionCoreCertificate
    {Face : Type w}
    (C : CommonResidualProjectionCore ℝ ℝ Face) :
    CommonScalarResidualProjectionCoreCertificate C where
  generic_common_core :=
    commonResidualProjectionCoreCertificate C
  scalar_projected_energy_step :=
    commonScalarProjectedResidualEnergy_step_eq C

end AffineRelaxation
end SaturationMonoid
