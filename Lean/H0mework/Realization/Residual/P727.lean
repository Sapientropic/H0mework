import H0mework.Realization.Residual.P726

/-!
# Proposition 727: linear face projections produce the common residual core

P726 proves that a supplied common residual projection core forces all projected
face dynamics to share one residual law.  This file removes the remaining
`step_commutes` burden for the important linear case.

Given a shared face carrier `E`, a common core `Core`, a linear projection
`π_face : E →ₗ[K] Core` for each face, and a face-local target whose projection
is the common target, the face-local update

`x ↦ relaxModule (faceTarget face) sigma x`

automatically commutes with the common core relaxation.  Hence it constructs a
`CommonResidualProjectionCore` and inherits the P726 residual, noisy-OR,
commutativity, synchronization, and scalar-energy laws.
-/

noncomputable section

set_option linter.checkUnivs false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

universe u v w z

variable {K : Type u} {E : Type z} {Core : Type v} {Face : Type w}
variable [Field K]
variable [AddCommGroup E] [Module K E]
variable [AddCommGroup Core] [Module K Core]

/-- A concrete producer surface for P726: all faces live on one module carrier,
each face has a local target, and each face has a linear projection into one
common core target. -/
structure LinearProjectedFaceFamily
    (K : Type u) (E : Type z) (Core : Type v) (Face : Type w)
    [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup Core] [Module K Core] where
  target : Core
  faceTarget : Face -> E
  toCore : Face -> E →ₗ[K] Core
  target_commutes : ∀ face : Face, toCore face (faceTarget face) = target

/-- THEOREM 1: a linear face projection transports the face-local relaxation
to the common-core relaxation whenever the face target projects to the common
target. -/
theorem linearProjectedFace_step_commutes
    (F : LinearProjectedFaceFamily K E Core Face)
    (face : Face) (sigma : K) (x : E) :
    F.toCore face (relaxModule (F.faceTarget face) sigma x) =
      relaxModule F.target sigma (F.toCore face x) := by
  calc
    F.toCore face (relaxModule (F.faceTarget face) sigma x)
        = relaxModule (F.toCore face (F.faceTarget face)) sigma
            (F.toCore face x) := by
          exact linearMap_relaxModule_commute (K := K)
            (F.toCore face) (F.faceTarget face) x sigma
    _ = relaxModule F.target sigma (F.toCore face x) := by
          rw [F.target_commutes face]

/-- The P727 producer coerced into the P726 common residual core. -/
def LinearProjectedFaceFamily.toCommonResidualProjectionCore
    (F : LinearProjectedFaceFamily K E Core Face) :
    CommonResidualProjectionCore K Core Face where
  Carrier := fun _ => E
  target := F.target
  toCore := fun face x => F.toCore face x
  step := fun face sigma x => relaxModule (F.faceTarget face) sigma x
  step_commutes := by
    intro face sigma x
    exact linearProjectedFace_step_commutes F face sigma x

/-- The residual readout produced directly by a linear projected face family. -/
def linearProjectedFaceResidual
    (F : LinearProjectedFaceFamily K E Core Face)
    (face : Face) (x : E) : Core :=
  F.target - F.toCore face x

/-- THEOREM 2: every linear projected face family has the P726 projected
residual normal form. -/
theorem linearProjectedFace_projectedResidual_step_eq
    (F : LinearProjectedFaceFamily K E Core Face)
    (face : Face) (sigma : K) (x : E) :
    linearProjectedFaceResidual F face
        (relaxModule (F.faceTarget face) sigma x) =
      (1 - sigma) •
        linearProjectedFaceResidual F face x := by
  unfold linearProjectedFaceResidual
  rw [linearProjectedFace_step_commutes F face sigma x]
  exact target_sub_relaxModule F.target sigma (F.toCore face x)

/-- THEOREM 3: equal common-core projections stay equal after same-rate
face-local relaxation. -/
theorem linearProjectedFace_sameProjection_stepsTogether
    (F : LinearProjectedFaceFamily K E Core Face)
    {face₁ face₂ : Face}
    (sigma : K) (x₁ x₂ : E)
    (hcore : F.toCore face₁ x₁ = F.toCore face₂ x₂) :
    F.toCore face₁ (relaxModule (F.faceTarget face₁) sigma x₁) =
      F.toCore face₂ (relaxModule (F.faceTarget face₂) sigma x₂) := by
  exact commonCore_same_projection_step
    F.toCommonResidualProjectionCore sigma x₁ x₂ hcore

/-- THEOREM 4: same-face two-step relaxation is noisy-OR after projection to
the common core. -/
theorem linearProjectedFace_sameFace_noisyOr_onCore
    (F : LinearProjectedFaceFamily K E Core Face)
    (face : Face) (x : E) (sigma₁ sigma₂ : K) :
    F.toCore face
        (relaxModule (F.faceTarget face) sigma₂
          (relaxModule (F.faceTarget face) sigma₁ x)) =
      F.toCore face
        (relaxModule (F.faceTarget face) (satOrField sigma₁ sigma₂) x) := by
  exact commonCore_sameFace_noisyOr
    F.toCommonResidualProjectionCore face x sigma₁ sigma₂

/-- THEOREM 5: same-face relaxation steps commute after projection to the
common core. -/
theorem linearProjectedFace_sameFace_commutes_onCore
    (F : LinearProjectedFaceFamily K E Core Face)
    (face : Face) (x : E) (sigma₁ sigma₂ : K) :
    F.toCore face
        (relaxModule (F.faceTarget face) sigma₂
          (relaxModule (F.faceTarget face) sigma₁ x)) =
      F.toCore face
        (relaxModule (F.faceTarget face) sigma₁
          (relaxModule (F.faceTarget face) sigma₂ x)) := by
  exact commonCore_sameFace_commutes
    F.toCommonResidualProjectionCore face x sigma₁ sigma₂

/-- THEOREM 6: if a face projection is injective, noisy-OR composition holds
on that face carrier. -/
theorem linearProjectedFace_sameFace_noisyOr_of_injective
    (F : LinearProjectedFaceFamily K E Core Face)
    (face : Face)
    (hinj : Function.Injective (F.toCore face))
    (x : E) (sigma₁ sigma₂ : K) :
    relaxModule (F.faceTarget face) sigma₂
        (relaxModule (F.faceTarget face) sigma₁ x) =
      relaxModule (F.faceTarget face) (satOrField sigma₁ sigma₂) x := by
  exact commonFace_noisyOr_of_injective
    F.toCommonResidualProjectionCore face hinj x sigma₁ sigma₂

/-- THEOREM 7: if a face projection is injective, same-face relaxation steps
commute on that face carrier. -/
theorem linearProjectedFace_sameFace_commutes_of_injective
    (F : LinearProjectedFaceFamily K E Core Face)
    (face : Face)
    (hinj : Function.Injective (F.toCore face))
    (x : E) (sigma₁ sigma₂ : K) :
    relaxModule (F.faceTarget face) sigma₂
        (relaxModule (F.faceTarget face) sigma₁ x) =
      relaxModule (F.faceTarget face) sigma₁
        (relaxModule (F.faceTarget face) sigma₂ x) := by
  exact commonFace_commutes_of_injective
    F.toCommonResidualProjectionCore face hinj x sigma₁ sigma₂

/-! ## Real scalar projected energy -/

/-- Squared residual energy produced directly by a real scalar linear projected
face family. -/
def linearProjectedFaceScalarEnergy
    {E : Type z} {Face : Type w}
    [AddCommGroup E] [Module ℝ E]
    (F : LinearProjectedFaceFamily ℝ E ℝ Face)
    (face : Face) (x : E) : ℝ :=
  (linearProjectedFaceResidual F face x) ^ 2

/-- THEOREM 8: on a real scalar common core, a linear projected face family
inherits the P726 projected residual-energy law. -/
theorem linearProjectedFace_scalarEnergy_step_eq
    {E : Type z} {Face : Type w}
    [AddCommGroup E] [Module ℝ E]
    (F : LinearProjectedFaceFamily ℝ E ℝ Face)
    (face : Face) (sigma : ℝ) (x : E) :
    linearProjectedFaceScalarEnergy F face
        (relaxModule (F.faceTarget face) sigma x) =
      (1 - sigma) ^ 2 *
        linearProjectedFaceScalarEnergy F face x := by
  unfold linearProjectedFaceScalarEnergy
  rw [linearProjectedFace_projectedResidual_step_eq F face sigma x]
  ring

/-! ## Certificates -/

/-- P727 certificate: a linear projected face family is a concrete producer of
the P726 common residual projection core. -/
structure LinearProjectedFaceFamilyCertificate
    (F : LinearProjectedFaceFamily K E Core Face) : Prop where
  step_commutes :
    ∀ (face : Face) (sigma : K) (x : E),
      F.toCore face (relaxModule (F.faceTarget face) sigma x) =
        relaxModule F.target sigma (F.toCore face x)
  common_core :
    CommonResidualProjectionCoreCertificate F.toCommonResidualProjectionCore
  projected_residual_normal_form :
    ∀ (face : Face) (sigma : K) (x : E),
      linearProjectedFaceResidual F face
          (relaxModule (F.faceTarget face) sigma x) =
        (1 - sigma) •
          linearProjectedFaceResidual F face x
  same_projection_steps_together :
    ∀ {face₁ face₂ : Face}
      (sigma : K) (x₁ x₂ : E),
      F.toCore face₁ x₁ = F.toCore face₂ x₂ ->
        F.toCore face₁ (relaxModule (F.faceTarget face₁) sigma x₁) =
          F.toCore face₂ (relaxModule (F.faceTarget face₂) sigma x₂)
  same_face_noisy_or_on_core :
    ∀ (face : Face) (x : E) (sigma₁ sigma₂ : K),
      F.toCore face
          (relaxModule (F.faceTarget face) sigma₂
            (relaxModule (F.faceTarget face) sigma₁ x)) =
        F.toCore face
          (relaxModule (F.faceTarget face) (satOrField sigma₁ sigma₂) x)
  same_face_commutes_on_core :
    ∀ (face : Face) (x : E) (sigma₁ sigma₂ : K),
      F.toCore face
          (relaxModule (F.faceTarget face) sigma₂
            (relaxModule (F.faceTarget face) sigma₁ x)) =
        F.toCore face
          (relaxModule (F.faceTarget face) sigma₁
            (relaxModule (F.faceTarget face) sigma₂ x))
  same_face_noisy_or_of_injective :
    ∀ (face : Face)
      (_ : Function.Injective (F.toCore face))
      (x : E) (sigma₁ sigma₂ : K),
      relaxModule (F.faceTarget face) sigma₂
          (relaxModule (F.faceTarget face) sigma₁ x) =
        relaxModule (F.faceTarget face) (satOrField sigma₁ sigma₂) x
  same_face_commutes_of_injective :
    ∀ (face : Face)
      (_ : Function.Injective (F.toCore face))
      (x : E) (sigma₁ sigma₂ : K),
      relaxModule (F.faceTarget face) sigma₂
          (relaxModule (F.faceTarget face) sigma₁ x) =
        relaxModule (F.faceTarget face) sigma₁
          (relaxModule (F.faceTarget face) sigma₂ x)

/-- THEOREM 9: every linear projected face family supplies the concrete common
core certificate. -/
theorem linearProjectedFaceFamilyCertificate
    (F : LinearProjectedFaceFamily K E Core Face) :
    LinearProjectedFaceFamilyCertificate F where
  step_commutes :=
    linearProjectedFace_step_commutes F
  common_core :=
    commonResidualProjectionCoreCertificate F.toCommonResidualProjectionCore
  projected_residual_normal_form :=
    linearProjectedFace_projectedResidual_step_eq F
  same_projection_steps_together := by
    intro face₁ face₂ sigma x₁ x₂ hcore
    exact linearProjectedFace_sameProjection_stepsTogether
      F sigma x₁ x₂ hcore
  same_face_noisy_or_on_core :=
    linearProjectedFace_sameFace_noisyOr_onCore F
  same_face_commutes_on_core :=
    linearProjectedFace_sameFace_commutes_onCore F
  same_face_noisy_or_of_injective :=
    linearProjectedFace_sameFace_noisyOr_of_injective F
  same_face_commutes_of_injective :=
    linearProjectedFace_sameFace_commutes_of_injective F

/-- P727 scalar certificate: a real scalar common core inherits projected
energy dissipation from a linear projected face family. -/
structure LinearProjectedFaceFamilyScalarEnergyCertificate
    {E : Type z} {Face : Type w}
    [AddCommGroup E] [Module ℝ E]
    (F : LinearProjectedFaceFamily ℝ E ℝ Face) : Prop where
  linear_projected_faces :
    LinearProjectedFaceFamilyCertificate F
  scalar_projected_energy_step :
    ∀ (face : Face) (sigma : ℝ) (x : E),
      linearProjectedFaceScalarEnergy F face
          (relaxModule (F.faceTarget face) sigma x) =
        (1 - sigma) ^ 2 *
          linearProjectedFaceScalarEnergy F face x

/-- THEOREM 10: every real scalar linear projected face family supplies the
projected energy certificate. -/
theorem linearProjectedFaceFamilyScalarEnergyCertificate
    {E : Type z} {Face : Type w}
    [AddCommGroup E] [Module ℝ E]
    (F : LinearProjectedFaceFamily ℝ E ℝ Face) :
    LinearProjectedFaceFamilyScalarEnergyCertificate F where
  linear_projected_faces :=
    linearProjectedFaceFamilyCertificate F
  scalar_projected_energy_step :=
    linearProjectedFace_scalarEnergy_step_eq F

end AffineRelaxation
end SaturationMonoid
