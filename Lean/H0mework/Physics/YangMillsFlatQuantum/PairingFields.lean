import H0mework.Physics.YangMillsFlatQuantum.PairingResponse
import H0mework.Physics.YangMillsFlatQuantum.HistoryAlgebra
import H0mework.Realization.Feature.HilbertRealization

/-! The physical mother pairing supplies the old feature completion. The
source word action then extends by the existing completion consumer. -/

set_option autoImplicit false
open scoped InnerProductSpace

namespace SaturationMonoid.PhysicsCore.YangMills.FullPairing

open StageNineHolonomicField ProofFreeRicherAnholonomicSource Stage9DEF
open Flat.Quantum.History
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedComplexFeaturePerfectification

noncomputable section

def feature (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    Polynomial →ₗ[ℂ] Hilbert :=
  naturalCoordinates.toLinearMap.comp
    ((LinearMap.applyₗ (Compatibility.embed (Source.vector point))).comp
      (evaluate configuration).toLinearMap)

theorem feature_value (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (P : Polynomial) :
    feature configuration point P = operator (evaluate configuration P) (prepared point) :=
  (operator_coordinates _ _).symm

theorem feature_left (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (P Q : Polynomial) :
    operator (evaluate configuration P) (feature configuration point Q) =
      feature configuration point (P * Q) := by
  change operator (evaluate configuration P)
    (naturalCoordinates (evaluate configuration Q (Compatibility.embed (Source.vector point)))) = _
  rw [operator_coordinates]
  change naturalCoordinates (evaluate configuration P
    (evaluate configuration Q (Compatibility.embed (Source.vector point)))) =
      naturalCoordinates (evaluate configuration (P * Q) (Compatibility.embed (Source.vector point)))
  rw [map_mul]
  rfl

abbrev Space (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :=
  HilbertAmbient (feature configuration point)

def vector (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    Polynomial →ₗ[ℂ] Space configuration point :=
  canonicalHilbertMap (feature configuration point)

theorem physical_pair (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (P Q : Polynomial) :
    inner ℂ (vector configuration point P) (vector configuration point Q) =
      State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (Compatibility.responseMatrix (pairedMother (evaluate configuration P) (evaluate configuration Q))) := by
  rw [← (hilbertAmbientRealization (feature configuration point)).inner_map_map]
  simp only [vector, hilbertAmbientRealization_source_readback, feature_value]
  exact (source_gram _ _ _).symm

private def rangeAction (configuration : StageNineHolonomicConfiguration) (point : BasePoint)
    (P : Polynomial) :
    LinearMap.range (feature configuration point) →L[ℂ] LinearMap.range (feature configuration point) :=
  ((operator (evaluate configuration P)).domRestrict (LinearMap.range (feature configuration point))).codRestrict
    (LinearMap.range (feature configuration point)) (by
      rintro ⟨_, Q, rfl⟩
      exact ⟨P * Q, (feature_left configuration point P Q).symm⟩)

def fieldAction (configuration : StageNineHolonomicConfiguration) (point : BasePoint)
    (P : Polynomial) : Space configuration point →L[ℂ] Space configuration point :=
  (((UniformSpace.Completion.toComplₗᵢ : LinearMap.range (feature configuration point) →ₗᵢ[ℂ]
    Space configuration point).toContinuousLinearMap).comp (rangeAction configuration point P)).fromCompletion

theorem fieldAction_vector (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (P Q : Polynomial) :
    fieldAction configuration point P (vector configuration point Q) =
      vector configuration point (P * Q) := by
  change fieldAction configuration point P
    ((feature configuration point).rangeRestrict Q : LinearMap.range (feature configuration point)) = _
  rw [fieldAction, ContinuousLinearMap.fromCompletion_apply_coe]
  change (UniformSpace.Completion.toComplₗᵢ : LinearMap.range (feature configuration point) →ₗᵢ[ℂ]
    Space configuration point) (rangeAction configuration point P ((feature configuration point).rangeRestrict Q)) =
      (UniformSpace.Completion.toComplₗᵢ : LinearMap.range (feature configuration point) →ₗᵢ[ℂ]
        Space configuration point) ((feature configuration point).rangeRestrict (P * Q))
  congr 1
  apply Subtype.ext
  exact feature_left configuration point P Q

end
end SaturationMonoid.PhysicsCore.YangMills.FullPairing
