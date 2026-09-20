import H0mework.Physics.CoframeJets.CoframeFirstJet
import H0mework.Physics.Gauge.GlobalConnection

/-!
# Source-generated coframe as an actual holonomic first jet

The proof-free source stores only affine coframe coefficients.  This module
shows that Fréchet differentiation of its generated coframe field recovers
exactly its own pointwise jet at every point.  Therefore the generated Lorentz
connection is computed from the actual primitive coframe first jet, not from
an unrelated stored derivative receipt.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceGeneratedCoframeFirstJet

open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection

noncomputable section

set_option autoImplicit false

/-- The source coframe is exactly the canonical affine integration of its
origin jet. -/
theorem legacy_coframeAt_eq_affine_origin_jet
    (source : SmoothUnifiedSource) :
    source.legacy.coframeAt =
      affineCoframeFieldOfJet (source.legacy.jetAt 0) := by
  funext point internal coordinate
  change
    (1 : LorentzianCoframe) internal coordinate +
          ∑ direction : LorentzianIndex,
            source.legacy.coframeLinearCoefficient direction internal coordinate *
              point direction =
      ((1 : LorentzianCoframe) internal coordinate +
          ∑ direction : LorentzianIndex,
            source.legacy.coframeLinearCoefficient direction internal coordinate *
              (0 : BasePoint) direction) +
        ∑ direction : LorentzianIndex,
          source.legacy.coframeLinearCoefficient direction internal coordinate *
            point direction
  simp

/-- The genuine Fréchet first jet of the source-generated coframe equals the
source's derived pointwise jet at every point. -/
theorem holonomicCoframeFirstJetAt_legacy_coframeAt
    (source : SmoothUnifiedSource) (point : BasePoint) :
    holonomicCoframeFirstJetAt source.legacy.coframeAt point =
      source.legacy.jetAt point := by
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    rw [legacy_coframeAt_eq_affine_origin_jet]
    exact affineCoframeFieldOfJet_directionalDerivative
      (source.legacy.jetAt 0) point derivativeDirection internal coordinate

/-- The source-generated Lorentz connection is the spin connection of the
actual coframe-field first jet. -/
theorem generatedLorentzConnectionAt_eq_actualCoframeFirstJet
    (source : SmoothUnifiedSource) (point : BasePoint) :
    generatedLorentzConnectionAt source point =
      (holonomicCoframeFirstJetAt source.legacy.coframeAt point).lorentzSpinConnection := by
  rw [holonomicCoframeFirstJetAt_legacy_coframeAt]
  rfl

end

end SaturationMonoid.PhysicsCore.StageNineSourceGeneratedCoframeFirstJet
