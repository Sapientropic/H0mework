import H0mework.Physics.QuantumFoundation.FoundationLineage
import H0mework.Physics.SpinPair.Actual

/-! The current actual descends through the original generated total bundle.
No background connection is substituted for its actual P286 connection. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9G.Foundation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalBundle StageNineGlobalConnection StageNineAssociatedBundles
open StageNineSpinMatterBundle StageNineFullMotherDescentAndTransport
open StageNineHolonomicField StageNineDynamicBreakingVacuum
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open Stage9C.Material.SpinPair DiracExteriorMatterAction

noncomputable section

def actualLocalMatter (chart : StageNineChart) (point : BasePoint) :
    DiracExteriorMatterCarrier :=
  totalDiracExteriorMatterRepresentation
    (generatedTotalTransition positiveSmoothUnifiedSource 0 chart point) (actual.matter point)

theorem actualLocalMatter_overlap (initial terminal : StageNineChart) (point : BasePoint) :
    actualLocalMatter terminal point =
      totalDiracExteriorMatterRepresentation
        (generatedTotalTransition positiveSmoothUnifiedSource initial terminal point)
        (actualLocalMatter initial point) := by
  unfold actualLocalMatter
  rw [← representation_mul_apply, generatedTotalTransition_cocycle]

theorem actualLocalMatter_zero (point : BasePoint) :
    actualLocalMatter 0 point = actual.matter point := by
  simp [actualLocalMatter]

def actualGlobalMatter (point : BasePoint) :
    PhysicalDiracMatterAssociatedBundle positiveSmoothUnifiedSource :=
  associatedLocalPoint totalDiracExteriorMatterRepresentation
    positiveSmoothUnifiedSource 0 point (actual.matter point)

theorem actualGlobalMatter_in_chart (chart : StageNineChart) (point : BasePoint) :
    actualGlobalMatter point =
      associatedLocalPoint totalDiracExteriorMatterRepresentation positiveSmoothUnifiedSource
        chart point (actualLocalMatter chart point) :=
  associatedLocalPoint_transition totalDiracExteriorMatterRepresentation
    positiveSmoothUnifiedSource 0 chart point (actual.matter point)

theorem actualGlobalMatter_section (point : BasePoint) :
    associatedBundleProjection totalDiracExteriorMatterRepresentation positiveSmoothUnifiedSource
      (actualGlobalMatter point) = point := rfl

def actualLocalPotential (chart : StageNineChart) (point : BasePoint)
    (direction : LorentzianIndex) : SU7MotherLieMatrix :=
  p286LieBlockEmbed (actual.gaugeConnection point direction) -
    if direction = 0 then
      (chartWeight chart * positiveSmoothUnifiedSource.continuousContactRate) •
        motherHyperchargeDirection
    else 0

theorem actualLocalPotential_zero (point : BasePoint) (direction : LorentzianIndex) :
    actualLocalPotential 0 point direction = p286LieBlockEmbed (actual.gaugeConnection point direction) := by
  simp [actualLocalPotential, chartWeight]

theorem actualPotential_adjoint (initial terminal : StageNineChart) (point : BasePoint)
    (direction : LorentzianIndex) :
    motherAdjointMatrix (generatedTransition positiveSmoothUnifiedSource initial terminal point)
        (p286LieBlockEmbed (actual.gaugeConnection point direction)) =
      (p286LieBlockEmbed (actual.gaugeConnection point direction) :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
  rw [motherAdjointMatrix, generatedTransition,
    (embeddedP286HyperchargeElement_commutes_p286LieBlockEmbed _ _).eq, Matrix.mul_assoc]
  change (p286LieBlockEmbed (actual.gaugeConnection point direction) :
    Matrix SU7MotherIndex SU7MotherIndex ℂ) *
    (((embeddedP286HyperchargeElement _ : SU7MotherGroup) *
      (embeddedP286HyperchargeElement _ : SU7MotherGroup)⁻¹ : SU7MotherGroup) :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) = _
  rw [mul_inv_cancel]
  simp

theorem actualLocalPotential_adjoint (initial terminal : StageNineChart) (point : BasePoint)
    (direction : LorentzianIndex) :
    motherAdjointMatrix (generatedTransition positiveSmoothUnifiedSource initial terminal point)
        (actualLocalPotential initial point direction) =
      (actualLocalPotential initial point direction : Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
  by_cases temporal : direction = 0
  · subst direction
    simp only [actualLocalPotential, ↓reduceIte]
    rw [show motherAdjointMatrix _ (_ - _) =
      motherAdjointMatrix
          (generatedTransition positiveSmoothUnifiedSource initial terminal point)
          (p286LieBlockEmbed (actual.gaugeConnection point 0)) -
        motherAdjointMatrix
          (generatedTransition positiveSmoothUnifiedSource initial terminal point)
          ((chartWeight initial * positiveSmoothUnifiedSource.continuousContactRate) •
            motherHyperchargeDirection) by
      simp [motherAdjointMatrix, Matrix.mul_sub, Matrix.sub_mul]]
    rw [actualPotential_adjoint, generatedTransition_adjoint_hyperchargeShift]
    rfl
  · simp only [actualLocalPotential, temporal, ↓reduceIte, sub_zero]
    exact actualPotential_adjoint initial terminal point direction

theorem actualLocalPotential_overlap (initial terminal : StageNineChart) (point : BasePoint)
    (direction : LorentzianIndex) :
    (actualLocalPotential terminal point direction : Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      motherAdjointMatrix (generatedTransition positiveSmoothUnifiedSource initial terminal point)
          (actualLocalPotential initial point direction) -
        (generatedTransitionLogDerivative positiveSmoothUnifiedSource initial terminal direction :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
  rw [actualLocalPotential_adjoint]
  apply congrArg Subtype.val (show actualLocalPotential terminal point direction =
    actualLocalPotential initial point direction -
      generatedTransitionLogDerivative positiveSmoothUnifiedSource initial terminal direction from ?_)
  by_cases temporal : direction = 0
  · subst direction
    simp [actualLocalPotential, generatedTransitionLogDerivative,
      generatedTransitionDerivativeCoefficient]
    module
  · simp [actualLocalPotential, generatedTransitionLogDerivative,
      generatedTransitionDerivativeCoefficient, temporal]

end
end SaturationMonoid.PhysicsCore.Stage9G.Foundation
