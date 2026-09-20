import H0mework.Physics.SourceFormation.AuxiliaryAction

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliaryFields

open StageNineHolonomicField StageNineEnrichedProofFreeSource ProofFreeRicherAnholonomicSource
open StageNineFormNativeP286GaugeYangMillsReadout StageNineFormNativeGaugeAuxiliaryVariation
open StageNineDiracDualFormNativeMotherAction StageNineGlobalIntegratedAction
open StageNineFormNativeGaugeWedge FullAuxiliary

noncomputable section

abbrev AuxiliaryField := BasePoint → FormNativeP286GaugeTwoForm

def replaceAuxiliary (field : StageNineHolonomicConfiguration) (auxiliary : AuxiliaryField) :
    StageNineHolonomicConfiguration := { field with gaugeAuxiliary := auxiliary }

theorem completion_ignores_auxiliary (source : SmoothUnifiedSource)
    (field : StageNineHolonomicConfiguration) (auxiliary : AuxiliaryField) :
    formNativeP286GaugeConstitutiveReadout source (replaceAuxiliary field auxiliary) =
      formNativeP286GaugeConstitutiveReadout source field := rfl

theorem completion_idempotent (source : SmoothUnifiedSource) (field : StageNineHolonomicConfiguration) :
    formNativeP286GaugeConstitutiveReadout source
        (formNativeP286GaugeConstitutiveReadout source field) =
      formNativeP286GaugeConstitutiveReadout source field := rfl

def Center (source : SmoothUnifiedSource) :=
  { field : StageNineHolonomicConfiguration // formNativeP286GaugeConstitutiveReadout source field = field }

/-- The center is computed by the original substitution. The separate full
auxiliary residual retains precisely the field data that substitution removes. -/
def wholeEquiv (source : SmoothUnifiedSource) :
    StageNineHolonomicConfiguration ≃ (Center source × AuxiliaryField) where
  toFun field :=
    (⟨formNativeP286GaugeConstitutiveReadout source field, completion_idempotent source field⟩,
      field.gaugeAuxiliary - (formNativeP286GaugeConstitutiveReadout source field).gaugeAuxiliary)
  invFun data := replaceAuxiliary data.1.val (data.1.val.gaugeAuxiliary + data.2)
  left_inv field := by
    apply StageNineHolonomicConfiguration.ext <;> try rfl
    change (formNativeP286GaugeConstitutiveReadout source field).gaugeAuxiliary +
      (field.gaugeAuxiliary - (formNativeP286GaugeConstitutiveReadout source field).gaugeAuxiliary) = _
    abel
  right_inv data := by
    rcases data with ⟨center, residual⟩
    apply Prod.ext
    · apply Subtype.ext
      change formNativeP286GaugeConstitutiveReadout source
        (replaceAuxiliary center.val (center.val.gaugeAuxiliary + residual)) = center.val
      rw [completion_ignores_auxiliary, center.property]
    · change center.val.gaugeAuxiliary + residual -
        (formNativeP286GaugeConstitutiveReadout source
          (replaceAuxiliary center.val (center.val.gaugeAuxiliary + residual))).gaugeAuxiliary = residual
      rw [completion_ignores_auxiliary, center.property]
      abel

theorem same_complete_coframe (source : SmoothUnifiedSource) (field : StageNineHolonomicConfiguration) :
    ((wholeEquiv source field).1.val).coframe = field.coframe := rfl

/-- Exact current-epoch action on the generated complete center and full
residual coordinates. The signed term is retained without positivity claims. -/
theorem action_in_generated_fields (source : SmoothUnifiedSource) (chart : StageNineChart)
    (field : StageNineHolonomicConfiguration) (nondegenerate : field.Nondegenerate) (point : BasePoint) :
    let data := wholeEquiv source field
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
        (toContinuumPointField field point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
        (toContinuumPointField data.1.val point) -
      (1 / 2 : ℝ) * formNativeP286GaugeWedgeCoefficient (data.2 point)
        (formNativeP286BlockwiseConstitutive (data.1.val.coframe point)
          ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings source).weakCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ) (data.2 point)) :=
  configuration_decomposition source chart field nondegenerate point

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliaryFields
