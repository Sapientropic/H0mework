import H0mework.Physics.CompositeSpectrum.Action
import H0mework.Physics.DiracCovariance.Covariance
import Mathlib.LinearAlgebra.Trace

/-! Full incoming actions intertwine before products or dual evaluation.
Local Spin preserves the same primitive gauge connection; the full ordered
cubic therefore commutes with the original Spin matter action. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineGlobalBundle StageNineSpinMatterBundle
open StageNineDiracDualFormNativeLocalSpinAction StageNineDiracKineticLocalSpinCovariance
open Stage9C.Material.SpinPair Stage9DEF
open SU7ExteriorMatterRepresentation SU7ExteriorMatterGaugeCovariantJet
open SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

theorem ordered_product_intertwines (first second left right : Module.End ℂ DiracExteriorMatterCarrier)
    (frame : Source.Frame.Action)
    (first_eq : ∀ matter, first (frame matter) = frame (left matter))
    (second_eq : ∀ matter, second (frame matter) = frame (right matter))
    (matter : DiracExteriorMatterCarrier) :
    (first * second) (frame matter) = frame ((left * right) matter) := by
  change first (second (frame matter)) = frame (left (right matter))
  rw [second_eq, first_eq]

theorem alternatingProduct_intertwines
    (first second : Fin 3 → Module.End ℂ DiracExteriorMatterCarrier)
    (frame : Source.Frame.Action)
    (intertwines : ∀ axis matter, first axis (frame matter) = frame (second axis matter))
    (matter : DiracExteriorMatterCarrier) :
    alternatingProduct first (frame matter) = frame (alternatingProduct second matter) := by
  simp only [alternatingProduct, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.mul_apply, intertwines, map_smul, map_add, map_sub]

def fullGaugeCompositeAction (element : SU7MotherGroup) (point : BasePoint) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  alternatingProduct (fullGaugeCurvatureAction element point)

theorem fullGaugeCompositeAction_intertwines (element : SU7MotherGroup) (point : BasePoint)
    (matter : DiracExteriorMatterCarrier) :
    fullGaugeCompositeAction element point (Source.Frame.gaugeFrame element matter) =
      Source.Frame.gaugeFrame element (compositeAction point matter) := by
  apply alternatingProduct_intertwines
  intro axis value
  rw [incomingCurvatureAction_eq]
  exact fullGaugeCurvatureAction_actual element point axis value

theorem fullGaugeCompositeAction_eq_conj (element : SU7MotherGroup) (point : BasePoint) :
    fullGaugeCompositeAction element point =
      (Source.Frame.gaugeFrame element).conj (compositeAction point) := by
  apply LinearMap.ext
  intro matter
  obtain ⟨value, rfl⟩ := (Source.Frame.gaugeFrame element).surjective matter
  rw [fullGaugeCompositeAction_intertwines]
  simp [LinearEquiv.conj_apply]

theorem fullGaugeCompositeAction_independentDual (element : SU7MotherGroup) (point : BasePoint) :
    ((Runtime.configuration.conjugateMatter point).comp
      (Source.Frame.gaugeFrame element).symm.toLinearMap)
      (fullGaugeCompositeAction element point
        (Source.Frame.gaugeFrame element (Runtime.configuration.matter point))) =
      Runtime.configuration.conjugateMatter point
        (compositeAction point (Runtime.configuration.matter point)) := by
  rw [fullGaugeCompositeAction_intertwines]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem fullGaugeCompositeAction_trace (element : SU7MotherGroup) (point : BasePoint) :
    LinearMap.trace ℂ DiracExteriorMatterCarrier (fullGaugeCompositeAction element point) =
      LinearMap.trace ℂ DiracExteriorMatterCarrier (compositeAction point) := by
  rw [fullGaugeCompositeAction_eq_conj, LinearMap.trace_conj']

theorem incomingCurvatureAction_spin (element : SpinPlus13) (point : BasePoint)
    (axis : Fin 3) (matter : DiracExteriorMatterCarrier) :
    incomingCurvatureAction point axis (Source.Frame.spinFrame element matter) =
      Source.Frame.spinFrame element (incomingCurvatureAction point axis matter) := by
  change Complex.I • diracExteriorMotherLieAction _ (spinDiracMatterRepresentation element matter) =
    spinDiracMatterRepresentation element (Complex.I • diracExteriorMotherLieAction _ matter)
  rw [diracExteriorMotherLieAction_spinDiracMatter_commutes, map_smul]

theorem compositeAction_spin (element : SpinPlus13) (point : BasePoint)
    (matter : DiracExteriorMatterCarrier) :
    compositeAction point (spinDiracMatterRepresentation element matter) =
      spinDiracMatterRepresentation element (compositeAction point matter) :=
  alternatingProduct_intertwines _ _ (Source.Frame.spinFrame element)
    (incomingCurvatureAction_spin element point) matter

theorem localSpin_curvature_source (spinField : BasePoint → SpinPlus13) (point : BasePoint) :
    holonomicGaugeCurvature (localSpinDiracDualFormNativeAction spinField Runtime.configuration) point =
      holonomicGaugeCurvature Runtime.configuration point :=
  StageNineHolonomicGaugeCurvatureTransport.holonomicGaugeCurvature_eq_of_connection_eq _ _ rfl point

theorem compositeAction_localSpin_dual (spinField : BasePoint → SpinPlus13) (point : BasePoint) :
    (localSpinDiracDualFormNativeAction spinField Runtime.configuration).conjugateMatter point
      (compositeAction point
        ((localSpinDiracDualFormNativeAction spinField Runtime.configuration).matter point)) =
      Runtime.configuration.conjugateMatter point
        (compositeAction point (Runtime.configuration.matter point)) := by
  rw [localSpinDiracDualFormNativeAction_conjugateMatter,
    localSpinDiracDualFormNativeAction_matter, compositeAction_spin]
  simp only [LinearMap.comp_apply, Representation.inv_self_apply]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
