import H0mework.Versions.R2.Physics.Helicity.Action
import H0mework.Versions.R2.Physics.CompositeSpectrum.Naturality

/-! The ordered matter action and its independent-dual response are
transported on the full carrier before occupied coordinates are read. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open Matrix DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterGaugeCovariantJet
open Stage9DEF Stage9DEF.Compatibility

noncomputable section

def fullGaugeAction (element : SU7MotherGroup) (point : BasePoint) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  ∑ axis : Fin 3,
    diracExteriorMotherLieAction (motherGaugeConjugate element (p286LieBlockEmbed (magnetic point axis))) *
      diracExteriorMotherLieAction (motherGaugeConjugate element (p286LieBlockEmbed (covariantCurl point axis)))

theorem fullGaugeAction_intertwines (element : SU7MotherGroup) (point : BasePoint)
    (matter : DiracExteriorMatterCarrier) :
    fullGaugeAction element point (Source.Frame.gaugeFrame element matter) =
      Source.Frame.gaugeFrame element (action point matter) := by
  change fullGaugeAction element point (diracExteriorMatterGaugeRepresentation element matter) =
    diracExteriorMatterGaugeRepresentation element (action point matter)
  simp only [fullGaugeAction, action, Fin.sum_univ_three, LinearMap.add_apply,
    Module.End.mul_apply, diracLie_gauge, map_add]

def movedCompression (element : SU7MotherGroup) (point : BasePoint) : State.Observable :=
  LinearMap.toMatrix' ((Source.Frame.movedCoordinates (Source.Frame.gaugeFrame element)).comp
    ((fullGaugeAction element point).comp (Source.Frame.movedEmbedding (Source.Frame.gaugeFrame element))))

theorem movedCompression_eq (element : SU7MotherGroup) (point : BasePoint) :
    movedCompression element point = compression (action point) := by
  ext row column
  simp only [movedCompression, compression, LinearMap.toMatrix'_apply, LinearMap.comp_apply,
    Source.Frame.movedEmbedding, LinearEquiv.coe_coe]
  rw [fullGaugeAction_intertwines]
  simp only [Source.Frame.movedCoordinates, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

def movedObservable (element : SU7MotherGroup) (point : BasePoint) : State.Observable :=
  fun row column => movedCompression element point (Compatibility.flip row) column

theorem movedObservable_eq (element : SU7MotherGroup) (point : BasePoint) :
    movedObservable element point = observable point := by
  unfold movedObservable
  rw [movedCompression_eq]
  rfl

theorem fullGaugeAction_independentDual (element : SU7MotherGroup) (point : BasePoint) :
    ((Runtime.configuration.conjugateMatter point).comp (Source.Frame.gaugeFrame element).symm.toLinearMap)
      (fullGaugeAction element point (Source.Frame.gaugeFrame element (Runtime.configuration.matter point))) =
      Runtime.configuration.conjugateMatter point (action point (Runtime.configuration.matter point)) := by
  rw [fullGaugeAction_intertwines]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
