import H0mework.Versions.R2.Physics.GaugeSpectrum.Curvature
import H0mework.Versions.R2.Physics.QuantumState.SourceFrame

/-! Full SU(7) naturality is proved on every exterior degree before reading
the jointly moved occupied coordinates. The ambient action may leave the
original fixed doublet. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineExteriorMotherLieRepresentation
open SU7ExteriorMatterRepresentation SU7ExteriorMatterGaugeCovariantJet
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility

noncomputable section

def actualMotherConnection (point : BasePoint) : SU7MotherGaugeConnection where
  potential direction := p286LieBlockEmbed (actual.gaugeConnection point direction)
  exteriorDerivative pair := p286LieBlockEmbed
    (p286ConnectionDerivative actual point (pairFirst pair) (pairSecond pair) -
      p286ConnectionDerivative actual point (pairSecond pair) (pairFirst pair))

theorem actualMotherConnection_curvature (point : BasePoint) (pair : Fin 6) :
    motherCurvature (actualMotherConnection point) pair =
      p286LieBlockEmbed (holonomicGaugeCurvature actual point pair) := by
  simp only [motherCurvature, actualMotherConnection, holonomicGaugeCurvature,
    p286LieBlockEmbed_add, p286LieBlockEmbed_bracket]

theorem actualMotherConnection_fullGauge (element : SU7MotherGroup)
    (point : BasePoint) (pair : Fin 6) :
    motherCurvature (constantGaugeTransformMotherConnection element (actualMotherConnection point)) pair =
      motherGaugeConjugate element (p286LieBlockEmbed (holonomicGaugeCurvature actual point pair)) := by
  rw [motherCurvature_constantGaugeTransform, actualMotherConnection_curvature]

theorem slot_naturality (degree : ℕ) (change : Module.End ℂ SU7FundamentalCarrier)
    (first second : Module.End ℂ SU7FundamentalCarrier)
    (intertwines : first.comp change = change.comp second) :
    (exteriorSlotDerivedAction degree first).comp (exteriorPower.map degree change) =
      (exteriorPower.map degree change).comp (exteriorSlotDerivedAction degree second) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro vectors
  change exteriorSlotDerivedAction degree first
      (exteriorPower.map degree change ((exteriorPower.ιMulti ℂ degree) vectors)) =
    exteriorPower.map degree change
      (exteriorSlotDerivedAction degree second ((exteriorPower.ιMulti ℂ degree) vectors))
  rw [exteriorPower.map_apply_ιMulti, exteriorSlotDerivedAction_apply_ιMulti,
    exteriorSlotDerivedAction_apply_ιMulti, map_sum]
  apply Finset.sum_congr rfl
  intro position _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext index
  by_cases same : index = position
  · subst index
    simpa using congrArg (fun action : Module.End ℂ SU7FundamentalCarrier =>
      action (vectors position)) intertwines
  · simp [same]

theorem fundamentalLie_gauge (element : SU7MotherGroup) (field : SU7MotherLieMatrix) :
    (fundamentalMotherLieAction (motherGaugeConjugate element field)).comp
        (su7FundamentalRepresentation element) =
      (su7FundamentalRepresentation element).comp (fundamentalMotherLieAction field) := by
  have unit : star (element : Matrix SU7MotherIndex SU7MotherIndex ℂ) * element = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp
      (Matrix.specialUnitaryGroup_le_unitaryGroup element.property)
  apply LinearMap.ext
  intro vector
  change (((element : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
      (field : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
      star (element : Matrix SU7MotherIndex SU7MotherIndex ℂ)) *ᵥ
      ((element : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ vector)) =
    (element : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ ((field : Matrix _ _ ℂ) *ᵥ vector)
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, unit, Matrix.mul_one]

theorem exteriorLie_gauge (degree : ℕ) (element : SU7MotherGroup) (field : SU7MotherLieMatrix) :
    (exteriorMotherLieAction degree (motherGaugeConjugate element field)).comp
        (su7ExteriorPowerRepresentation degree element) =
      (su7ExteriorPowerRepresentation degree element).comp (exteriorMotherLieAction degree field) := by
  simp only [exteriorMotherLieAction_eq_slotDerivedAction, su7ExteriorPowerRepresentation]
  exact slot_naturality degree _ _ _ (fundamentalLie_gauge element field)

theorem exteriorSpinorLie_gauge (element : SU7MotherGroup) (field : SU7MotherLieMatrix)
    (matter : SU7ExteriorSpinorMatterCarrier) :
    exteriorSpinorMotherLieAction (motherGaugeConjugate element field)
        (su7ExteriorSpinorMatterRepresentation element matter) =
      su7ExteriorSpinorMatterRepresentation element (exteriorSpinorMotherLieAction field matter) := by
  rcases matter with ⟨six, two, four⟩
  apply Prod.ext
  · exact congrArg (fun action => action six) (exteriorLie_gauge 6 element field)
  · apply Prod.ext
    · exact congrArg (fun action => action two) (exteriorLie_gauge 2 element field)
    · exact congrArg (fun action => action four) (exteriorLie_gauge 4 element field)

theorem diracLie_gauge (element : SU7MotherGroup) (field : SU7MotherLieMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction (motherGaugeConjugate element field)
        (diracExteriorMatterGaugeRepresentation element matter) =
      diracExteriorMatterGaugeRepresentation element (diracExteriorMotherLieAction field matter) := by
  funext spin
  exact exteriorSpinorLie_gauge element field (matter spin)

def fullGaugeCurvatureAction (element : SU7MotherGroup) (point : BasePoint) (axis : Fin 3) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • diracExteriorMotherLieAction (motherGaugeConjugate element
    (p286LieBlockEmbed (holonomicGaugeCurvature actual point (magneticPair axis))))

theorem fullGaugeCurvatureAction_actual (element : SU7MotherGroup) (point : BasePoint)
    (axis : Fin 3) (matter : DiracExteriorMatterCarrier) :
    fullGaugeCurvatureAction element point axis (Source.Frame.gaugeFrame element matter) =
      Source.Frame.gaugeFrame element (curvatureAction point axis matter) := by
  change Complex.I • diracExteriorMotherLieAction _
      (diracExteriorMatterGaugeRepresentation element matter) =
    diracExteriorMatterGaugeRepresentation element
      (Complex.I • diracExteriorMotherLieAction _ matter)
  rw [diracLie_gauge, map_smul]

def movedCurvature (element : SU7MotherGroup) (point : BasePoint) (axis : Fin 3) : State.Observable :=
  LinearMap.toMatrix'
    ((Source.Frame.movedCoordinates (Source.Frame.gaugeFrame element)).comp
      ((fullGaugeCurvatureAction element point axis).comp
        (Source.Frame.movedEmbedding (Source.Frame.gaugeFrame element))))

theorem movedCurvature_eq (element : SU7MotherGroup) (point : BasePoint) (axis : Fin 3) :
    movedCurvature element point axis = curvature point axis := by
  apply Matrix.ext
  intro row column
  simp only [movedCurvature, curvature, compression, LinearMap.toMatrix'_apply,
    LinearMap.comp_apply, Source.Frame.movedEmbedding, LinearEquiv.coe_coe]
  rw [fullGaugeCurvatureAction_actual]
  simp only [Source.Frame.movedCoordinates, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

def movedDualCurvature (element : SU7MotherGroup) (point : BasePoint) (axis : Fin 3) : State.Observable :=
  fun row column => movedCurvature element point axis (Compatibility.flip row) column

theorem movedDualCurvature_eq (element : SU7MotherGroup) (point : BasePoint) (axis : Fin 3) :
    movedDualCurvature element point axis = dualCurvature point axis := by
  unfold movedDualCurvature
  rw [movedCurvature_eq]
  rfl

theorem fullGauge_independentDual (element : SU7MotherGroup) (point : BasePoint) (axis : Fin 3) :
    ((actual.conjugateMatter point).comp (Source.Frame.gaugeFrame element).symm.toLinearMap)
      (fullGaugeCurvatureAction element point axis
        (diracExteriorMatterGaugeRepresentation element (actual.matter point))) =
      actual.conjugateMatter point (curvatureAction point axis (actual.matter point)) := by
  rw [show diracExteriorMatterGaugeRepresentation element (actual.matter point) =
    Source.Frame.gaugeFrame element (actual.matter point) by rfl, fullGaugeCurvatureAction_actual]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
