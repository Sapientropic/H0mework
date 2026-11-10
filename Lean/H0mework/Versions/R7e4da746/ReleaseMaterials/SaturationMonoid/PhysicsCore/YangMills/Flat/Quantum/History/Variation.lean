import H0mework.Versions.R7e4da746.Physics.YangMillsFlatQuantum.HistoryAlgebra
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariation

/-! The existing primitive connection jet generates the evaluation of every
ordered curvature polynomial, including its non-Abelian quadratic channel. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.Flat.Quantum.History

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource SU7MotherLieAlgebra
open StageNineHolonomicField StageNineCompactSupportIntegrationByParts
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariation
open SU7MotherGaugeTheory
open Stage9C.Material.SpinPair Stage9DEF

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite P286CoordinateIndex

def coordinateAction (value : P286CoordinateCarrier) : Mother :=
  Complex.I • diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm value))

theorem coordinateAction_add (a b : P286CoordinateCarrier) :
    coordinateAction (a + b) = coordinateAction a + coordinateAction b := by
  simp only [coordinateAction, p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add,
    diracExteriorMotherLieAction_add, smul_add]

theorem coordinateAction_smul (t : ℝ) (a : P286CoordinateCarrier) :
    coordinateAction (t • a) = (t : ℂ) • coordinateAction a := by
  simp only [coordinateAction, p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_real_smul, smul_smul, mul_comm]

theorem field_coordinate (configuration : StageNineHolonomicConfiguration) (label : Label) :
    field configuration label = coordinateAction
      (holonomicP286GaugeCurvatureCoordinate configuration label.1 label.2) := by
  simp only [coordinateAction, holonomicP286GaugeCurvatureCoordinate,
    p286CoordinateEquiv.symm_apply_apply, field]

def expandedField (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (t : ℝ) (label : Label) : Mother :=
  field configuration label + (t : ℂ) • coordinateAction
    (p286GaugeConnectionLinearCurvatureVariation configuration variation label.1 label.2) +
    ((t ^ 2 : ℝ) : ℂ) • coordinateAction
      (p286GaugeConnectionQuadraticCurvatureVariation variation label.1 label.2)

theorem field_expansion (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) (t : ℝ) (label : Label) :
    field (varyP286GaugeConnectionCoordinate configuration variation t) label =
      expandedField configuration variation t label := by
  rw [field_coordinate,
    holonomicP286GaugeCurvatureCoordinate_expansion configuration smooth variation t label.1]
  simp only [Pi.add_apply, Pi.smul_apply, coordinateAction_add, coordinateAction_smul]
  rw [← field_coordinate]
  rfl

theorem evaluate_expansion (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) (t : ℝ) :
    evaluate (varyP286GaugeConnectionCoordinate configuration variation t) =
      FreeAlgebra.lift ℂ (expandedField configuration variation t) := by
  apply FreeAlgebra.hom_ext
  funext label
  simpa only [Function.comp_apply, evaluate_generator, FreeAlgebra.lift_ι_apply] using
    field_expansion configuration smooth variation t label

theorem current_varied_readback (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (t : ℝ) (point : BasePoint) (P : Polynomial) :
    Stage10.Runtime.configuration.conjugateMatter point
      (evaluate (varyP286GaugeConnectionCoordinate configuration variation t) P
        (Stage10.Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (Compatibility.responseMatrix (FreeAlgebra.lift ℂ
          (expandedField configuration variation t) P)) := by
  have generated := current_readback
    (varyP286GaugeConnectionCoordinate configuration variation t) point P
  simpa only [response, evaluate_expansion configuration smooth] using generated

theorem source_varied_readback
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (t : ℝ) (point : BasePoint) (P : Polynomial) :
    Stage10.Runtime.configuration.conjugateMatter point
      (evaluate (Flat.configuration
        (varyP286GaugeConnectionCoordinate actual variation t).gaugeConnection) P
          (Stage10.Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (Compatibility.responseMatrix (FreeAlgebra.lift ℂ
          (expandedField actual variation t) P)) := by
  rw [evaluate_flat]
  exact current_varied_readback actual actual_smooth variation t point P

end
end SaturationMonoid.PhysicsCore.YangMills.Flat.Quantum.History
