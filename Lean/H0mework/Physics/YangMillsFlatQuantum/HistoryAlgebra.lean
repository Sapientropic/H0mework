import H0mework.Physics.YangMillsFlatQuantum.Response
import Mathlib.Algebra.FreeAlgebra

/-! Local curvature words act on the full mother carrier before the single
independent-dual response. No intermediate occupied projection is inserted. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.Flat.Quantum.History

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource
open StageNineHolonomicField Stage9C.Material.SpinPair Stage9DEF

noncomputable section

abbrev Label := BasePoint × Fin 6
abbrev Polynomial := FreeAlgebra ℂ Label
abbrev Mother := Module.End ℂ DiracExteriorMatterCarrier

def field (configuration : StageNineHolonomicConfiguration) (label : Label) : Mother :=
  Complex.I • diracExteriorMotherLieAction
    (SU7MotherLieAlgebra.p286LieBlockEmbed
      (holonomicGaugeCurvature configuration label.1 label.2))

def evaluate (configuration : StageNineHolonomicConfiguration) : Polynomial →ₐ[ℂ] Mother :=
  FreeAlgebra.lift ℂ (field configuration)

@[simp] theorem evaluate_generator (configuration : StageNineHolonomicConfiguration)
    (label : Label) : evaluate configuration (FreeAlgebra.ι ℂ label) = field configuration label :=
  FreeAlgebra.lift_ι_apply _ _

theorem evaluate_word (configuration : StageNineHolonomicConfiguration) (word : List Label) :
    evaluate configuration (word.map (FreeAlgebra.ι ℂ)).prod =
      (word.map (field configuration)).prod := by
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def, evaluate_generator]

theorem flat_magnetic (connection : P286ConnectionField) (point : BasePoint) (axis : Fin 3) :
    field (Flat.configuration connection) (point, Stage10.GaugeSpectrum.magneticPair axis) =
      curvatureAction connection point axis := rfl

theorem evaluate_flat (configuration : StageNineHolonomicConfiguration) :
    evaluate (Flat.configuration configuration.gaugeConnection) = evaluate configuration := by
  apply FreeAlgebra.hom_ext
  funext label
  rfl

def response (configuration : StageNineHolonomicConfiguration) (P : Polynomial) : State.Observable :=
  Compatibility.responseMatrix (evaluate configuration P)

theorem current_readback (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (P : Polynomial) :
    Stage10.Runtime.configuration.conjugateMatter point
      (evaluate configuration P (Stage10.Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (response configuration P) := by
  have generated := Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.quantumClosure.sourceResponse
    point (evaluate configuration P)
  rw [Stage9DEF.Runtime.firstQuantumTick_answer, Stage9DEF.Runtime.fieldAt_eq_vector] at generated
  rw [Stage10.Runtime.configuration_eq, Stage10.Runtime.tick_vector]
  exact generated

theorem next_readback (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (P : Polynomial) :
    Stage10.Runtime.nextConfiguration.conjugateMatter point
      (evaluate configuration P (Stage10.Runtime.nextConfiguration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Stage10.Runtime.nextTick.answer point)
        (response configuration P) := by
  have generated := current_readback configuration point P
  rw [Stage10.Runtime.configuration_eq, Stage10.Runtime.tick_vector] at generated
  rw [Stage10.Runtime.nextConfiguration, Stage9DEF.Runtime.configurationAt_eq_actual,
    Stage10.Runtime.nextTick_vector]
  exact generated

end
end SaturationMonoid.PhysicsCore.YangMills.Flat.Quantum.History
