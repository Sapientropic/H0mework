import H0mework.Versions.R2.Physics.CompositeSpectrum.Naturality

/-! Full representation trace, occupied trace, and dual-response trace have
different carriers. The full trace retains its explicitly generated
complement term instead of identifying it with the two-color readout. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility

noncomputable section

def occupiedProjection : Module.End ℂ DiracExteriorMatterCarrier := embed.comp coordinates

def complementaryComposite (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  (1 - occupiedProjection) * compositeAction point

def fullCompositeTrace (point : BasePoint) : ℂ :=
  LinearMap.trace ℂ DiracExteriorMatterCarrier (compositeAction point)

theorem occupiedCompositeTrace (point : BasePoint) :
    (compression (compositeAction point)).trace = 8 * (curvatureScale : ℂ) ^ 3 := by
  rw [compositeAction_compression, rawCubic_normalForm, Matrix.trace_smul]
  norm_num [Matrix.trace_one, Source.Index, Fintype.card_prod]
  ring

theorem responseCompositeTrace (point : BasePoint) :
    (responseMatrix (compositeAction point)).trace = 0 := by
  rw [compositeAction_responseMatrix, cubic_normalForm, Matrix.trace_smul, Matrix.trace_kronecker]
  simp [Matrix.trace, exchange, Compatibility.spinFlip, Fin.sum_univ_four]

theorem fullTrace_occupied_part (point : BasePoint) :
    LinearMap.trace ℂ DiracExteriorMatterCarrier (occupiedProjection * compositeAction point) =
      (compression (compositeAction point)).trace := by
  change LinearMap.trace ℂ DiracExteriorMatterCarrier
      ((embed.comp coordinates).comp (compositeAction point)) = _
  rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ Source.Index)]
  rfl

theorem fullCompositeTrace_decomposition (point : BasePoint) :
    fullCompositeTrace point = 8 * (curvatureScale : ℂ) ^ 3 +
      LinearMap.trace ℂ DiracExteriorMatterCarrier (complementaryComposite point) := by
  have split : compositeAction point = occupiedProjection * compositeAction point +
      complementaryComposite point := by
    unfold complementaryComposite
    change compositeAction point = occupiedProjection.comp (compositeAction point) +
      (LinearMap.id - occupiedProjection).comp (compositeAction point)
    rw [LinearMap.sub_comp, LinearMap.id_comp]
    abel
  rw [fullCompositeTrace, split, map_add, fullTrace_occupied_part, occupiedCompositeTrace]

theorem fullCompositeTrace_gauge (element : SU7ExteriorMatterRepresentation.SU7MotherGroup)
    (point : BasePoint) :
    LinearMap.trace ℂ DiracExteriorMatterCarrier (fullGaugeCompositeAction element point) =
      fullCompositeTrace point := fullGaugeCompositeAction_trace element point

theorem occupiedAction_scalar (point : BasePoint) (values : Source.Index → ℂ) :
    compositeAction point (embed values) = (curvatureScale : ℂ) ^ 3 • embed values := by
  rw [compositeAction_embed, rawCubic_normalForm, Matrix.smul_mulVec, Matrix.one_mulVec, map_smul]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
