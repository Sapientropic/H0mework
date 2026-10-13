import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMeanReturnMixedSource.Consumer
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKLiteralEdgeMeanSourcePrice
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualEdgeSourceNormalization (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
 (-star coordinate.value*OriginalRieszSource.GapEuler.gapMean q coordinate)⁻¹

private theorem even_source_read (value material : BurnolL2) (even : reflectL2 material=material) :
 inner ℂ (burnolAmbientEvenPart value) material=inner ℂ value material := by
 have reflected : inner ℂ (reflectL2 value) material=inner ℂ value material := by
  conv_lhs => rw [←even]
  exact reflectL2.inner_map_map value material
 change inner ℂ ((1/2:ℂ) • (value+reflectL2 value)) material=_
 rw [inner_smul_left,inner_add_left,reflected]
 simp only [starRingEnd_apply,star_div₀,star_one,star_ofNat]
 norm_num
 ring

/-- The original edge source reads the actual position/even R face generated on the same physical material. -/
theorem actual_edge_R_material_price (coordinate : BurnolCompletedMellinCoordinate)
 (material : BurnolPaAmbientCarrier) :
 inner ℂ (OriginalRieszFiniteSource.edgePrimitive coordinate)
   (burnolDirectRightResolvent (coordinate.value/2) (material : BurnolL2))=
 -star (actualEdgeSourceNormalization coordinate)*
   inner ℂ (burnolCompletedMellinRieszVector coordinate) material/(coordinate.value-1/2) := by
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have below : (coordinate.value/2).re<1/2 := by
  rw [Complex.div_re];norm_num;linarith [coordinate.belowOne]
 have coordinateRead : burnolDivisionCompletedMellinCoordinate (coordinate.value/2) right below=coordinate := by
  cases coordinate
  unfold burnolDivisionCompletedMellinCoordinate
  dsimp only
  congr 1
  ring
 have source:=CombSource.Pricing.ambient_R_scalar_action (coordinate.value/2) right
   (material : BurnolL2) material.property.1.1 (coordinate.value/2) right below
 rw [coordinateRead] at source
 have restriction:=congrArg (fun reader : BurnolPaAmbientCarrier→L[ℂ]ℂ=>reader material)
   (burnolAmbientCompletedMellinEvaluator_restrict coordinate)
 change burnolAmbientCompletedMellinEvaluator coordinate (material : BurnolL2)=
   burnolCompletedMellinEvaluator coordinate material at restriction
 rw [restriction,←burnolCompletedMellinRieszVector_readback] at source
 have read:=burnolAmbientCompletedMellinRieszVector_readback coordinate
   (burnolDirectRightResolvent (coordinate.value/2) (material : BurnolL2))
 rw [burnolAmbientCompletedMellinRieszVector_eq_kernelFormula] at read
 have even:=mem_evenL2ClosedFace_iff.mp
   (burnolDirectRightResolvent_position_even_of_integrable q (by norm_num) (coordinate.value/2) material
    (burnolDirectRightResolventIntegrand_integrableOn (coordinate.value/2) right (material : BurnolL2))).2
 change inner ℂ (actualEdgeSourceNormalization coordinate •
   burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate))
   (burnolDirectRightResolvent (coordinate.value/2) (material : BurnolL2))=_
 rw [inner_smul_left,even_source_read _ _ even,read,source]
 simp only [starRingEnd_apply]
 ring


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKLiteralEdgeMeanSourcePrice
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
