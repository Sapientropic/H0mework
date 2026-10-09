import H0mework.Versions.AB.Physics.LowEnergyActive.Triplet

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.ActiveSector
open DiracCliffordRepresentation DiracExteriorMatterAction
open SU7ExteriorMatterRepresentation SU7ExteriorBreakingYukawa SU7ExteriorMatterRestriction
open StageNineDiracDualYukawaSpinJurisdiction Stage9C.Material.SpinPair
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open ProofFreeRicherAnholonomicSource
noncomputable section

def internalProjection : Module.End ℂ SU7ExteriorSpinorMatterCarrier where
  toFun matter := ∑ color : Fin 3,
    (su7ExteriorBasis 2).coord (colorTripletIndex color) matter.2.1 • colorTripletMatter color
  map_add' := by intros; simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [map_smul, Finset.smul_sum, smul_smul]

def projection : Module.End ℂ DiracExteriorMatterCarrier :=
  internalMatterLinearAction internalProjection

theorem internalProjection_basis (color : Fin 3) :
    internalProjection (colorTripletMatter color) = colorTripletMatter color := by
  fin_cases color <;>
    simp +decide [internalProjection, colorTripletMatter, colorTripletIndex, Fin.sum_univ_three]

theorem projection_triplet (coefficient : DiracSpinorIndex → Fin 3 → ℂ) :
    projection (tripletMatter coefficient) = tripletMatter coefficient := by
  funext spin
  change internalProjection (∑ color, coefficient spin color • colorTripletMatter color) = _
  simp only [map_sum, map_smul, internalProjection_basis]
  rfl

theorem projection_idempotent : projection.comp projection = projection := by
  apply LinearMap.ext
  intro matter
  exact projection_triplet (fun spin color =>
    (su7ExteriorBasis 2).coord (colorTripletIndex color) (matter spin).2.1)

theorem projection_spin (matrix : DiracMatrix) :
    projection.comp (diracMatrixMatterAction matrix) =
      (diracMatrixMatterAction matrix).comp projection :=
  (diracMatrixMatterAction_commutes_internal matrix internalProjection).symm

theorem projection_original (upper lower : ℂ) :
    projection (spinPairMatter upper lower) = spinPairMatter upper lower := by
  rw [original_matter_triplet, projection_triplet]

theorem doubletDual_projection (state : Fin 2) (matter : SU7ExteriorSpinorMatterCarrier) :
    sourceColorDoubletDual state (internalProjection matter) = sourceColorDoubletDual state matter := by
  fin_cases state <;>
    simp +decide [internalProjection, sourceColorDoubletDual, sourceColorDoubletIndex,
      colorTripletMatter, colorTripletIndex, Fin.sum_univ_three]

theorem original_dual_projection (upper lower : ℂ) :
    (spinPairDual upper lower).comp projection = spinPairDual upper lower := by
  apply LinearMap.ext
  intro matter
  change (∑ spin, ∑ state, spinPairCoefficients upper lower spin state *
    sourceColorDoubletDual state (internalProjection (matter spin))) = _
  simp only [doubletDual_projection]
  rfl

theorem projection_yukawa_zero (scalar : ExteriorBreakingScalarCarrier) :
    projection.comp (diracDualRightChiralYukawaAction scalar) = 0 := by
  apply LinearMap.ext
  intro matter
  funext spin
  change (∑ color : Fin 3, (su7ExteriorBasis 2).coord (colorTripletIndex color)
    (diracDualRightChiralYukawaAction scalar matter spin).2.1 • colorTripletMatter color) = 0
  rw [Response.Yukawa.output_degree_two_zero]
  simp

theorem actual_yukawa_projection_zero :
    (diracDualRightChiralYukawaAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)).comp
      projection = 0 := by
  apply LinearMap.ext
  intro matter
  exact triplet_yukawa_zero (fun spin color =>
    (su7ExteriorBasis 2).coord (colorTripletIndex color) (matter spin).2.1)

end
end SaturationMonoid.PhysicsCore.LowEnergy.ActiveSector
