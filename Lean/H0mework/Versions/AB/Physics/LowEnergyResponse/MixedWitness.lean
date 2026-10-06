import H0mework.Versions.AB.Physics.LowEnergyResponse.Yukawa

/-! A nonzero scalar--independent-dual mixed channel at the ORIGINAL actual.
This witness rules out dropping that Hessian block, not any physical theory. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Response.MixedWitness
open DiracCliffordRepresentation DiracExteriorMatterAction
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum
open StageNineDiracDualYukawaSpinJurisdiction Stage9C.Material.SpinPair
open GaugeProjection.ConcreteBlockDiagonal ProofFreeRicherAnholonomicSource
noncomputable section
local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

def scalarIndex : ExteriorBasisIndex 4 :=
  ⟨{colorZeroIndex, colorTwoIndex, weakZeroIndex, weakOneIndex}, by
    change ({colorZeroIndex, colorTwoIndex, weakZeroIndex, weakOneIndex} :
      Finset SU7MotherIndex).card = 4
    decide⟩

theorem disjoint_channel : Disjoint (sourceColorDoubletIndex 1).1 scalarIndex.1 := by
  decide

def outputIndex : ExteriorBasisIndex 6 := Set.powersetCard.disjUnion disjoint_channel

def scalarDirection : ExteriorBreakingScalarCarrier := su7ExteriorBasis 4 scalarIndex

def outputDual : Module.Dual ℂ DiracExteriorMatterCarrier where
  toFun matter := (su7ExteriorBasis 6).coord outputIndex (matter 2).1
  map_add' := by intros; simp
  map_smul' := by intros; simp

theorem right_input (point : BasePoint) :
    (diracMatrixMatterAction rightChiralityProjector (actual.matter point) 2).2.1 =
      lowerPhase point • su7ExteriorBasis 2 (sourceColorDoubletIndex 1) := by
  rw [actual_matter]
  simp [diracMatrixMatterAction, rightChiralityProjector, diracGammaFive,
    spinPairMatter, sourceColorDiracMatter, spinPairCoefficients,
    sourceColorDoubletMatter, Fin.sum_univ_four, Fin.sum_univ_two]
  norm_num

/-- The matrix element is a source phase times an actual exterior permutation sign. -/
theorem channel_value (point : BasePoint) :
    outputDual (diracDualRightChiralYukawaAction scalarDirection (actual.matter point)) =
      lowerPhase point * ((Set.powersetCard.permOfDisjoint disjoint_channel).sign • (1 : ℂ)) := by
  change (su7ExteriorBasis 6).coord outputIndex
    (exteriorYukawaMassMap scalarDirection
      (diracMatrixMatterAction rightChiralityProjector (actual.matter point) 2).2.1) = _
  rw [right_input, map_smul, map_smul]
  rw [scalarDirection, exteriorYukawaMassMap_basisPair_of_disjoint
    (sourceColorDoubletIndex 1) scalarIndex disjoint_channel]
  simp [outputIndex]

/-- Occupied Yukawa zero does not make the scalar/dual-matter Hessian zero. -/
theorem mixed_channel_nonzero :
    (outputDual (diracDualRightChiralYukawaAction scalarDirection (actual.matter 0))).re ≠ 0 := by
  rw [channel_value]
  simp only [lowerPhase, phase_zero, one_mul, Units.smul_def]
  simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.Response.MixedWitness
