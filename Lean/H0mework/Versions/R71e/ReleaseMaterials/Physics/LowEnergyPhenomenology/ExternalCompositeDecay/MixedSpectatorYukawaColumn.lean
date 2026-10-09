import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorDynamicResponse
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.ActualMotherTripleGram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SaturationMonoid SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction SU7ExteriorMatterRepresentation
open SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum
open DiracCliffordRepresentation DiracExteriorMatterAction StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaugeProjection.ConcreteBlockDiagonal
open scoped BigOperators InnerProductSpace Matrix
local instance h0R71eMixedSpectatorYukawaColumnLocal1 : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective
local instance h0R71eMixedSpectatorYukawaColumnLocal2 : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

private theorem source_disjoint_a :
    Disjoint (internalBasis 2 1).1 (finiteGenerationScalarIndex 1 0).1 := by decide
private theorem source_disjoint_b :
    Disjoint (internalBasis 2 1).1 (finiteGenerationScalarIndex 1 1).1 := by decide

def yukawaOutputA : ExteriorBasisIndex 6 := Set.powersetCard.disjUnion source_disjoint_a
def yukawaOutputB : ExteriorBasisIndex 6 := Set.powersetCard.disjUnion source_disjoint_b

def yukawaSourcePhase : ℂ := (Set.powersetCard.permOfDisjoint source_disjoint_a).sign • (1 : ℂ)

/-- A literal entry of the actual four-term joint vacuum exterior product. -/
theorem actual_vacuum_mass_entry :
    (su7ExteriorBasis 6).repr
      (exteriorYukawaMassMap finiteGenerationJointBreakingScalar
        (su7ExteriorBasis 2 (internalBasis 2 1))) yukawaOutputA = yukawaSourcePhase := by
  have hn0 : ¬Disjoint (internalBasis 2 1).1 (finiteGenerationScalarIndex 0 0).1 := by decide
  have hn1 : ¬Disjoint (internalBasis 2 1).1 (finiteGenerationScalarIndex 0 1).1 := by decide
  have hd : yukawaOutputA ≠ yukawaOutputB := by decide
  simp only [finiteGenerationJointBreakingScalar,Fin.sum_univ_two,
    exteriorYukawaMassMap_add_breaking,LinearMap.add_apply,finiteGenerationBreakingTensor]
  rw [exteriorYukawaMassMap_basisPair_of_not_disjoint _ _ hn0,
    exteriorYukawaMassMap_basisPair_of_not_disjoint _ _ hn1,
    exteriorYukawaMassMap_basisPair_of_disjoint _ _ source_disjoint_a,
    exteriorYukawaMassMap_basisPair_of_disjoint _ _ source_disjoint_b]
  simp only [zero_add,add_zero]
  change (su7ExteriorBasis 6).repr
    ((Set.powersetCard.permOfDisjoint source_disjoint_a).sign • su7ExteriorBasis 6 yukawaOutputA +
      (Set.powersetCard.permOfDisjoint source_disjoint_b).sign • su7ExteriorBasis 6 yukawaOutputB) yukawaOutputA = _
  simp [yukawaSourcePhase,hd]

theorem actual_vacuum_mass_entry_nonzero :
    (su7ExteriorBasis 6).repr
      (exteriorYukawaMassMap finiteGenerationJointBreakingScalar
        (su7ExteriorBasis 2 (internalBasis 2 1))) yukawaOutputA ≠ 0 := by
  rw [actual_vacuum_mass_entry]
  intro hz
  exact one_ne_zero ((smul_eq_zero_iff_eq (Set.powersetCard.permOfDisjoint source_disjoint_a).sign).mp hz)

end LowEnergy.MixedSpectatorCandidate
