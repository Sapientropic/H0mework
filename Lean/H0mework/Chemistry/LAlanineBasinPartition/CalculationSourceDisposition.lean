import H0mework.Chemistry.LAlanineBasinPartition.CalculationBasinIntegrals
import H0mework.Chemistry.LAlanineBasinPartition.CalculationAttractorReceipts

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.Disposition

open SourceData Force.Interface LAlanine40K2025.BasinPartition.Calculation
open scoped BigOperators
noncomputable section

theorem everyAtomicBasin_positive (atom : Atom) :
    0 < basinCount (atomicBucket atom) ∧ 0 < basinIntegral (atomicBucket atom) 0 := by
  rw [basinCount_eq_reported, basinIntegral_eq_reported]
  fin_cases atom <;> decide

theorem allRows_accounted : (∑ bucket : Bucket, basinCount bucket) = 233656 := by
  simp only [basinCount_eq_reported]
  decide

theorem atomicRows_stable :
    (∑ atom : Atom, basinCount (atomicBucket atom)) = Source.stablePointCount := by
  simp only [basinCount_eq_reported]
  decide

theorem residualRows_preserved : basinCount 13 = Source.residualPointCount ∧ basinCount 13 = 7 := by
  simp only [basinCount_eq_reported]
  decide

theorem residualBuckets_zero_weight :
    ∀ bucket : Bucket, 13 ≤ bucket.val → ∀ field : Field, basinIntegral bucket field = 0 := by
  simp only [basinIntegral_eq_reported]
  decide

theorem unusedDispositionCodes_empty :
    ∀ bucket : Bucket, 14 ≤ bucket.val → basinCount bucket = 0 := by
  simp only [basinCount_eq_reported]
  decide

theorem fullDensity_with_residual :
    (∑ bucket : Bucket, basinIntegral bucket 0) =
      1000000000000 * (Source.sourceElectronCount : Int) +
        Source.gridToSourceElectronResidual + Source.globalPointRoundingResidual 0 := by
  rw [allBuckets_commute, wholePoint_to_float]
  decide

theorem signedGauge_accounted :
    (∑ bucket : Bucket, basinGaugeResidual bucket) = Source.globalGaugeResidual ∧
    Source.globalGaugeResidual = -172 ∧ basinGaugeResidual 0 = 112 := by
  simp only [basinGauge_eq_reported]
  decide

end
end LAlanine40K2025.BasinPartition.Disposition
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
