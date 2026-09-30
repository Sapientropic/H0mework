import H0mework.Chemistry.LAlanineBasinPartition.CalculationGlobalExact

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.Calculation

open SourceData
open scoped BigOperators
noncomputable section

def basinIntegral (bucket : Bucket) (field : Field) : Int :=
  ∑ block : GridBlock, Source.bucketIntegrals block bucket field

def basinCount (bucket : Bucket) : Nat := ∑ block : GridBlock, Source.bucketCounts block bucket

def wholePointIntegral (field : Field) : Int := ∑ block : GridBlock, Source.blockPointSums block field

def wholeFloatingBlockIntegral (field : Field) : Int := ∑ block : GridBlock, Source.blockFloatSums block field

def basinGaugeResidual (bucket : Bucket) : Int :=
  4 * (basinIntegral bucket 1 - basinIntegral bucket 2) - basinIntegral bucket 3

def basinElectronicIntegral (bucket : Bucket) : Int :=
  basinIntegral bucket 1 + basinIntegral bucket 4 + basinIntegral bucket 5 +
    basinIntegral bucket 6 + basinIntegral bucket 7

theorem basinIntegral_eq_reported (bucket : Bucket) (field : Field) :
    basinIntegral bucket field = Source.globalBucketIntegrals bucket field :=
  (GlobalExact.everyBucket bucket).2.1 field

theorem basinCount_eq_reported (bucket : Bucket) : basinCount bucket = Source.globalBucketCounts bucket :=
  (GlobalExact.everyBucket bucket).1

theorem wholePointIntegral_eq_reported (field : Field) : wholePointIntegral field = Source.globalPointSums field :=
  (GlobalExact.everyField field).1

theorem allBuckets_commute (field : Field) :
    (∑ bucket : Bucket, basinIntegral bucket field) = wholePointIntegral field := by
  simp_rw [basinIntegral_eq_reported, wholePointIntegral_eq_reported]
  exact (GlobalExact.everyField field).2.2

theorem wholePoint_to_float (field : Field) :
    wholePointIntegral field = Source.globalFloatSums field + Source.globalPointRoundingResidual field :=
  (wholePointIntegral_eq_reported field).trans (GlobalExact.everyField field).2.1

theorem basinGauge_eq_reported (bucket : Bucket) : basinGaugeResidual bucket = Source.globalBucketGaugeResidual bucket := by
  unfold basinGaugeResidual
  simp only [basinIntegral_eq_reported]
  exact (GlobalExact.everyBucket bucket).2.2

end
end LAlanine40K2025.BasinPartition.Calculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
