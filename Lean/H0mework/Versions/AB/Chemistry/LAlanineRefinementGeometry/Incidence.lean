import H0mework.Versions.AB.Chemistry.LAlanineRefinementGeometry.Accounts

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Geometry.Incidence

open Data Force.Interface
open scoped BigOperators
noncomputable section

theorem actualSourceCensus :
    Source.runs.size = 5 ∧ Source.selectedBasin = 7 ∧ Source.incidentPair = #[6, 7] ∧
    Source.sourceRows = #[83494, 82922] ∧ Source.centerCoordinates.size = 3 ∧
    Source.basisCoordinates.size = 3 ∧ Source.curveKnots.size = 9 ∧
    Source.curveLower.size = 9 ∧ Source.curveUpper.size = 9 := by decide

theorem selectedResidual_isMaximal (atom : Atom) :
    |BasinPartition.Source.globalBucketIntegrals (BasinPartition.SourceData.atomicBucket atom) 3| ≤
      |BasinPartition.Source.globalBucketIntegrals 7 3| := by
  fin_cases atom <;> decide

theorem curveBrackets_preserved :
    ∀ knot : Knot, Source.lower knot < Source.upper knot ∧
      (Source.curveEndpointBuckets[0]!)[knot.val]! = 6 ∧ (Source.curveEndpointBuckets[1]!)[knot.val]! = 7 ∧
      (Source.curveEndpointCoarse[0]!)[knot.val]! = 6 ∧ (Source.curveEndpointFine[0]!)[knot.val]! = 6 ∧
      (Source.curveEndpointCoarse[1]!)[knot.val]! = 7 ∧ (Source.curveEndpointFine[1]!)[knot.val]! = 7 := by decide +kernel

theorem ambiguousCentres_preserved :
    Source.seedLastBucket = 17 ∧ Source.curveAmbiguousBuckets = #[17, 17, 17, 17, 17, 17, 17] := by decide

theorem generatedSideDisposition :
    ∀ r : RunIndex,
      (∀ b : Bucket, (Source.run r).lowerCounts[b.val]! = if b.val = 6 then 256 else 0) ∧
      (∀ b : Bucket, (Source.run r).upperCounts[b.val]! = if b.val = 7 then 256 else 0) ∧
      (Source.domain r 0).counts[6]! = 1024 ∧ (Source.domain r 0).counts[7]! = 0 ∧
      (Source.domain r 2).counts[6]! = 0 ∧ (Source.domain r 2).counts[7]! = 1024 ∧
      (Source.domain r 1).counts[6]! = 512 ∧ (Source.domain r 1).counts[7]! = 512 ∧
      (∀ d : Slab, (Source.domain r d).wholeLabel = none) := by decide

theorem mixedBand_cannotBeUnanimous (r : RunIndex) :
    ¬∃ atom : Bucket, ∀ other : Bucket, other ≠ atom → (Source.domain r 1).counts[other.val]! = 0 := by
  have actual := generatedSideDisposition r
  have left : (Source.domain r 1).counts[6]! = 512 := actual.2.2.2.2.2.2.1
  have right : (Source.domain r 1).counts[7]! = 512 := actual.2.2.2.2.2.2.2.1
  rintro ⟨atom, alone⟩
  by_cases h : (6 : Bucket) = atom
  · have different : (7 : Bucket) ≠ atom := by rw [← h]; decide
    have zero := alone 7 different
    exact (by decide : (512 : Nat) ≠ 0) (right.symm.trans zero)
  · have zero := alone 6 h
    exact (by decide : (512 : Nat) ≠ 0) (left.symm.trans zero)

theorem independentRefinementReceipts :
    (Source.run 0).steps = 4 ∧ (Source.run 1).steps = 8 ∧ (Source.run 2).steps = 16 ∧
    (Source.run 0).epsilonHex = (Source.run 1).epsilonHex ∧ (Source.run 1).epsilonHex = (Source.run 2).epsilonHex ∧
    Source.epsilon 0 = Source.epsilon 1 ∧ Source.epsilon 1 = Source.epsilon 2 ∧
    Source.epsilon 2 = 2 * Source.epsilon 3 ∧ Source.epsilon 3 = 2 * Source.epsilon 4 ∧
    (∀ r : RunIndex, 0 < Source.epsilon r) ∧
    (Source.run 2).sampledNormalUpper < (Source.run 1).sampledNormalUpper ∧
    (Source.run 1).sampledNormalUpper < (Source.run 0).sampledNormalUpper ∧
    (Source.run 3).steps = 16 ∧ (Source.run 4).steps = 16 ∧
    (Source.domain 4 1).measure < (Source.domain 3 1).measure ∧
    (Source.domain 3 1).measure < (Source.domain 2 1).measure := by decide +kernel

theorem caps_and_residuals_not_zero :
    ∀ r : RunIndex, (Source.run r).account.capPoint ≠ 0 ∧
      (Source.run r).account.divergenceResidual ≠ 0 ∧ (Source.run r).sampledNormalUpper ≠ 0 := by decide

theorem threeSlabs_signed_point_account (r : RunIndex) (f : Field) :
    (∑ d : Fin 3, ((Source.run r).domains[d.val]!).point[f.val]!) =
      (Source.domain r 3).point[f.val]! + (Source.run r).account.pointSlabResidual[f.val]! := by
  rcases Accounts.everyRun r with ⟨_, _, _, _, _, _, fields, _⟩
  have equality := (fields f).1
  omega

theorem band_signed_flux_account (r : RunIndex) :
    1000000000 * (Source.domain r 1).point[3]! =
      (Source.run r).account.pointBoundary - (Source.run r).account.boundaryRounding +
      (Source.run r).account.divergenceResidual - (Source.run r).account.picoResolutionResidual +
      1000000000 * (Source.domain r 1).rounding[3]! := by
  rcases Accounts.everyRun r with ⟨_, _, _, domains, _, _, _, _, _, _, pointFloat, lapPico, lapFlux, _⟩
  rcases domains 1 with ⟨_, _, _, _, _, _, _, _, _, rounding, _⟩
  have same := rounding (3 : Field)
  change (Source.domain r 1).point[3]! =
    (Source.domain r 1).floating[3]! + (Source.domain r 1).rounding[3]! at same
  omega

end
end LAlanine40K2025.BasinRefinement.Geometry.Incidence
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
