import H0mework.Chemistry.LAlanineRefinementGeometry.Incidence

/-! Actual finite parameter geometry and signed source accounts; no continuous basin-label premise. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Geometry

open Data

def refinementClosure : Prop :=
  type_of% Data.parent_installed ∧
  type_of% Data.parent_same_occurrence ∧
  type_of% BasinPartition.Runtime.basinRuntime_full_state_and_error ∧
  type_of% (BasinPartition.Runtime.basinRuntime_no_extra_MD Data.parentCurrent) ∧
  type_of% (BasinPartition.Runtime.basinRuntime_wholeLedger_same_occurrence Data.parentCurrent) ∧
  Source.sourcePacketText = Parsing.sourceText ∧
  type_of% Incidence.actualSourceCensus ∧
  type_of% Incidence.selectedResidual_isMaximal ∧
  type_of% Incidence.curveBrackets_preserved ∧
  type_of% Incidence.ambiguousCentres_preserved ∧
  (∀ r : RunIndex, Accounts.runAccount r) ∧
  type_of% Incidence.generatedSideDisposition ∧
  type_of% Incidence.mixedBand_cannotBeUnanimous ∧
  type_of% Incidence.independentRefinementReceipts ∧
  type_of% Incidence.caps_and_residuals_not_zero ∧
  type_of% Incidence.threeSlabs_signed_point_account ∧
  type_of% Incidence.band_signed_flux_account

theorem sourceGeneratedCurvedRefinement : refinementClosure :=
  ⟨Data.parent_installed, Data.parent_same_occurrence,
    BasinPartition.Runtime.basinRuntime_full_state_and_error,
    BasinPartition.Runtime.basinRuntime_no_extra_MD Data.parentCurrent,
    BasinPartition.Runtime.basinRuntime_wholeLedger_same_occurrence Data.parentCurrent,
    rfl, Incidence.actualSourceCensus, Incidence.selectedResidual_isMaximal,
    Incidence.curveBrackets_preserved, Incidence.ambiguousCentres_preserved, Accounts.everyRun,
    Incidence.generatedSideDisposition, Incidence.mixedBand_cannotBeUnanimous,
    Incidence.independentRefinementReceipts, Incidence.caps_and_residuals_not_zero,
    Incidence.threeSlabs_signed_point_account, Incidence.band_signed_flux_account⟩

example : refinementClosure := sourceGeneratedCurvedRefinement
example (r : RunIndex) : Accounts.runAccount r := Accounts.everyRun r
example (r : RunIndex) :
    ¬∃ atom : Bucket, ∀ other : Bucket, other ≠ atom → (Source.domain r 1).counts[other.val]! = 0 :=
  Incidence.mixedBand_cannotBeUnanimous r
example : Source.seedLastBucket = 17 := Incidence.ambiguousCentres_preserved.1
example (r : RunIndex) : (Source.run r).account.capPoint ≠ 0 := (Incidence.caps_and_residuals_not_zero r).1
example : Source.sourcePacketText = Parsing.sourceText := rfl

end LAlanine40K2025.BasinRefinement.Geometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
