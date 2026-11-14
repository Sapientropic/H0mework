import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPriceJointTail
import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.EmittedPaPrices

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.EmittedPaJointProbe

open BurnolPhysicalState
open scoped InnerProductSpace
open EmittedPaInnovation
open private retained physical_novel from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.EmittedPaInnovation

namespace Fit
export SourceGeneratedFiniteGram.Projection (coefficients synthesis)
end Fit
namespace Sparse
export SourceGeneratedFiniteGram.CofinalRecord (sample)
end Sparse

variable {n : Nat}

private def fitted (row : Fin (n+1) → BurnolPaAmbientCarrier) (tests : Fin n → Nat) : Record.Values n :=
  Fit.coefficients
    (fun j : Fin n => Sparse.sample tests (fun t => PhysicalPriceGrid.price t (row j.castSucc)))
    (Sparse.sample tests (fun t => PhysicalPriceGrid.price t (row (Fin.last n))))

/-- Subtract the fit of the actual retained K samples in the physical field. -/
def fieldResidual (row : Fin (n+1) → BurnolPaAmbientCarrier) (tests : Fin n → Nat) :
    BurnolPaAmbientCarrier :=
  row (Fin.last n) - Fit.synthesis (retained row) (fitted row tests)

theorem residual_price (row : Fin (n+1) → BurnolPaAmbientCarrier) (tests : Fin n → Nat) (t : Nat) :
    PhysicalPriceGrid.price t (fieldResidual row tests) =
      PhysicalPriceGrid.price t (row (Fin.last n)) -
        ∑ j : Fin n, fitted row tests j * PhysicalPriceGrid.price t (row j.castSucc) := by
  change PhysicalPriceGrid.price t
    (row (Fin.last n) - ∑ j : Fin n, fitted row tests j • row j.castSucc) = _
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]

private theorem field_residual_live {row : Fin (n+1) → BurnolPaAmbientCarrier}
    (rank : LinearIndependent ℂ row) (tests : Fin n → Nat) : fieldResidual row tests ≠ 0 := by
  intro zero
  exact physical_novel rank ⟨fitted row tests, (sub_eq_zero.mp zero).symm⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "Event" => RetainedRecord.Progress observation nontrivial half depth
local notation "pair" => physicalPair observation nontrivial half depth

/-- The two residuals are generated at one retained list of actual original K tests. -/
def pairedResidual {start : Nat} (event : Event start n) (tests : Fin n → Nat) :
    BurnolPaAmbientCarrier × BurnolPaAmbientCarrier :=
  (fieldResidual (fun actor => (pair event actor).1) tests,
    fieldResidual (fun actor => (pair event actor).2) tests)

local notation "residuals" => pairedResidual observation nontrivial half depth

private theorem exists_common {start : Nat} (event : Event start n) (tests : Fin n → Nat) (cutoff : Nat) :
    ∃ t, PhysicalPriceGrid.price (cutoff+t) (residuals event tests).1 ≠ 0 ∧
      PhysicalPriceGrid.price (cutoff+t) (residuals event tests).2 ≠ 0 := by
  let fields := residuals event tests
  have rank := physical_ranks observation nontrivial half depth event
  have first : fields.1 ≠ 0 := field_residual_live rank.1 tests
  have second : fields.2 ≠ 0 := field_residual_live rank.2 tests
  exact PhysicalPriceJointTail.common_price_in_tail fields.1 fields.2 first second cutoff

/-- One source-selected original K address pays both actual physical residuals. -/
def firstCommon {start : Nat} (event : Event start n) (tests : Fin n → Nat) (cutoff : Nat) : Nat := by
  classical
  exact cutoff + Nat.find (exists_common observation nontrivial half depth event tests cutoff)

local notation "chosen" => firstCommon observation nontrivial half depth

theorem first_common_live {start : Nat} (event : Event start n) (tests : Fin n → Nat) (cutoff : Nat) :
    PhysicalPriceGrid.price (chosen event tests cutoff) (residuals event tests).1 ≠ 0 ∧
      PhysicalPriceGrid.price (chosen event tests cutoff) (residuals event tests).2 ≠ 0 := by
  classical
  exact Nat.find_spec (exists_common observation nontrivial half depth event tests cutoff)

theorem earlier_has_silent_leg {start : Nat} (event : Event start n) (tests : Fin n → Nat) (cutoff k : Nat)
    (earlier : cutoff+k < chosen event tests cutoff) :
    PhysicalPriceGrid.price (cutoff+k) (residuals event tests).1 = 0 ∨
      PhysicalPriceGrid.price (cutoff+k) (residuals event tests).2 = 0 := by
  classical
  by_contra! live
  have least := Nat.find_min' (exists_common observation nontrivial half depth event tests cutoff) live
  change cutoff+k < cutoff + Nat.find (exists_common observation nontrivial half depth event tests cutoff) at earlier
  omega

theorem common_original_K {start : Nat} (event : Event start n) (tests : Fin n → Nat) (cutoff : Nat) :
    let address := chosen event tests cutoff
    let probe := PhysicalPriceGrid.coordinate address
    probe.value.re = 3/4 ∧
      inner ℂ (burnolCompletedMellinRieszVector probe : BurnolL2) ((residuals event tests).1 : BurnolL2) ≠ 0 ∧
      inner ℂ (burnolCompletedMellinRieszVector probe : BurnolL2) ((residuals event tests).2 : BurnolL2) ≠ 0 := by
  have live := first_common_live observation nontrivial half depth event tests cutoff
  exact ⟨PhysicalPriceGrid.real_part _, fun zero => live.1 ((PhysicalPriceGrid.price_is_original_K _ _).trans zero),
    fun zero => live.2 ((PhysicalPriceGrid.price_is_original_K _ _).trans zero)⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.EmittedPaJointProbe
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
