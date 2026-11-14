import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit

open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.KGamma
open SourceOperationScalarInventoryLift CofinalHistorySettlement
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Install
open scoped InnerProductSpace

namespace PrimeThree
export OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Consumer
  (actual_gap actual_physical_live actual_B_two_means actual_R_covariance value_source)
end PrimeThree

namespace First
export OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Consumer
  (actual_rho_successor fullSource full_source_value)
end First

namespace CS
export BoundaryNativeKConductorSource (Source)
end CS

namespace Pay
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (native_effect native_inverse)
end Pay

local notation "Word" => PairValue C.Value
local instance consumerGroups (k : Nat) : ∀ slot, AddCommGroup (L.Value Word k slot) := L.groups Word k

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ j : Nat, observation.coordinate = -2 * (j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth width start : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R₀" => burnolDirectRightResolventCLM c
local notation "V" => Orbit.value observation nontrivial half depth width start
local notation "F" => frameAt observation nontrivial half depth width start
local notation "Q" => cfgAt observation nontrivial half depth width start
local notation "write" => writerAt observation nontrivial half depth width start
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)

theorem actual_direct_R (k : Nat) : V (k+1) = R₀ (V k) :=
  (actual_R_step observation nontrivial half depth width start k).trans
    (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half _)

private abbrev referenceValue (k : Nat) :=
  OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Consumer.value
    observation nontrivial half depth (start+1+k) width

/-- Value covariance lets the independent physical reader use its original cofinal estimates. -/
theorem actual_cofinal_value (k : Nat) : V k = referenceValue observation nontrivial half depth width start k := by
  induction k with
  | zero =>
    exact (initial_value observation nontrivial half depth width start).trans
      ((First.actual_rho_successor observation nontrivial half depth width start).trans
        (PrimeThree.value_source observation nontrivial half depth (start+1) width).symm)
  | succ k previous =>
    calc
      _ = R₀ (V k) := actual_direct_R observation nontrivial half depth width start k
      _ = R₀ (referenceValue observation nontrivial half depth width start k) := congrArg R₀ previous
      _ = _ := (PrimeThree.actual_R_covariance observation nontrivial half depth (start+1+k) width).trans
        (PrimeThree.value_source observation nontrivial half depth (start+1+k+1) width).symm

theorem actual_gap_and_live (k : Nat) :
    V k ∈ locallyConstantFace Math.scale⁻¹ ∧ P (V k) ≠ 0 := by
  rw [actual_cofinal_value]
  exact ⟨PrimeThree.actual_gap observation nontrivial half depth (start+1+k) width,
    PrimeThree.actual_physical_live observation nontrivial half depth (start+1+k) width⟩

/-- The two logarithmic graphs are generated along the same action as the entire paid value. -/
def fullSource : Nat → CS.Source
  | 0 => First.fullSource observation nontrivial half depth start
  | k+1 => Material.resolve c (fullSource k)

theorem actual_full_source (k : Nat) : (fullSource observation nontrivial half depth start k).value = V k := by
  induction k with
  | zero =>
    exact (First.full_source_value observation nontrivial half depth width start).trans
      (initial_value observation nontrivial half depth width start).symm
  | succ k previous =>
    exact (Material.resolve_value c _).trans
      ((congrArg R₀ previous).trans (actual_direct_R observation nontrivial half depth width start k).symm)

theorem actual_graphs (k : Nat) :
    let source := fullSource observation nontrivial half depth start k
    LogPair (V k) source.position ∧ LogPair (fourierL2.symm (V k)) source.inverse ∧
      GammaPair (V k) source.gamma := by
  dsimp only
  rw [← actual_full_source observation nontrivial half depth width start k]
  let source := fullSource observation nontrivial half depth start k
  exact ⟨source.position_graph, source.inverse_graph, source.graph⟩

theorem actual_Gamma_step (k : Nat) :
    (fullSource observation nontrivial half depth start (k+1)).gamma =
      R₀ (fullSource observation nontrivial half depth start k).gamma :=
  Material.resolve_gamma c _

theorem actual_B_means (k : Nat) :
    let mean := fun value : BurnolL2 => burnolQuarterMeanCoefficient (burnolQuarterRestriction value)
    let correction := burnolAmbientEvenMeanZeroCorrection (V k)
    mean (P (V k)) = mean (V k) - mean correction ∧
      mean (fourierL2 (P (V k))) = mean (fourierL2 (V k)) - mean (fourierL2 correction) := by
  dsimp only
  rw [actual_cofinal_value]
  exact PrimeThree.actual_B_two_means observation nontrivial half depth (start+1+k) width

/-- The original physical K tests each paid successor against the prior actual frame. -/
theorem actual_K_price (k : Nat) :
    inner ℂ K (P (V (k+1))) = inner ℂ ((R₀).adjoint K) (V k) :=
  (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (burnolCompletedMellinRieszVector c) _).trans
    ((congrArg (inner ℂ K) (actual_direct_R observation nontrivial half depth width start k)).trans
      (ContinuousLinearMap.adjoint_inner_left R₀ (V k) K).symm)

theorem actual_receipt_writeback (k : Nat) :
    type_of% (Pay.native_effect (F k) (Q k) (write k)) ∧
    type_of% (Pay.native_inverse (F k) (Q k) (write k)) ∧
    type_of% (WB.born_inventory (F k) (Q k) (write k)) ∧
    type_of% (WB.born_pair_inventory (F k) (Q k) (write k)) ∧
    type_of% (WB.source_target_root (F k) (Q k) (write k)) ∧
    type_of% (WB.source_whole (F k) (Q k) (write k)) ∧
    type_of% (WB.actual_receipt_next (F k) (Q k) (write k)) ∧
    type_of% (WB.source_target_next (F k) (Q k) (write k)) :=
  ⟨Pay.native_effect (F k) (Q k) (write k), Pay.native_inverse (F k) (Q k) (write k),
    WB.born_inventory (F k) (Q k) (write k), WB.born_pair_inventory (F k) (Q k) (write k),
    WB.source_target_root (F k) (Q k) (write k), WB.source_whole (F k) (Q k) (write k),
    WB.actual_receipt_next (F k) (Q k) (write k), WB.source_target_next (F k) (Q k) (write k)⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
