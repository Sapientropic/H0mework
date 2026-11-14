import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedAdjointWord
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedFourier
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.ContractiveInverse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedWordInverse

open BurnolPhysicalState Set
open scoped BigOperators

open private damping_nonzero from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedContinuousInverse
open private scale loss loss_pos from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedWord
open private clock q tail relative_bound bounded_powers from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedFiniteFlow
open private phase scaleMass from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedMassMesh
open private mesh_gap from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedDivision
open private right_quarter from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private clock_factor from H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.FiniteInverseWord
open private inverse_fourier_even from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedFourier
open private currentField current_source from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedProgramSource

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "F" => fourierL2
local notation "U" => burnolMultiplicativeDilation
local notation "R" => burnolDirectRightResolventCLM
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "I" => BoundaryCountedContinuousInverse.index
local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "M" => BoundaryCountedDivision.sharedLength
local notation "W" => BoundaryCountedDivision.commonWord
local notation "word" => BoundaryCountedFiniteFlow.word

private theorem contraction (coordinate : ℂ) (right : 1/4 < coordinate.re) (n : Nat) :
    ‖q coordinate n (n+1)‖ < 1 :=
  (relative_bound coordinate right n (n+1) (Nat.succ_pos n)).trans_lt
    (sub_lt_self 1 (loss_pos coordinate right n))

private theorem length_nonzero (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
    M coordinate n ≠ 0 := by
  unfold BoundaryCountedDivision.sharedLength SourceGeneratedFiniteInverseWord.cutoff
  exact Nat.succ_ne_zero _

private theorem omitted_contraction (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
    ‖q (coordinate.value/2) n (n+1)^M coordinate n‖ < 1 := by
  let z := coordinate.value/2
  let mesh := n+1
  have right : 1/4 < z.re := right_quarter coordinate
  have ratio : 0 ≤ 1-loss z n :=
    (norm_nonneg _).trans (relative_bound z right n mesh (Nat.succ_pos n))
  exact (bounded_powers z right n mesh (Nat.succ_pos n) (M coordinate n)).trans_lt
    (pow_lt_one₀ ratio (sub_lt_self 1 (loss_pos z right n)) (length_nonzero coordinate n))

private def clockUnit (coordinate : ℂ) (right : 1/4 < coordinate.re) (n : Nat) : Endˣ :=
  Units.map (algebraMap ℂ End).toMonoidHom (Units.mk0 (scale coordinate n) (damping_nonzero coordinate right n)) *
    Units.oneSub (q coordinate n (n+1)) (contraction coordinate right n)

private theorem clockUnit_source (coordinate : ℂ) (right : 1/4 < coordinate.re) (n : Nat) :
    ↑(clockUnit coordinate right n) = clock coordinate n (n+1) := by
  let β := scale coordinate n
  let d := tail coordinate n (n+1)
  change algebraMap ℂ End β * (1-SourceGeneratedFiniteInverseWord.relative β d) = β • (1 : End)-d
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact clock_factor β (damping_nonzero coordinate right n) d

private def omittedUnit (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) : Endˣ :=
  Units.oneSub (q (coordinate.value/2) n (n+1)^M coordinate n) (omitted_contraction coordinate n)

private theorem exact_product (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
    clock (coordinate.value/2) n (n+1) * word (coordinate.value/2) n (n+1) (M coordinate n) =
      (omittedUnit coordinate n : End) :=
  SourceGeneratedFiniteInverseWord.clock_word (scale (coordinate.value/2) n)
    (damping_nonzero (coordinate.value/2) (right_quarter coordinate) n)
    (tail (coordinate.value/2) n (n+1)) (M coordinate n)

private def wordUnit (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) : Endˣ :=
  -((clockUnit (coordinate.value/2) (right_quarter coordinate) n)⁻¹ * omittedUnit coordinate n)

private theorem wordUnit_source (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
    (wordUnit coordinate n : End) = W coordinate n := by
  let z := coordinate.value/2
  let clockU := clockUnit z (right_quarter coordinate) n
  let a := word z n (n+1) (M coordinate n)
  have source : (omittedUnit coordinate n : End) = (clockU : End)*a :=
    (exact_product coordinate n).symm.trans (congrArg (fun op : End => op*a)
      (clockUnit_source z (right_quarter coordinate) n).symm)
  change -((↑(clockU⁻¹) : End)*(omittedUnit coordinate n : End)) = -a
  rw [source, ← mul_assoc, clockU.inv_mul, one_mul]

/-- The actual finite word has a two-sided inverse generated by its own clock and omitted power. -/
def equiv (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) : BurnolL2 ≃L[ℂ] BurnolL2 :=
  ContinuousLinearEquiv.ofUnit (wordUnit coordinate n)

theorem equiv_source (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (value : BurnolL2) :
    equiv coordinate n value = W coordinate n value :=
  congrArg (fun f : End => f value) (wordUnit_source coordinate n)

private def closedGap : ClosedSubmodule ℂ BurnolL2 :=
  ⟨G,locallyConstantFace_isClosed _⟩

private theorem power_keeps_gap (coordinate : ℂ) (n k : Nat) {value : BurnolL2} (inside : value ∈ G) :
    (q coordinate n (n+1)^k) value ∈ G := by
  induction k with
  | zero => exact inside
  | succ k previous =>
    rw [pow_succ']
    change (scale coordinate n)⁻¹ • BoundaryCountedMassMesh.meshTail (I coordinate n) (n+1)
      ((q coordinate n (n+1)^k) value) ∈ G
    exact Submodule.smul_mem G _ (mesh_gap _ _ _ previous)

/-- The finite position read reflects the entire original position face. -/
theorem position_iff (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (value : BurnolL2) :
    W coordinate n value ∈ G ↔ value ∈ G := by
  refine ⟨?_,BoundaryCountedDivision.common_gap coordinate n value⟩
  intro inside
  let z := coordinate.value/2
  let a := word z n (n+1) (M coordinate n)
  let residual := q z n (n+1)^M coordinate n
  have old : a value ∈ G := by
    change -a value ∈ G at inside
    simpa only [neg_neg] using Submodule.neg_mem G inside
  have clockRead : clock z n (n+1) (a value) ∈ G := by
    change scale z n • a value-BoundaryCountedMassMesh.meshTail (I z n) (n+1) (a value) ∈ G
    exact Submodule.sub_mem G (Submodule.smul_mem G _ old) (mesh_gap _ _ _ old)
  have exactRead := congrArg (fun op : End => op value) (exact_product coordinate n)
  change clock z n (n+1) (a value) = value-residual value at exactRead
  rw [exactRead] at clockRead
  apply (SourceGeneratedContractiveInverse.sub_mem_iff residual (omitted_contraction coordinate n)
    closedGap (fun _ member => power_keeps_gap z n (M coordinate n) member) value).mp
  exact clockRead

theorem frequency_iff (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (value : BurnolL2) :
    (F).symm ((W coordinate n).adjoint value) ∈ G ↔ (F).symm value ∈ G := by
  rw [BoundaryCountedAdjointWord.adjoint_source, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    (F).symm_apply_apply]
  exact position_iff (C coordinate) n _

/-- The two true directions detect the original complete Pa carrier on the same even input. -/
theorem two_faces (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (value : BurnolL2)
    (even : reflectL2 value = value) :
    (W coordinate n value ∈ G ∧ (F).symm ((W coordinate n).adjoint value) ∈ G) ↔
      value ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  rw [position_iff, frequency_iff, inverse_fourier_even value even]
  exact ⟨fun reads => ⟨reads,mem_evenL2ClosedFace_iff.mpr even⟩,fun physical => physical.1⟩

/-- The original R action commutes with each actual finite dilation letter and the complete word. -/
theorem action_commutes (coordinate parameter : BurnolCompletedMellinCoordinate) (n : Nat) :
    Commute (R parameter) (W coordinate n) := by
  let z := coordinate.value/2
  let N := I z n
  let mesh := n+1
  let d (j : Nat) : End :=
    (U (-phase N (SourceGeneratedUnitMesh.node mesh (j+1)))).toContinuousLinearEquiv.toContinuousLinearMap
  have letter (j : Nat) : Commute (R parameter) (d j) := by
    apply ContinuousLinearMap.ext
    intro value
    exact (burnolDirectRightResolvent_dilation (parameter.value/2)
      (-phase N (SourceGeneratedUnitMesh.node mesh (j+1))) value)
  have cell : Commute (R parameter) (tail z n mesh) := by
    change Commute (R parameter) (((N : ℝ) : ℂ) • (scaleMass N : ℂ) •
      (((mesh : ℝ)⁻¹ : ℝ) : ℂ) • ∑ j ∈ Finset.range mesh, d j)
    apply Commute.smul_right
    apply Commute.smul_right
    apply Commute.smul_right
    exact Commute.sum_right _ _ _ (fun j _ => letter j)
  have relative : Commute (R parameter) (q z n mesh) :=
    cell.smul_right (scale z n)⁻¹
  change Commute (R parameter)
    (-( (scale z n)⁻¹ • ∑ j ∈ Finset.range (M coordinate n), (q z n mesh)^j : End))
  apply Commute.neg_right
  apply Commute.smul_right
  exact Commute.sum_right _ _ _ (fun j _ => relative.pow_right j)

local notation "P" => burnolEvenAmbientProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

/-- The two original physical ports give the full inverse input. -/
def recover (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (value : BurnolL2) : BurnolL2 :=
  (equiv coordinate n).symm ((P value : BurnolL2)+O value)

theorem recover_source (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (value : BurnolL2) :
    recover coordinate n (W coordinate n value) = value := by
  have whole (w : BurnolL2) : (P w : BurnolL2)+O w = w :=
    Submodule.starProjection_add_starProjection_orthogonal _
  rw [recover, whole, ← equiv_source coordinate n, ContinuousLinearEquiv.symm_apply_apply]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "pa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth
local notation "invisible" => OriginalKCombCofinalPaAction.invisible
local notation "field" => BoundaryCountedDivisionTrace.fields observation nontrivial half depth
local notation "packetField" => currentField observation nontrivial half depth

/-- The actual paired receipt recovers both literal source legs and the complete old packet. -/
theorem actual_recovery (ordinal n : Nat) :
    let old := recover c n (field ordinal n).1
    let rest := recover c n (field ordinal n).2
    (old,rest) = ((pa (ordinal+1) : BurnolL2), invisible (raw (ordinal+1))) ∧
      old+rest = packetField ordinal ∧
      recover c n (OriginalKCombPhysicalAction.R observation nontrivial half ((field ordinal n).1+(field ordinal n).2)) =
        raw (ordinal+2) := by
  have same := BoundaryCountedDivisionTrace.fields_source observation nontrivial half depth ordinal n
  rw [BoundaryCountedDivision.jointWord_read] at same
  have whole : (pa (ordinal+1) : BurnolL2)+invisible (raw (ordinal+1)) = raw (ordinal+1) := by
    change (pa (ordinal+1) : BurnolL2)+(raw (ordinal+1)-(pa (ordinal+1) : BurnolL2)) = _
    abel
  have recovered : (recover c n (field ordinal n).1,recover c n (field ordinal n).2) =
      ((pa (ordinal+1) : BurnolL2),invisible (raw (ordinal+1))) := by
    rw [same]
    exact Prod.ext (recover_source c n _) (recover_source c n _)
  have restored : recover c n (field ordinal n).1 + recover c n (field ordinal n).2 = packetField ordinal :=
    (congrArg (fun pair : BurnolL2 × BurnolL2 => pair.1+pair.2) recovered).trans
      (whole.trans (current_source observation nontrivial half depth ordinal).symm)
  have finite : (field ordinal n).1+(field ordinal n).2 = W c n (raw (ordinal+1)) := by
    rw [same]
    change W c n (pa (ordinal+1) : BurnolL2) + W c n (invisible (raw (ordinal+1))) = _
    rw [← map_add, whole]
  have action := congrArg (fun op : End => op (raw (ordinal+1))) (action_commutes c c n).eq
  change R c (W c n (raw (ordinal+1))) = W c n (R c (raw (ordinal+1))) at action
  have direct (value : BurnolL2) : OriginalKCombPhysicalAction.R observation nontrivial half value = R c value :=
    OriginalKCombCofinalRAction.original_R_direct observation nontrivial half value
  have next : R c (raw (ordinal+1)) = raw (ordinal+2) :=
    (direct _).symm.trans
      (OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth (ordinal+1)).symm
  have encoded :
      OriginalKCombPhysicalAction.R observation nontrivial half ((field ordinal n).1+(field ordinal n).2) =
        W c n (raw (ordinal+2)) := by
    rw [finite, direct, action, next]
  exact ⟨recovered,restored,(congrArg (recover c n) encoded).trans (recover_source c n _)⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedWordInverse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
