import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryAdjointDefect

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryQuarterRelease

open BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

open private adjoint_even center_zero_iff from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private source_right_inverse from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private in_position parity gap_head from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryAdjointDefect

namespace D
export BoundaryAdjointDefect
  (returnField defect defect_source physical_defect coefficient nativeSlot actual_coefficient_live price actual_fixed_price)
end D

local notation "q" => (1/4 : ℝ)
local notation "S" => HilbertInventory.PositionField
local notation "position" => ClosedSubmodule.toSubmodule HilbertInventory.positionSpace
local notation "Ppos" => Submodule.starProjection position
local notation "T" => sourceCayley
local notation "R" => burnolDirectRightResolventCLM
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Z" => OriginalRieszSource.Constructor.zeroMean
local notation "Q" => burnolQuarterRestriction
local notation "E" => burnolQuarterZeroExtension
local notation "F" => fourierL2
local notation "P" => burnolEvenAmbientProjection
local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Gq" => BurnolQuarterMeanZeroCarrier

local instance : CompleteSpace S := HilbertInventory.positionSpace.isClosed.isComplete.completeSpace_coe

private theorem evenPart_source (w : BurnolL2) (even : reflectL2 w = w) : burnolAmbientEvenPart w = w := by
  rw [burnolAmbientEvenPart, even]
  module

/-- A true centered quarter extension is orthogonal to every constant-gap test. -/
private theorem compact_orthogonal (u : Gq) (test : BurnolL2) (gap : test ∈ G) :
    inner ℂ test (E (u : Hq)) = 0 := by
  rw [show E = (Q).adjoint from rfl, ContinuousLinearMap.adjoint_inner_right]
  exact u.property _ gap

/-- Removing the actual centered quarter gives exactly the original position projection. -/
theorem position_cut (w : BurnolL2) (even : reflectL2 w = w) :
    w - Ppos w = E (Z (Q w) : Hq) := by
  let cut := Z (Q w)
  let tail := E (cut : Hq)
  let kept : BurnolL2 := w - tail
  have center : Q kept = burnolQuarterMeanCoefficient (Q w) • intervalConstant q := by
    change Q (w - E (Z (Q w) : Hq)) = _
    rw [map_sub, burnolQuarterRestriction_zeroExtension, OriginalRieszSource.Constructor.zeroMean_read, sub_sub_cancel]
  have gap : kept ∈ G := mem_locallyConstantFace_iff_exists.mpr ⟨_,center.symm⟩
  have same : cut = burnolAmbientMeanZeroPosition w := by
    unfold burnolAmbientMeanZeroPosition
    rw [evenPart_source w even]
    rfl
  have fixed : reflectRestricted q (cut : Hq) = (cut : Hq) := by
    rw [same]
    exact burnolAmbientMeanZeroPosition_reflection_fixed w
  have evenTail : reflectL2 tail = tail := by
    change reflectL2 (burnolRadiusZeroExtension q (cut : Hq)) = _
    rw [burnolRadiusZeroExtension_reflect, fixed]
    rfl
  have evenKept : reflectL2 kept = kept := by
    change reflectL2 (w-tail) = _
    rw [map_sub, even, evenTail]
  have rest : w-kept ∈ (position)ᗮ := by
    change w-(w-tail) ∈ (position)ᗮ
    rw [sub_sub_cancel]
    intro test belongs
    exact compact_orthogonal cut test belongs.1
  have positionRead : Ppos w = kept :=
    Submodule.eq_starProjection_of_mem_orthogonal (in_position gap evenKept) rest
  rw [positionRead]
  exact sub_sub_cancel _ _

/-- The actual next adjoint value writes its centered quarter as source material. -/
def release (anchor : BurnolCompletedMellinCoordinate) (v : S) : Gq :=
  Z (Q ((T anchor).adjoint (v : BurnolL2)))

theorem release_source (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    release anchor v =
      (-2 * (sourceDamping anchor : ℂ) * M (C anchor) (v : BurnolL2)) •
        SingularCounting.centeredPower anchor :=
  actual_gap_cayley_adjoint_position anchor _ v.property.1 (parity v)

/-- The compact release is the entire input for the forward defect action. -/
def raw (anchor : BurnolCompletedMellinCoordinate) (v : S) : BurnolL2 :=
  T anchor (E (release anchor v : Hq))

theorem defect_release (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    D.defect anchor v = raw anchor v := by
  have input := position_cut ((T anchor).adjoint (v : BurnolL2)) (adjoint_even anchor _ (parity v))
  have action := congrArg (T anchor) input
  rw [map_sub, source_right_inverse] at action
  exact action

private theorem raw_position (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    raw anchor v ∈ position := by
  rw [← defect_release, D.defect_source]
  exact (position).smul_mem _ (gap_head _)

/-- Only the true R action on the centered input survives the physical projection. -/
theorem physical_release (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    P (D.defect anchor v) = (sourceDamping anchor : ℂ) • P (R anchor (E (release anchor v : Hq))) := by
  have zero : P (E (release anchor v : Hq)) = 0 := by
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    intro test belongs
    exact compact_orthogonal (release anchor v) test belongs.1.1
  rw [defect_release, raw, sourceCayley_apply, map_add, map_smul, zero, zero_add]
  rfl

private theorem position_zero (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    burnolAmbientMeanZeroPosition (raw anchor v) = 0 := by
  let w := raw anchor v
  let point : S := ⟨w,raw_position anchor v⟩
  change burnolAmbientMeanZeroPosition w = 0
  unfold burnolAmbientMeanZeroPosition
  rw [evenPart_source w (parity point)]
  exact (center_zero_iff w).mpr point.property.1

/-- The original B inverse takes both equations at the same actual release. -/
theorem actual_B_block (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    let w := raw anchor v
    let first := burnolAmbientMeanZeroFirstCorrection w
    let second := burnolAmbientMeanZeroSecondCorrection w
    first + burnolMeanZeroTruncatedFourier second = 0 ∧
      burnolMeanZeroTruncatedFourier first + second = burnolAmbientMeanZeroFourier w := by
  let w := raw anchor v
  let rhs := burnolAmbientMeanZeroBlockRhs w
  have first := burnolMeanZeroBlock_first_equation rhs
  change _ = burnolAmbientMeanZeroPosition w at first
  rw [position_zero anchor v] at first
  exact ⟨first, burnolMeanZeroBlock_second_equation rhs⟩

theorem projection_source (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    (P (D.defect anchor v) : BurnolL2) =
      raw anchor v - burnolAmbientEvenMeanZeroCorrection (raw anchor v) := by
  let point : S := ⟨raw anchor v,raw_position anchor v⟩
  rw [defect_release]
  change ((evenBurnolClosedFace q).toSubmodule.orthogonalProjectionOnto (raw anchor v) : BurnolL2) = _
  rw [burnolEvenOrthogonalProjectionOnto_eq_resolventFormula, burnolAmbientExtendedSonineProjectionFormula,
    evenPart_source _ (parity point)]

/-- Both uncentered means are measured on the output of this same B inverse. -/
theorem projected_means (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    let w := raw anchor v
    let correction := burnolAmbientEvenMeanZeroCorrection w
    let output := (P (D.defect anchor v) : BurnolL2)
    burnolQuarterMeanCoefficient (Q output) =
      burnolQuarterMeanCoefficient (Q w) - burnolQuarterMeanCoefficient (Q correction) ∧
    burnolQuarterMeanCoefficient (Q (F output)) =
      burnolQuarterMeanCoefficient (Q (F w)) - burnolQuarterMeanCoefficient (Q (F correction)) := by
  have mean_sub (x y : Hq) : burnolQuarterMeanCoefficient (x - y) =
      burnolQuarterMeanCoefficient x - burnolQuarterMeanCoefficient y := by
    simp only [burnolQuarterMeanCoefficient, inner_sub_right, sub_div]
  dsimp only
  rw [projection_source]
  simp only [map_sub, mean_sub, and_true]

/-- A physical cotest acts on the local quarter through its true adjoint. -/
def quarterPrice (anchor : BurnolCompletedMellinCoordinate) (v : S) (test : BurnolPaAmbientCarrier) : ℂ :=
  inner ℂ (Z (Q ((T anchor).adjoint (test : BurnolL2)))) (release anchor v)

theorem actual_quarter_read (anchor : BurnolCompletedMellinCoordinate) (v : S) (test : BurnolPaAmbientCarrier) :
    inner ℂ (test : BurnolL2) (P (D.defect anchor v) : BurnolL2) = quarterPrice anchor v test := by
  rw [defect_release]
  have project := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left test (raw anchor v)
  change inner ℂ (test : BurnolL2) (P (raw anchor v) : BurnolL2) = _ at project
  rw [project, raw, ← ContinuousLinearMap.adjoint_inner_left,
    show E = (Q).adjoint from rfl, ContinuousLinearMap.adjoint_inner_right]
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (release anchor v)
    (Q ((T anchor).adjoint (test : BurnolL2)))).symm

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => C c
local notation "slot" => D.nativeSlot observation nontrivial half depth

theorem actual_release_live (ordinal : Nat) : release a (slot ordinal) ≠ 0 := by
  intro vanished
  have inside : (T a).adjoint (slot ordinal : BurnolL2) ∈ G :=
    (center_zero_iff _).mp vanished
  exact (BoundaryXiSlot.actual_slot observation nontrivial half depth ordinal).2.2.2.2 inside

theorem actual_fixed_quarter (ordinal : Nat) :
    quarterPrice a (slot ordinal) (BoundaryAdjointDefect.B.physicalCotest c) =
      D.coefficient a (slot ordinal) *
        (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual) := by
  rw [← actual_quarter_read]
  exact D.actual_fixed_price observation nontrivial half depth ordinal

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryQuarterRelease
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
