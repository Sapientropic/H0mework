import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryXiSlot
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.GapHilbertBasis
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Inverse.Projection
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryAdjointDefect

open BurnolPhysicalState OriginalRieszSourceGreen
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace

open private adjoint_even cayley_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private source_right_inverse from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private even_source_read from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKLiteralEdgeMeanSourcePrice.Source
open private gapState_ne_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.GapHilbertBasis
open private elementary_projection from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Inverse.Projection

namespace B
export OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices
  (physicalCotest actual_projection_fee)
export OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField
  (actual_original_boundary_fee)
end B

local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "S" => HilbertInventory.PositionField
local notation "position" => ClosedSubmodule.toSubmodule HilbertInventory.positionSpace
local notation "T" => sourceCayley
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "K" => burnolCompletedMellinRieszVector
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate

local instance : CompleteSpace S := HilbertInventory.positionSpace.isClosed.isComplete.completeSpace_coe

private theorem in_position {v : BurnolL2} (gap : v ∈ G) (even : reflectL2 v = v) : v ∈ position :=
  ⟨gap, mem_evenL2ClosedFace_iff.mpr even⟩

private theorem parity (v : S) : reflectL2 (v : BurnolL2) = v :=
  mem_evenL2ClosedFace_iff.mp v.property.2

private theorem gap_head (c : BurnolCompletedMellinCoordinate) : gapState c ∈ position :=
  in_position (mem_locallyConstantFace_iff_exists.mpr ⟨_, (gapState_restriction c).symm⟩)
    (burnolAmbientEvenPart_even _)

private theorem head_read (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) : M c v = inner ℂ (gapState c) v := by
  rw [← burnolAmbientCompletedMellinRieszVector_readback,
    burnolAmbientCompletedMellinRieszVector_eq_kernelFormula]
  exact (even_source_read _ _ even).symm

private theorem head_live (c : BurnolCompletedMellinCoordinate) : M c (gapState c) ≠ 0 := by
  rw [head_read c _ (parity ⟨_,gap_head c⟩)]
  exact fun zero => gapState_ne_zero c (inner_self_eq_zero.mp zero)

/-- Return the projected true adjoint through the original forward action. -/
def returnField (anchor : BurnolCompletedMellinCoordinate) (v : S) : BurnolL2 :=
  T anchor ((position).starProjection ((T anchor).adjoint (v : BurnolL2)))

/-- The defect is the actual difference of the whole field and its forward return. -/
def defect (anchor : BurnolCompletedMellinCoordinate) (v : S) : BurnolL2 :=
  (v : BurnolL2) - returnField anchor v

private theorem returned_in_position (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    returnField anchor v ∈ position := by
  let prior := (position).orthogonalProjectionOnto ((T anchor).adjoint (v : BurnolL2))
  exact in_position (actual_gap_cayley anchor _ prior.property.1) (cayley_even anchor _ (parity prior))

private theorem orthogonal_to_return (anchor : BurnolCompletedMellinCoordinate) (v before : S) :
    inner ℂ (T anchor (before : BurnolL2)) (defect anchor v) = 0 := by
  have projects := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left before ((T anchor).adjoint (v : BurnolL2))
  unfold defect returnField
  rw [inner_sub_right, ← ContinuousLinearMap.adjoint_inner_right, sourceCayley_inner]
  exact sub_eq_zero.mpr projects.symm

/-- The quotient coefficient is measured on the retained source field. -/
def coefficient (anchor : BurnolCompletedMellinCoordinate) (v : S) : ℂ :=
  M (C anchor) (v : BurnolL2) / M (C anchor) (gapState (C anchor))

theorem defect_source (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    defect anchor v = coefficient anchor v • gapState (C anchor) := by
  let d := C anchor
  let proposed := coefficient anchor v • gapState d
  let error := defect anchor v - proposed
  have inDefect : defect anchor v ∈ position := (position).sub_mem v.property (returned_in_position anchor v)
  have inError : error ∈ position := (position).sub_mem inDefect
    ((position).smul_mem _ (gap_head d))
  let residual : S := ⟨error,inError⟩
  have gone : M d error = 0 := by
    have gap : (position).starProjection ((T anchor).adjoint (v : BurnolL2)) ∈ G :=
      (Submodule.starProjection_apply_mem position _).1
    unfold error proposed defect returnField coefficient
    rw [map_sub, map_sub, actual_gap_cayley_conjugate_zero anchor _ gap, sub_zero, map_smul, smul_eq_mul,
      div_mul_cancel₀ _ (head_live d), sub_self]
  have beforeGap : (T anchor).adjoint error ∈ G :=
    (actual_gap_cayley_adjoint_iff anchor error inError.1 (parity residual)).mpr gone
  let previous : S :=
    ⟨(T anchor).adjoint error, in_position beforeGap (adjoint_even anchor error (parity residual))⟩
  have written := orthogonal_to_return anchor v previous
  change inner ℂ (T anchor ((T anchor).adjoint error)) (defect anchor v) = 0 at written
  rw [source_right_inverse] at written
  have projected : inner ℂ (gapState d) error = 0 := (head_read d error (parity residual)).symm.trans gone
  have test : inner ℂ error proposed = 0 := by
    unfold proposed
    rw [inner_smul_right, inner_eq_zero_symm.mp projected, mul_zero]
  have square : inner ℂ error error = 0 := by
    change inner ℂ error (defect anchor v-proposed) = 0
    rw [inner_sub_right, written, test, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp square)

/-- The actual physical projection consumes the defect before recognizing the original K. -/
theorem physical_defect (anchor : BurnolCompletedMellinCoordinate) (v : S) :
    burnolEvenAmbientProjection (defect anchor v) = coefficient anchor v • K (C anchor) := by
  rw [defect_source, map_smul, elementary_projection]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => C c
local notation "h₀" => Real.log stageZeroSonineQ

def nativeSlot (ordinal : Nat) : S :=
  let fact := BoundaryXiSlot.actual_slot observation nontrivial half depth ordinal
  ⟨BoundaryXiSlot.slot observation nontrivial half depth ordinal, in_position fact.2.1 fact.2.2.1⟩

local notation "slot" => nativeSlot observation nontrivial half depth
local notation "amount" => fun n : Nat => coefficient a (slot n)
local notation "installed" => installedOriginalKReceiptAt observation nontrivial half.down

theorem actual_coefficient_live (ordinal : Nat) : amount ordinal ≠ 0 := by
  have live := (BoundaryXiSlot.actual_slot observation nontrivial half depth ordinal).2.2.2.1
  unfold coefficient
  rw [BoundaryXiSlot.conjugate_twice c]
  exact div_ne_zero live (head_live c)

theorem actual_physical_defect (ordinal : Nat) :
    burnolEvenAmbientProjection (defect a (slot ordinal)) = amount ordinal • K c := by
  rw [physical_defect, BoundaryXiSlot.conjugate_twice c]

/-- The independently measured nonzero head normalizes the generated physical field. -/
def generatedK (ordinal : Nat) : BurnolPaAmbientCarrier :=
  (amount ordinal)⁻¹ • burnolEvenAmbientProjection (defect a (slot ordinal))

theorem actual_generated_K (ordinal : Nat) :
    generatedK observation nontrivial half depth ordinal = K c := by
  rw [generatedK, actual_physical_defect observation nontrivial half depth, smul_smul,
    inv_mul_cancel₀ (actual_coefficient_live observation nontrivial half depth ordinal), one_smul]

private theorem original_K_live : M c (K c : BurnolL2) ≠ 0 := by
  have read := congrArg (fun f : BurnolPaAmbientCarrier →L[ℂ] ℂ => f (K c))
    (burnolAmbientCompletedMellinEvaluator_restrict c)
  change M c (K c : BurnolL2) = burnolCompletedMellinEvaluator c (K c) at read
  rw [read, ← burnolCompletedMellinRieszVector_readback]
  intro erased
  have zero : K c = 0 := inner_self_eq_zero.mp erased
  apply burnolCompletedMellinEvaluator_nonzero_at_zero c observation.mathlibZero
  ext value
  simp only [← burnolCompletedMellinRieszVector_readback, zero, inner_zero_left, zero_apply]

/-- No closed combination of forward parameter fields can supply the original K read. -/
theorem generated_K_outside_forward (ordinal : Nat) :
    (generatedK observation nontrivial half depth ordinal : BurnolL2) ∉
      (Submodule.span ℂ (Set.range (fun site : List BurnolCompletedMellinCoordinate × Nat =>
        BoundaryXiSlot.forwardWord observation nontrivial half depth site.2 site.1))).topologicalClosure := by
  let samples := Set.range (fun site : List BurnolCompletedMellinCoordinate × Nat =>
    BoundaryXiSlot.forwardWord observation nontrivial half depth site.2 site.1)
  have silent : Submodule.span ℂ samples ≤ (M c).toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro value ⟨site, rfl⟩
    exact LinearMap.mem_ker.mpr ((BoundaryXiSlot.forward_word_law observation nontrivial half depth site.2 site.1).2)
  intro recovered
  have preserved := Submodule.topologicalClosure_minimal _ silent (ContinuousLinearMap.isClosed_ker (M c)) recovered
  rw [actual_generated_K observation nontrivial half depth ordinal] at preserved
  exact original_K_live observation half (LinearMap.mem_ker.mp preserved)

/-- The independent fixed B covector is applied to the physical defect generated by the actual slot. -/
def price (ordinal : Nat) : ℂ :=
  inner ℂ (B.physicalCotest c : BurnolL2) (burnolEvenAmbientProjection (defect a (slot ordinal)) : BurnolL2)

private theorem fixed_read : -(installed).fixedResidual = OriginalRieszFinitePairing.evaluatorSource c h₀ := by
  rw [installedOriginalKReceiptAt_eq_source]
  exact OriginalRieszFinitePairing.fixed_residual_source c observation.mathlibZero

theorem actual_fixed_price (ordinal : Nat) :
    price observation nontrivial half depth ordinal = amount ordinal * (-(installed).fixedResidual) := by
  have projection : burnolEvenAmbientProjection (K c : BurnolL2) = K c :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  have fixed := B.actual_projection_fee c (K c : BurnolL2)
  rw [projection, B.actual_original_boundary_fee] at fixed
  unfold price
  rw [actual_physical_defect observation nontrivial half depth, Submodule.coe_smul, inner_smul_right,
    ← fixed, ← fixed_read observation nontrivial half]

/-- The terminal read is the difference of two real physical outputs of this same adjoint slot. -/
theorem actual_fixed_difference (ordinal : Nat) :
    inner ℂ (B.physicalCotest c : BurnolL2) (burnolEvenAmbientProjection (slot ordinal : BurnolL2) : BurnolL2) -
      inner ℂ (B.physicalCotest c : BurnolL2) (burnolEvenAmbientProjection (returnField a (slot ordinal)) : BurnolL2) =
        amount ordinal * (-(installed).fixedResidual) := by
  have read := actual_fixed_price observation nontrivial half depth ordinal
  unfold price defect at read
  simpa only [map_sub, Submodule.coe_sub, inner_sub_right] using read

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryAdjointDefect
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
