import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiBoundaryNative

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 155000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn.XiContact

open BurnolPhysicalState Filter RootInquiryCompletion SourceOperationEffects
open RootGeneratedDebtActivationJointSource.OwnerFree
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open scoped Topology InnerProductSpace

open private Material Boundary boundaryMap boundary_source rawMap releaseMap from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiBoundaryNative

local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "P" => burnolEvenAmbientProjection
local notation "Riesz" => burnolCompletedMellinRieszVector
local notation "Rq" => burnolQuarterRestriction
local notation "mean" => burnolQuarterMeanCoefficient
local notation "F" => fourierL2

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => C c
local notation "degree" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "written" => output observation nontrivial half depth ordinal
local notation "result" => fun n m : Nat => Prod.snd (written n m)
local notation "fit" => paidQualified observation nontrivial half depth ordinal
local notation "slot" => fun n m : Nat => terminalPosition observation half (fit n m)
local notation "literal" => BoundaryAdjointDefect.nativeSlot observation nontrivial half depth ordinal
local notation "graphs" => paid observation nontrivial half depth ordinal
local notation "pa" => PaOverlap.output observation nontrivial half depth ordinal
local notation "authority" => OriginalKDirectRCofinalCalculatedSource.calculationRoot observation nontrivial half depth ordinal
local notation "origin" => OriginalKDirectRCofinalCalculatedSource.calculationCurrent observation nontrivial half depth ordinal
local notation "read" => reader observation nontrivial half depth ordinal

attribute [local irreducible] output terminalPosition paidQualified in
private theorem output_boundary (n m : Nat) : result n m = boundaryMap a (slot n m) :=
  congrArg (fun material : Material => material.2) (paid_boundary_source observation nontrivial half depth ordinal n m)

attribute [local irreducible] paid PaOverlap.output output in
private theorem retained_source (n m : Nat) :
    ((written n m).1.1.1, (written n m).1.1.2, (written n m).1.2) =
      ((graphs n m).2.1, rejected a degree (graphs n m).2.1, pa n m) :=
  congrArg (fun value : Material => (value.1.1.1, value.1.1.2, value.1.2))
    (paid_boundary_source observation nontrivial half depth ordinal n m)

private def BoundaryEquations (out : Boundary) : Prop :=
  let raw := out.2.1
  let B := out.2.2.1
  let μ := out.2.2.2.1
  let physical := out.2.2.2.2.1
  let correction := burnolAmbientEvenMeanZeroCorrection raw
  B.1 + burnolMeanZeroTruncatedFourier B.2 = 0 ∧
  burnolMeanZeroTruncatedFourier B.1 + B.2 = burnolAmbientMeanZeroFourier raw ∧
  (physical : BurnolL2) = raw - correction ∧
  μ = (mean (Rq raw) - mean (Rq correction), mean (Rq (F raw)) - mean (Rq (F correction))) ∧
  out.2.2.2.2.2 = Pa.E raw

attribute [local irreducible] output paid PaOverlap.output paidQualified terminalPosition in
theorem paid_boundary_B_means (n m : Nat) : BoundaryEquations (result n m) := by
  let x := slot n m
  let w := BoundaryQuarterRelease.raw a x
  let u := burnolAmbientMeanZeroFirstCorrection w
  let v := burnolAmbientMeanZeroSecondCorrection w
  have used := (output_boundary observation nontrivial half depth ordinal n m).trans (boundary_source a x)
  apply (congrArg BoundaryEquations used).mpr
  have split := BoundaryQuarterRelease.projection_source a x
  rw [BoundaryQuarterRelease.defect_release] at split
  have pair := BoundaryQuarterRelease.projected_means a x
  dsimp only at pair
  rw [BoundaryQuarterRelease.defect_release] at pair
  have solved : u + burnolMeanZeroTruncatedFourier v = 0 ∧
      burnolMeanZeroTruncatedFourier u + v = burnolAmbientMeanZeroFourier w :=
    BoundaryQuarterRelease.actual_B_block a x
  exact ⟨solved.1, solved.2, split, Prod.ext pair.1 pair.2, rfl⟩

private def cotest : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
  innerSL ℂ (BoundaryAdjointDefect.B.physicalCotest c)

attribute [local irreducible] output paidQualified terminalPosition in
theorem paid_boundary_original_K (n m : Nat) :
    (result n m).2.2.2.2.1 =
      BoundaryAdjointDefect.coefficient a (slot n m) • Riesz c := by
  have recorded := (output_boundary observation nontrivial half depth ordinal n m).trans (boundary_source a (slot n m))
  have got := congrArg (fun t : Boundary => t.2.2.2.2.1) recorded
  have original := BoundaryAdjointDefect.physical_defect a (slot n m)
  rw [BoundaryQuarterRelease.defect_release, BoundaryXiSlot.conjugate_twice c] at original
  exact got.trans original

attribute [local irreducible] output paidQualified terminalPosition in
theorem paid_fixed_tendsto :
    Tendsto (fun n => cotest observation half (result n n).2.2.2.2.1) atTop
      (𝓝 (BoundaryAdjointDefect.coefficient a literal *
        (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual))) := by
  let observe : PositionField →L[ℂ] ℂ :=
    (cotest observation half).comp ((P).comp (rawMap a))
  have sequence := (observe.continuous.tendsto literal).comp
    (paid_terminal_tendsto observation nontrivial half depth ordinal)
  have terminal : observe literal = BoundaryAdjointDefect.coefficient a literal *
        (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual) := by
    have fixed := BoundaryAdjointDefect.actual_fixed_price observation nontrivial half depth ordinal
    unfold BoundaryAdjointDefect.price at fixed
    rw [BoundaryQuarterRelease.defect_release] at fixed
    exact fixed
  rw [terminal] at sequence
  apply sequence.congr'
  exact Eventually.of_forall fun n => (congrArg
    (fun t : Boundary => cotest observation half t.2.2.2.2.1) (output_boundary observation nontrivial half depth ordinal n n)).symm

attribute [local irreducible] output paidQualified terminalPosition in
theorem actual_finite_xi_exit :
    ∀ᶠ n : Nat in atTop, (result n n).1 ≠ 0 := by
  let release := releaseMap a
  have limit : release literal ≠ 0 := BoundaryQuarterRelease.actual_release_live observation nontrivial half depth ordinal
  have sequence := ((release.continuous.tendsto literal).comp
    (paid_terminal_tendsto observation nontrivial half depth ordinal)).eventually_ne limit
  filter_upwards [sequence] with n checked
  have stored : (result n n).1 = release (slot n n) :=
    congrArg (fun t : Boundary => t.1) (output_boundary observation nontrivial half depth ordinal n n)
  exact fun erased => checked (stored.symm.trans erased)

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "consume_paid_xi_boundary"

theorem consume_paid_xi_boundary (n m : Nat) :
    type_of% (retained_source observation nontrivial half depth ordinal n m) ∧
    type_of% (paid_boundary_B_means observation nontrivial half depth ordinal n m) ∧
    type_of% (paid_boundary_original_K observation nontrivial half depth ordinal n m) ∧
    type_of% (paid_fixed_tendsto observation nontrivial half depth ordinal) ∧
    type_of% (actual_finite_xi_exit observation nontrivial half depth ordinal) ∧
    type_of% (paid_qualification_error observation nontrivial half depth ordinal n m) ∧
    type_of% (qualified_paid_next observation nontrivial half depth ordinal n m) ∧
    type_of% (paid_boundary_steps observation nontrivial half depth ordinal n m) ∧
    type_of% (Eval.original_material authority origin (read n m)) ∧
    type_of% (Eval.relation_boundary (R := ℤ) authority origin (read n m)) ∧
    type_of% (Relations.boundary_in_inventory authority origin (read n m)
      (Calculation.targetRuntime authority origin (read n m))) ∧
    type_of% (Calculation.target_factorizes authority origin (read n m)) ∧
    type_of% (PaOverlap.consume_paid_native_pa_return observation nontrivial half depth ordinal n m) :=
  ⟨retained_source observation nontrivial half depth ordinal n m,
    paid_boundary_B_means observation nontrivial half depth ordinal n m,
    paid_boundary_original_K observation nontrivial half depth ordinal n m,
    paid_fixed_tendsto observation nontrivial half depth ordinal,
    actual_finite_xi_exit observation nontrivial half depth ordinal,
    paid_qualification_error observation nontrivial half depth ordinal n m,
    qualified_paid_next observation nontrivial half depth ordinal n m,
    paid_boundary_steps observation nontrivial half depth ordinal n m,
    Eval.original_material authority origin (read n m),
    Eval.relation_boundary (R := ℤ) authority origin (read n m),
    Relations.boundary_in_inventory authority origin (read n m)
      (Calculation.targetRuntime authority origin (read n m)),
    Calculation.target_factorizes authority origin (read n m),
    PaOverlap.consume_paid_native_pa_return observation nontrivial half depth ordinal n m⟩

end WideResidualReturn.XiContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
