import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidFaithfulness

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u v w
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open BurnolPhysicalState SourceOperationScalarInventoryLift CofinalHistorySettlement
open CofinalFaithfulRealization CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

attribute [local instance] relationGroups

private theorem divide_at_grade (denominator : ℤ) (nonzero : denominator ≠ 0)
    (grade : Nat) (value : L.Value (PairValue C.Value) grade ()) :
    ∃ divided : L.Value (PairValue C.Value) grade (), denominator • divided = value := by
  induction grade with
  | zero =>
    change BurnolL2 × BurnolL2 at value
    change ∃ divided : BurnolL2 × BurnolL2, denominator • divided = value
    refine ⟨((denominator : ℂ)⁻¹) • value, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul,
      mul_inv_cancel₀ (Int.cast_ne_zero.mpr nonzero), one_smul]
  | succ grade previous =>
    change L.Value (PairValue C.Value) grade () × L.Value (PairValue C.Value) grade () at value
    obtain ⟨left, paidLeft⟩ := previous value.1
    obtain ⟨right, paidRight⟩ := previous value.2
    exact ⟨(left, right), Prod.ext paidLeft paidRight⟩

private theorem divided_coordinate_fibre {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (evaluate : A →ₗ[ℤ] B) (injective : Function.Injective evaluate)
    (coordinate : A ≃ₗ[ℤ] ℤ) (source : A) (unit : coordinate source = 1)
    (denominator : ℤ) (divided : B) (division : denominator • divided = evaluate source)
    (charge : ℤ) :
    charge • divided ∈ LinearMap.range evaluate ↔ denominator ∣ charge := by
  constructor
  · rintro ⟨preimage, exactRead⟩
    have same : evaluate (denominator • preimage) = evaluate (charge • source) := by
      calc
        _ = denominator • (charge • divided) := by rw [map_smul, exactRead]
        _ = charge • (denominator • divided) := by rw [smul_smul, smul_smul, mul_comm]
        _ = _ := by rw [division, map_smul]
    have read := congrArg coordinate (injective same)
    simp only [map_smul, unit, smul_eq_mul, mul_one] at read
    exact ⟨coordinate preimage, read.symm⟩
  · rintro ⟨multiple, rfl⟩
    refine ⟨multiple • source, ?_⟩
    rw [map_smul, ← division, smul_smul, mul_comm]

private theorem divided_evaluator {A : Type} [AddCommGroup A] (grade : Nat)
    (evaluate : A →ₗ[ℤ] PairValue (L.Value (PairValue C.Value) grade) ())
    (injective : Function.Injective evaluate) (coordinate : A ≃ₗ[ℤ] ℤ)
    (source : A) (unit : coordinate source = 1)
    (denominator : ℤ) (nonzero : denominator ≠ 0) :
    ∃ divided : PairValue (L.Value (PairValue C.Value) grade) (),
      denominator • divided = evaluate source ∧
      ∀ charge : ℤ, charge • divided ∈ LinearMap.range evaluate ↔ denominator ∣ charge := by
  obtain ⟨left, leftPaid⟩ := divide_at_grade denominator nonzero grade (evaluate source).1
  obtain ⟨right, rightPaid⟩ := divide_at_grade denominator nonzero grade (evaluate source).2
  let divided : PairValue (L.Value (PairValue C.Value) grade) () := (left, right)
  have division : denominator • divided = evaluate source := Prod.ext leftPaid rightPaid
  exact ⟨divided, division, divided_coordinate_fibre evaluate injective coordinate source unit
    denominator divided division⟩

private theorem uncovered_at_two {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (evaluate : A →ₗ[ℤ] B) (source : A)
    (witness : ∃ divided : B, (2 : ℤ) • divided = evaluate source ∧
      ∀ charge : ℤ, charge • divided ∈ LinearMap.range evaluate ↔ (2 : ℤ) ∣ charge) :
    ¬ Function.Surjective evaluate := by
  intro all
  obtain ⟨divided, _, exactImage⟩ := witness
  have impossible := (exactImage 1).mp (all ((1 : ℤ) • divided))
  norm_num at impossible

private theorem coverage_of_evaluation {Root : Type w} {Generator : Type u} {Carrier : Type v}
    [AddCommGroup Carrier] {root : RootedAccountedUnfolding Root}
    {seed : RootedAccountedUnfolding (PresentedRelationEventAt Generator)}
    {continuation : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator → RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
    {history : RootGeneratedCofinalHistoryAt root seed continuation}
    {evaluator : RootedAccountedUnfolding (Generator → Carrier)}
    (face : RootGeneratedCofinalFaithfulRealizationAt history evaluator)
    (sound : GeneratedRelationSoundnessAt face)
    (faithful : Function.Injective (face.completionEvaluation sound))
    (uncovered : ¬ Function.Surjective (face.completionEvaluation sound))
    (outcome : ResidualDispositionOutcome face) :
    ∃ sound obstruction coordinate, outcome = .coverageResidual sound obstruction coordinate := by
  cases outcome with
  | faithful receipt coverage _ =>
    have same : receipt = sound := Subsingleton.elim _ _
    cases same
    exact False.elim (uncovered (LinearMap.range_eq_top.mp
      (Submodule.Quotient.subsingleton_iff.mp coverage.vanishes.2)))
  | unsound obstruction _ => exact False.elim (obstruction.notSound sound.sound)
  | kernelResidual receipt _ coordinate =>
    have same : receipt = sound := Subsingleton.elim _ _
    cases same
    exact False.elim (coordinate.coordinate_ne_zero
      (faithful (coordinate.maps_to_zero.trans (map_zero _).symm)))
  | coverageResidual receipt obstruction coordinate =>
    exact ⟨receipt, obstruction, coordinate, rfl⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private abbrev paidEvaluation (ordinal : Nat) :=
  (sourceEvaluation observation nontrivial half depth ordinal).completionEvaluation
    (sourceSound observation nontrivial half depth ordinal)

/-- The ambient division of the actual source unit has exact order in the original cokernel. -/
theorem actual_paid_divided_cokernel (ordinal : Nat) (denominator : ℤ) (nonzero : denominator ≠ 0) :
    ∃ divided, denominator • divided =
        paidEvaluation observation nontrivial half depth ordinal
          (sourceClass observation nontrivial half depth ordinal) ∧
      ∀ charge : ℤ, charge • divided ∈ LinearMap.range (paidEvaluation observation nontrivial half depth ordinal) ↔
        denominator ∣ charge :=
  divided_evaluator (D.packet observation nontrivial half depth ordinal).1
    (paidEvaluation observation nontrivial half depth ordinal)
    (actual_paid_evaluation_injective observation nontrivial half depth ordinal)
    (actualPaidCompletion observation nontrivial half depth ordinal)
    (sourceClass observation nontrivial half depth ordinal)
    (actual_paid_completion_source_unit observation nontrivial half depth ordinal) denominator nonzero

theorem actual_paid_evaluation_not_surjective (ordinal : Nat) :
    ¬ Function.Surjective (paidEvaluation observation nontrivial half depth ordinal) :=
  uncovered_at_two (paidEvaluation observation nontrivial half depth ordinal)
    (sourceClass observation nontrivial half depth ordinal)
    (actual_paid_divided_cokernel observation nontrivial half depth ordinal 2 (by norm_num))

/-- The original installed disposition emits its own coverage coordinate. -/
theorem actual_paid_disposition_coverage (ordinal : Nat) :
    ∃ sound obstruction coordinate,
      sourceDisposition observation nontrivial half depth ordinal =
        .coverageResidual sound obstruction coordinate :=
  coverage_of_evaluation (sourceEvaluation observation nontrivial half depth ordinal)
    (sourceSound observation nontrivial half depth ordinal)
    (actual_paid_evaluation_injective observation nontrivial half depth ordinal)
    (actual_paid_evaluation_not_surjective observation nontrivial half depth ordinal)
    (sourceDisposition observation nontrivial half depth ordinal)

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
