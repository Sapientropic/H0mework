import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRegisteredRConsumer.Insertion
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJointMobiusSourceWriteback

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OutsideIncrementalCotestCertificate

open BurnolPhysicalState
open SourceGeneratedFiniteGram (Coordinates)
open SourceGeneratedFiniteGram.Projection
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit.FeedbackHistory
open OriginalWholeDebtRJointMobiusRegisteredRConsumer
open scoped BigOperators InnerProductSpace

open private coefficients_on_synthesis synthesis_single from SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection.DualColumn.Insert

open private gram_kernel_eq_zero from SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection.DualColumn

private def the_Gram_snoc_pays_both_cotests_and_all_arbitrary_field_coordinates
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (source : Fin n → E) (column : E)
    (independent : LinearIndependent ℂ (Fin.snoc source column)) (field : E) :=
  And.intro (dualColumn_snoc_last source column independent) <|
  And.intro (fun i : Fin n => dualColumn_snoc_castSucc source column independent i)
    (coefficients_snoc_read source column independent field)

private theorem the_appended_outside_column_is_the_original_self_action
    (c : BurnolCompletedMellinCoordinate) (n : ℕ) :
    column c (n+1) = selfAction c (column c n) := by
  change ((selfAction c)^(n+1)) _ = selfAction c (((selfAction c)^n) _)
  rw [pow_succ',mul_apply_eq_comp]

section Actual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

set_option cleanup.letToHave false in
private def actual_D_exterior_pays_the_new_innovation_and_keeps_the_original_price
    (ordinal : ℕ) (lag : Fin (ordinal+1)) :=
  let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
  let field := (OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth ordinal).2
  let read := original_outside_lag_insertion c ordinal field
  And.intro (the_appended_outside_column_is_the_original_self_action c ordinal) <|
  And.intro (original_outside_innovation_ne_zero c ordinal) <|
  And.intro (original_outside_last_cotest c ordinal) <|
  And.intro (original_outside_prior_cotest c ordinal lag) <|
  And.intro (read.2 lag)
    (read.1.symm.trans (actual_single_outside_history observation nontrivial half depth ordinal
      (Fin.last (ordinal+1))))

set_option cleanup.letToHave false in
private def the_written_registered_field_pays_the_same_residual_and_its_innovation_norm
    (phase : ℕ) :=
  And.intro (actual_source_equation observation nontrivial half depth) <|
  And.intro (actual_registered_incremental_lag_read observation nontrivial half depth phase)
    (actual_registered_outside_innovation_norm observation nontrivial half depth phase)

set_option cleanup.letToHave false in
private def the_actual_joint_source_occurrences_pay_the_born_relation_and_canonical_whole_next
    (ordinal : ℕ) :=
  And.intro (OriginalKJointMobiusSourceWriteback.source_occurrences observation nontrivial half depth ordinal) <|
  And.intro (OriginalKJointMobiusSourceWriteback.actual_born_kernel observation nontrivial half depth ordinal) <|
  And.intro (OriginalKJointMobiusSourceWriteback.whole_next observation nontrivial half depth ordinal)
    (OriginalKJointMobiusSourceWriteback.canonical_next observation nontrivial half depth ordinal)

end Actual

private abbrev Plane := EuclideanSpace ℂ (Fin 2)
private def axis (k : Fin 2) : Plane := PiLp.single 2 k (1 : ℂ)
private def priorAxis : Fin 1 → Plane := fun _ => axis 0
private def addedColumn : Plane := axis 0 + axis 1

private theorem appended_axes_independent :
    LinearIndependent ℂ (Fin.snoc priorAxis addedColumn) := by
  apply Fintype.linearIndependent_iff.mpr
  intro weights vanished
  rw [Fin.sum_univ_two] at vanished
  have first : Fin.snoc priorAxis addedColumn (0 : Fin 2) = axis 0 :=
    Fin.snoc_castSucc addedColumn priorAxis (0 : Fin 1)
  have last : Fin.snoc priorAxis addedColumn (1 : Fin 2) = addedColumn :=
    Fin.snoc_last addedColumn priorAxis
  rw [first,last] at vanished
  have atOne := congrArg (fun v : Plane => v (1 : Fin 2)) vanished
  have atZero := congrArg (fun v : Plane => v (0 : Fin 2)) vanished
  have zeroOne : (0 : Fin 2) ≠ 1 := by decide
  have oneZero : (1 : Fin 2) ≠ 0 := by decide
  have tail : weights 1 = 0 := by
    simpa only [addedColumn,axis,PiLp.zero_apply,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,
      if_neg zeroOne,if_neg oneZero,if_pos rfl,smul_eq_mul,mul_zero,mul_one,zero_add] using atOne
  have head : weights 0 = 0 := by
    simpa only [addedColumn,axis,PiLp.zero_apply,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,
      if_neg zeroOne,if_neg oneZero,if_pos rfl,smul_eq_mul,add_zero,mul_one,tail,mul_zero,zero_mul] using atZero
  intro k
  fin_cases k
  · exact head
  · exact tail

private theorem coefficients_at_one_source_column
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (source : ι → E) (independent : LinearIndependent ℂ source) (index : ι) :
    coefficients source (source index) index = 1 := by
  let unit : Coordinates ι := PiLp.single 2 index (1 : ℂ)
  have written : coefficients source (source index) = unit :=
    (congrArg (coefficients source) (synthesis_single source index).symm).trans
      (coefficients_on_synthesis source independent unit)
  rw [written]
  exact PiLp.single_eq_same _ _

private theorem the_nonorthogonal_append_requires_subtracting_the_new_charge :
    let charge := insertedCoefficient priorAxis addedColumn addedColumn
    coefficients priorAxis addedColumn 0 = 1 ∧ charge = 1 ∧
    coefficients priorAxis (addedColumn-charge • addedColumn) 0 = 0 ∧
    coefficients (Fin.snoc priorAxis addedColumn) addedColumn ((0 : Fin 1).castSucc) = 0 := by
  dsimp only
  have oldIndependent := (linearIndependent_finSnoc.mp appended_axes_independent).1
  have sameRead : rhs priorAxis addedColumn = rhs priorAxis (axis 0) := by
    ext i
    change inner ℂ (axis 0) (axis 0+axis 1) = inner ℂ (axis 0) (axis 0)
    have orthogonal : inner ℂ (axis 0) (axis 1) = 0 := by
      change inner ℂ (PiLp.single 2 (0 : Fin 2) (1 : ℂ) : Plane) (PiLp.single 2 (1 : Fin 2) (1 : ℂ) : Plane) = 0
      rw [EuclideanSpace.inner_single_left,PiLp.single_apply,if_neg (show (0 : Fin 2) ≠ 1 by decide),mul_zero]
    rw [inner_add_right,orthogonal,add_zero]
  have oldFull : coefficients priorAxis addedColumn 0 = 1 := by
    have same : coefficients priorAxis addedColumn = coefficients priorAxis (axis 0) := by
      have sameAction : action (gram priorAxis) (coefficients priorAxis addedColumn) =
          action (gram priorAxis) (coefficients priorAxis (axis 0)) := by
        rw [equation,equation,sameRead]
      apply sub_eq_zero.mp
      apply gram_kernel_eq_zero priorAxis oldIndependent
      rw [map_sub,sameAction,sub_self]
    rw [same]
    exact coefficients_at_one_source_column priorAxis oldIndependent 0
  have read := coefficients_snoc_read priorAxis addedColumn appended_axes_independent addedColumn
  dsimp only at read
  have newest : coefficients (Fin.snoc priorAxis addedColumn) addedColumn (Fin.last 1) = 1 :=
    (congrArg (fun v : Plane => coefficients (Fin.snoc priorAxis addedColumn) v (Fin.last 1))
      (Fin.snoc_last addedColumn priorAxis).symm).trans
      (coefficients_at_one_source_column _ appended_axes_independent (Fin.last 1))
  have paid : insertedCoefficient priorAxis addedColumn addedColumn = 1 := read.1.symm.trans newest
  have oldZero : coefficients priorAxis (0 : Plane) = 0 := by
    simpa only [map_zero] using coefficients_on_synthesis priorAxis oldIndependent (0 : Coordinates (Fin 1))
  have after : coefficients priorAxis (addedColumn - insertedCoefficient priorAxis addedColumn addedColumn • addedColumn) 0 = 0 := by
    simp only [paid,one_smul,sub_self,oldZero,PiLp.zero_apply]
  exact ⟨oldFull,paid,after,(read.2 0).trans after⟩

run_cmd do
  IO.println "CP775_CONTROL + the_Gram_snoc_pays_both_cotests_and_all_arbitrary_field_coordinates\nCP775_CONTROL + actual_D_exterior_pays_the_new_innovation_and_keeps_the_original_price\nCP775_CONTROL + the_written_registered_field_pays_the_same_residual_and_its_innovation_norm\nCP775_CONTROL + the_actual_joint_source_occurrences_pay_the_born_relation_and_canonical_whole_next\nCP775_CONTROL - the_nonorthogonal_append_requires_subtracting_the_new_charge\nCP775_GATE_PASS positive=4 negative=1"

end OutsideIncrementalCotestCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
