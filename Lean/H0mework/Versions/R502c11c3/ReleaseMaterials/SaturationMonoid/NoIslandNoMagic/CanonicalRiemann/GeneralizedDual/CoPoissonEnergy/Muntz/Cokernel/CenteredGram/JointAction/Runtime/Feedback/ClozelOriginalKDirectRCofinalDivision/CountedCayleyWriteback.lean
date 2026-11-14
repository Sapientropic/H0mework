import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyProgramme

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 190000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision

open BurnolPhysicalState Filter SourceOperationEffects SourceOperationScalarRelations
open RootGeneratedDebtActivationJointSource.OwnerFree
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped Topology InnerProductSpace

open private literal_R wave_source from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocity
open private slotRead slotRead_tendsto slots Riesz_read old_field_nonzero from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocityReceipt

namespace CountedCayleyWriteback

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "prior" => D.raw observation nontrivial half depth ordinal
local notation "before" => D.raw observation nontrivial half depth (ordinal+1)
local notation "after" => D.raw observation nontrivial half depth (ordinal+1+1)
local notation "wave" => actualDivisionCompactWave observation nontrivial half depth (ordinal+1)
local notation "Resolvent" => burnolDirectRightResolventCLM
local notation "F" => fourierL2
local notation "K" => (burnolCompletedMellinRieszVector coord : BurnolL2)
local notation "nativeInput" => OriginalKCombFirstFullSourceDynamics.input
local notation "authority" => CountedFiniteNative.root observation nontrivial half depth ordinal
local notation "origin" => CountedFiniteNative.current observation nontrivial half depth ordinal
local notation "readIn" => CountedCayleyProgramme.reader observation nontrivial half depth ordinal
local notation "out" => CountedCayleyProgramme.output observation nontrivial half depth ordinal

theorem finite_source (N : Nat) (positive : 0 < N) (n : Nat) :
    out N positive n = (CountedCayleyInverse.entrance coord after n, after) := by
  have field := congrArg (Prod.snd : BurnolL2 × BurnolL2 → BurnolL2)
    (actual_counted_cell_incidence observation nontrivial half depth ordinal N positive).1
  exact (CountedCayleyProgramme.output_source observation nontrivial half depth ordinal N positive n).trans
    (congrArg (fun y : BurnolL2 => (CountedCayleyInverse.entrance coord y n,y)) field)

theorem finite_entrance_error (N : Nat) (positive : 0 < N) (n : Nat) :
    ‖(out N positive n).1-before‖ ≤
      2*‖prior‖/(sourceDamping coord*((n : ℝ)+1)) := by
  have p : @Eq BurnolL2 before (Resolvent coord prior) :=
    literal_R observation nontrivial half depth ordinal
  have q : @Eq BurnolL2 after (Resolvent coord before) :=
    literal_R observation nontrivial half depth (ordinal+1)
  rw [finite_source, q, p]
  exact CountedCayleyInverse.entrance_error coord prior n

theorem finite_wave (N : Nat) (positive : 0 < N) (n : Nat) :
    (F (out N positive n).1,F (out N positive n).2) =
      (CountedCayleyInverse.waveEntrance coord wave n,wave) := by
  have actualWave : @Eq BurnolL2 (F after) wave := wave_source observation nontrivial half depth ordinal
  rw [finite_source]
  exact Prod.ext ((CountedCayleyInverse.entrance_fourier coord after n).trans
    (congrArg (fun y : BurnolL2 => CountedCayleyInverse.waveEntrance coord y n) actualWave)) actualWave

theorem actual_entrance (N : Nat) (positive : 0 < N) :
    Tendsto (out N positive) atTop (𝓝 (before,after)) := by
  have q : @Eq BurnolL2 after (Resolvent coord before) :=
    literal_R observation nontrivial half depth (ordinal+1)
  have limit : Tendsto (CountedCayleyInverse.entrance coord after) atTop (𝓝 before) :=
    by
      rw [q]
      exact CountedCayleyInverse.entrance_tendsto coord before
  exact (limit.prodMk_nhds (tendsto_const_nhds (x := after))).congr'
    (Eventually.of_forall fun n => (finite_source observation nontrivial half depth ordinal N positive n).symm)

theorem actual_entrance_slots (N : Nat) (positive : 0 < N) :
    Tendsto (fun n => slotRead K (out N positive n)) atTop
      (𝓝 (nativeInput observation nontrivial half depth (ordinal+1),
        nativeInput observation nontrivial half depth (ordinal+1+1),inner ℂ ((Resolvent coord).adjoint K) before)) ∧
      ∀ᶠ n : Nat in atTop, (out N positive n).1 ≠ 0 := by
  have actual := actual_entrance observation nontrivial half depth ordinal N positive
  exact ⟨slotRead_tendsto actual (slots observation nontrivial half depth ordinal)
      (slots observation nontrivial half depth (ordinal+1)) (Riesz_read observation nontrivial half depth ordinal),
    actual.fst_nhds.eventually_ne (old_field_nonzero observation nontrivial half depth ordinal)⟩

namespace WriteEval
export CountedCayleyProgramme.Eval (original_material relation_boundary updated_inverse_fibre relation_cochain)
end WriteEval

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_entrance_writeback"

theorem actual_entrance_writeback (N : Nat) (positive : 0 < N) (n : Nat)
    (increment : Env CountedCellHistory.CellValue CountedCellHistory.Var) :
    type_of% (CountedCayleyProgramme.count_child_source observation nontrivial half depth ordinal N positive n) ∧
    type_of% (CountedCayleyProgramme.paid_steps observation nontrivial half depth ordinal N positive n) ∧
    type_of% (WriteEval.original_material authority origin (readIn N positive n)) ∧
    type_of% (WriteEval.relation_boundary (R := ℤ) authority origin (readIn N positive n)) ∧
    type_of% (WriteEval.relation_cochain (R := ℤ) authority origin (readIn N positive n) increment) ∧
    type_of% (WriteEval.updated_inverse_fibre (R := ℤ) authority origin (readIn N positive n) increment) ∧
    type_of% (Relations.boundary_in_inventory authority origin (readIn N positive n)
      (Calculation.targetRuntime authority origin (readIn N positive n))) ∧
    type_of% (Calculation.target_factorizes authority origin (readIn N positive n)) ∧
    type_of% (finite_entrance_error observation nontrivial half depth ordinal N positive n) ∧
    type_of% (finite_wave observation nontrivial half depth ordinal N positive n) ∧
    type_of% (actual_entrance_slots observation nontrivial half depth ordinal N positive) ∧
    type_of% (DirectRDivisionControls.actual_division_action_same_root observation nontrivial half depth (ordinal+1)) :=
  ⟨CountedCayleyProgramme.count_child_source observation nontrivial half depth ordinal N positive n,
    CountedCayleyProgramme.paid_steps observation nontrivial half depth ordinal N positive n,
    WriteEval.original_material authority origin (readIn N positive n),
    WriteEval.relation_boundary (R := ℤ) authority origin (readIn N positive n),
    WriteEval.relation_cochain (R := ℤ) authority origin (readIn N positive n) increment,
    WriteEval.updated_inverse_fibre (R := ℤ) authority origin (readIn N positive n) increment,
    Relations.boundary_in_inventory authority origin (readIn N positive n)
      (Calculation.targetRuntime authority origin (readIn N positive n)),
    Calculation.target_factorizes authority origin (readIn N positive n),
    finite_entrance_error observation nontrivial half depth ordinal N positive n,
    finite_wave observation nontrivial half depth ordinal N positive n,
    actual_entrance_slots observation nontrivial half depth ordinal N positive,
    DirectRDivisionControls.actual_division_action_same_root observation nontrivial half depth (ordinal+1)⟩

end CountedCayleyWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
