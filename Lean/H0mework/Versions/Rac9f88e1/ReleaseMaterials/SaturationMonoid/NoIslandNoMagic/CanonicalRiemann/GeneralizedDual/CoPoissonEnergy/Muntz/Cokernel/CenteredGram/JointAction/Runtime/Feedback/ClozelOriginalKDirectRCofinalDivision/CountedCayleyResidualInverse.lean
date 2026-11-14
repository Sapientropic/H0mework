import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyEffectInverse.Finite
import H0mework.Versions.Rac9f88e1.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyUpdateConsumer

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 140000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCayleyResidualInverse

open BurnolPhysicalState Filter
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped Topology

namespace Geom
export SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse
  (cayley retention retention_pos retention_lt_one loss_eq clock driveScale finite finite_zero finite_succ
    finite_effect finite_commutes source_norm_le_effect finite_error inverse inverse_isometric_effect finite_tendsto)
end Geom

local notation "R" => burnolDirectRightResolventCLM
local notation "d" => sourceDamping
local notation "FieldOp" => BurnolL2 →L[ℂ] BurnolL2

def effect (c : BurnolCompletedMellinCoordinate) : FieldOp := R c-1

def approximate (c : BurnolCompletedMellinCoordinate) (n : Nat) : FieldOp :=
  Geom.finite (R c) (d c) n

def recover (c : BurnolCompletedMellinCoordinate) : FieldOp :=
  Geom.inverse (R c) (d c)

theorem effect_value (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) : effect c x = R c x-x := rfl

theorem effect_inverse (c : BurnolCompletedMellinCoordinate) :
    Function.LeftInverse (recover c) (effect c) ∧ Function.RightInverse (recover c) (effect c) := by
  have solved := Geom.inverse_isometric_effect (R c) (sourceDamping_pos c) (sourceCayley_norm c)
  exact ⟨fun x => congrArg (fun op : FieldOp => op x) solved.1,
    fun x => congrArg (fun op : FieldOp => op x) solved.2⟩

theorem approximate_error (c : BurnolCompletedMellinCoordinate) (data : BurnolL2) (n : Nat) :
    ‖approximate c n data-recover c data‖ ≤ Geom.retention (d c)^n*‖data‖ := by
  have solved := (effect_inverse c).2 data
  change (R c-1) (recover c data) = data at solved
  simpa only [approximate, solved] using
    (Geom.finite_error (R c) (sourceDamping_pos c) (sourceCayley_norm c) (recover c data) n).2

theorem approximate_tendsto (c : BurnolCompletedMellinCoordinate) (data : BurnolL2) :
    Tendsto (fun n => approximate c n data) atTop (𝓝 (recover c data)) :=
  Geom.finite_tendsto (R c) (sourceDamping_pos c) (sourceCayley_norm c) data

theorem approximate_succ (c : BurnolCompletedMellinCoordinate) (n : Nat) (x : BurnolL2) :
    approximate c (n+1) x = Geom.clock (R c) (d c) (approximate c n x) + Geom.driveScale (d c) • x :=
  congrArg (fun op : FieldOp => op x) (Geom.finite_succ (R c) (d c) n)

def defect (c : BurnolCompletedMellinCoordinate) (pair : BurnolL2 × BurnolL2) : BurnolL2 :=
  pair.2-R c pair.1

theorem defect_effect (c : BurnolCompletedMellinCoordinate) (pair : BurnolL2 × BurnolL2) :
    defect c (effect c pair.1, effect c pair.2) = effect c (defect c pair) := by
  simp only [defect, effect_value, map_sub]

theorem approximate_defect (c : BurnolCompletedMellinCoordinate) (pair : BurnolL2 × BurnolL2) (n : Nat) :
    defect c (approximate c n pair.1, approximate c n pair.2) = approximate c n (defect c pair) := by
  change approximate c n pair.2 - R c (approximate c n pair.1) =
    approximate c n (pair.2 - R c pair.1)
  rw [map_sub]
  exact congrArg (fun y => approximate c n pair.2-y)
    (congrArg (fun op : FieldOp => op pair.1) (Geom.finite_commutes (R c) (d c) n).eq)

/-- The original incidence graph has a unique complete preimage exactly when the measured square closes. -/
theorem exact_incidence_fibre (c : BurnolCompletedMellinCoordinate) (data : BurnolL2 × BurnolL2) :
    (∃! x, (effect c x, effect c (R c x)) = data) ↔ defect c data = 0 := by
  have inv := effect_inverse c
  have commute (x : BurnolL2) : effect c (R c x) = R c (effect c x) := by
    rw [effect_value, effect_value, map_sub]
  constructor
  · rintro ⟨x, rfl, _⟩
    exact sub_eq_zero.mpr (commute x)
  · intro closes
    have second : data.2 = R c data.1 := sub_eq_zero.mp closes
    refine ⟨recover c data.1, Prod.ext (inv.2 data.1) ?_, ?_⟩
    · rw [commute, inv.2 data.1, ← second]
    · intro x paid
      exact inv.1.injective ((congrArg Prod.fst paid).trans (inv.2 data.1).symm)

section Actual

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "out" => CountedCayleyProgramme.output observation nontrivial half depth ordinal

/-- Both fields of the installed inverse fibre are the input of the finite return. -/
def data (N : Nat) (positive : 0 < N) (n : Nat) : BurnolL2 × BurnolL2 :=
  let read := CountedCayleyIncrement.residualRead observation nontrivial half depth ordinal N positive n
  (read 0,read 1)

theorem actual_effect (N : Nat) (positive : 0 < N) (n : Nat) :
    data observation nontrivial half depth ordinal N positive n =
      (effect c (out N positive n).1, effect c (out N positive n).2) :=
  (CountedCayleyIncrement.actual_residual observation nontrivial half depth ordinal N positive n).trans
    (CountedCayleyIncrement.actual_resolvent_effect observation nontrivial half depth ordinal N positive n)

theorem actual_recovered (N : Nat) (positive : 0 < N) (n : Nat) :
    let read := data observation nontrivial half depth ordinal N positive n
    (recover c read.1,recover c read.2) = out N positive n := by
  dsimp only
  rw [actual_effect]
  exact Prod.ext ((effect_inverse c).1 _) ((effect_inverse c).1 _)

theorem actual_graph_defect (N : Nat) (positive : 0 < N) (n : Nat) :
    defect c (data observation nontrivial half depth ordinal N positive n) =
      effect c (defect c (out N positive n)) := by
  rw [actual_effect, defect_effect]

theorem actual_zero_round_defect (N : Nat) (positive : 0 < N) :
    defect c (data observation nontrivial half depth ordinal N positive 0) ≠ 0 := by
  let read := data observation nontrivial half depth ordinal N positive 0
  have entrance : CountedCayleyInverse.entrance c (out N positive 0).2 0 = 0 := by
    simp [CountedCayleyInverse.entrance,
      SourceGeneratedActionObservationHistory.ContractiveRecovery.approximate,
      birkhoffAverage, birkhoffSum]
  have before : (out N positive 0).1 = 0 := by
    have fields := CountedCayleyWriteback.finite_source observation nontrivial half depth ordinal N positive 0
    rw [fields] at entrance ⊢
    exact entrance
  have first : read.1 = 0 := by
    dsimp only [read]
    rw [actual_effect, before, map_zero]
  have second : read.2 ≠ 0 :=
    CountedCayleyIncrement.actual_residual_successor_ne_zero observation nontrivial half depth ordinal N positive 0
  change defect c read ≠ 0
  simpa only [defect, first, map_zero, sub_zero] using second

end Actual

end CountedCayleyResidualInverse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
