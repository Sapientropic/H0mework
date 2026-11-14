import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCellHistory
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocityReceipt

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 160000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision

open BurnolPhysicalState OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

open private literal_R wave_source from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocity
open private slotRead slots Riesz_read old_field_nonzero from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocityReceipt

local notation "R" => burnolDirectRightResolventCLM
local notation "Riesz" => burnolCompletedMellinRieszVector
local notation "F" => fourierL2
local notation "nativeInput" => OriginalKCombFirstFullSourceDynamics.input

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "before" => D.raw observation nontrivial half depth (ordinal+1)
local notation "after" => D.raw observation nontrivial half depth (ordinal+1+1)
local notation "wave" => actualDivisionCompactWave observation nontrivial half depth (ordinal+1)
local notation "counts" => CountedCellHistory.count observation nontrivial half depth ordinal

def cellIncidence (N : Nat) (positive : 0 < N) : BurnolL2 × BurnolL2 :=
  CountedCellInverse.recoverIncidence coord N positive (counts N 0) (counts N 1)

def cellWave (N : Nat) (positive : 0 < N) : BurnolL2 × BurnolL2 :=
  CountedCellInverse.recoverWaveIncidence coord N positive (F (counts N 0)) (F (counts N 1))

/-- Two adjacent paid counts determine the exact original R incidence and both its Fourier fields. -/
theorem actual_counted_cell_incidence (N : Nat) (positive : 0 < N) :
    cellIncidence observation nontrivial half depth ordinal N positive = (before,after) ∧
    cellWave observation nontrivial half depth ordinal N positive = (F before,wave) := by
  have first : @Eq BurnolL2 (counts N 0) (DualSource.source N after) :=
    CountedCellHistory.count_source observation nontrivial half depth ordinal N 0
  have second : @Eq BurnolL2 (counts N 1) (DualSource.source (N+1) after) :=
    CountedCellHistory.count_source observation nontrivial half depth ordinal N 1
  have actual : @Eq BurnolL2 after (R coord before) :=
    literal_R observation nontrivial half depth (ordinal+1)
  have originalWave : @Eq BurnolL2 (F after) wave :=
    wave_source observation nontrivial half depth ordinal
  constructor
  · have data := congrArg₂ (CountedCellInverse.recoverIncidence coord N positive) first second
    refine data.trans ?_
    rw [actual, CountedCellInverse.recover_incidence]
  · have w₀ : @Eq BurnolL2 (F (counts N 0)) (FiniteForcing.source N (F (R coord before))) :=
      (congrArg F first).trans ((OriginalGamma.Source.CountingQuadraticLimit.source_fourier N after).symm.trans
        (congrArg (fun y : BurnolL2 => FiniteForcing.source N (F y)) actual))
    have w₁ : @Eq BurnolL2 (F (counts N 1)) (FiniteForcing.source (N+1) (F (R coord before))) :=
      (congrArg F second).trans ((OriginalGamma.Source.CountingQuadraticLimit.source_fourier (N+1) after).symm.trans
        (congrArg (fun y : BurnolL2 => FiniteForcing.source (N+1) (F y)) actual))
    have data := congrArg₂ (CountedCellInverse.recoverWaveIncidence coord N positive) w₀ w₁
    exact data.trans ((CountedCellInverse.recover_wave_incidence coord N positive before).trans
      (congrArg (fun y : BurnolL2 => (F before,y)) ((congrArg F actual.symm).trans originalWave)))

/-- The fixed-cell inverse reads both complete native slot pairs and the original independent K price. -/
theorem actual_counted_cell_slots (N : Nat) (positive : 0 < N) :
    slotRead (Riesz coord : BurnolL2) (cellIncidence observation nontrivial half depth ordinal N positive) =
      (nativeInput observation nontrivial half depth (ordinal+1),
        nativeInput observation nontrivial half depth (ordinal+1+1),
        inner ℂ ((R coord).adjoint (Riesz coord : BurnolL2)) before) := by
  have paired := (actual_counted_cell_incidence observation nontrivial half depth ordinal N positive).1
  exact (congrArg (slotRead (Riesz coord : BurnolL2)) paired).trans
    (Prod.ext (slots observation nontrivial half depth ordinal)
      (Prod.ext (slots observation nontrivial half depth (ordinal+1))
        (Riesz_read observation nontrivial half depth ordinal)))

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_counted_cell_receipt"

theorem actual_counted_cell_receipt (N : Nat) (positive : 0 < N) :
    type_of% (actual_counted_cell_incidence observation nontrivial half depth ordinal N positive) ∧
    type_of% (actual_counted_cell_slots observation nontrivial half depth ordinal N positive) ∧
    (cellIncidence observation nontrivial half depth ordinal N positive).1 ≠ 0 ∧
    type_of% (CountedCellHistory.count_paid_steps observation nontrivial half depth ordinal N) ∧
    type_of% (CountedCellHistory.cell_same_root observation nontrivial half depth ordinal N) ∧
    type_of% (DirectRDivisionControls.actual_division_action_same_root observation nontrivial half depth (ordinal+1)) := by
  have fields := actual_counted_cell_incidence observation nontrivial half depth ordinal N positive
  have live : (cellIncidence observation nontrivial half depth ordinal N positive).1 ≠ 0 := by
    have first := congrArg (Prod.fst : BurnolL2 × BurnolL2 → BurnolL2) fields.1
    exact fun erased => old_field_nonzero observation nontrivial half depth ordinal (first.symm.trans erased)
  exact ⟨fields, actual_counted_cell_slots observation nontrivial half depth ordinal N positive, live,
    CountedCellHistory.count_paid_steps observation nontrivial half depth ordinal N,
    CountedCellHistory.cell_same_root observation nontrivial half depth ordinal N,
    DirectRDivisionControls.actual_division_action_same_root observation nontrivial half depth (ordinal+1)⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
