import H0mework.Versions.Red5c4028.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideFeedbackHistory.Insertion
import H0mework.Versions.Red5c4028.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRegisteredRConsumer.OutsideHistory

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusRegisteredRConsumer

open BurnolPhysicalState SourceGeneratedFiniteGram.Projection
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit.FeedbackHistory
open scoped InnerProductSpace

local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "R₀" => burnolDirectRightResolventCLM c
local notation "written" => W.actualValue observation nontrivial half depth 1
local notation "originalResidual" => burnolPaFixedShiftResidual c observation.mathlibZero

/-- The actual next outside field pays the original residual through its new column and reuses the old lag inverse. -/
theorem actual_registered_incremental_lag_read (phase : Nat) :
    let field : BurnolL2 := O ((R₀^(phase+1)) written)
    let inserted : BurnolL2 := column c (phase+1)
    let charge : ℂ := insertedCoefficient (fun j : Fin (phase+1) => column c j.val) inserted field
    charge = 2*originalResidual ∧
      ∀ lag : Fin (phase+1),
        decodedLag c (phase+1) field lag.castSucc = decodedLag c phase (field-charge • inserted) lag := by
  dsimp only
  have computed := original_outside_lag_insertion c phase (O ((R₀^(phase+1)) written))
  dsimp only at computed
  refine ⟨?_,computed.2⟩
  rw [← inserted_dualColumn_read,← original_outside_last_cotest]
  exact actual_registered_oldest_cotest observation nontrivial half depth (phase+1)

/-- The actual outside norm pays the original residual times the exact new-column innovation. -/
theorem actual_registered_outside_innovation_norm (phase : Nat) :
    2*‖originalResidual‖ *
      ‖innovationCLM (fun j : Fin (phase+1) => column c j.val) (column c (phase+1))‖ ≤
      ‖O ((R₀^(phase+1)) written)‖ := by
  have bound := inserted_coefficient_norm_le (fun j : Fin (phase+1) => column c j.val) (column c (phase+1))
    (O ((R₀^(phase+1)) written)) (original_outside_innovation_ne_zero c phase)
  have actual : insertedCoefficient (fun j : Fin (phase+1) => column c j.val) (column c (phase+1))
      (O ((R₀^(phase+1)) written)) = 2*originalResidual :=
    (actual_registered_incremental_lag_read observation nontrivial half depth phase).1
  rw [actual,norm_mul] at bound
  simpa only [Complex.norm_ofNat] using bound

end OriginalWholeDebtRJointMobiusRegisteredRConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
