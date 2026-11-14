import H0mework.Versions.Red5c4028.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideFeedbackHistory.PhysicalSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRegisteredRConsumer

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusRegisteredRConsumer

open Complex BurnolPhysicalState OriginalKSourceResolventReconstruction
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit.FeedbackHistory
open scoped InnerProductSpace

open private input_price from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRActionSource

local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "K" => burnolCompletedMellinRieszVector

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "R₀" => burnolDirectRightResolventCLM c
local notation "point" => Sigma.fst (W.actualRInput observation nontrivial half depth)
local notation "written" => W.actualValue observation nontrivial half depth 1
local notation "receiptSource" => R.sourceInput observation nontrivial half
local notation "originalResidual" => burnolPaFixedShiftResidual c observation.mathlibZero

private theorem executed_power (phase : Nat) :
    (R₀^phase) written = (R₀^(phase+1)) point := by
  rw [pow_succ,mul_apply_eq_comp,actual_source_equation observation nontrivial half depth]

/-- Each lag is generated from this registered actor's own executed R input and literal written field. -/
theorem actual_registered_outside_history (phase : Nat) (lag : Fin (phase+1)) :
    decodedLag c phase (O ((R₀^phase) written)) lag =
      inner ℂ (fourierL2 (K c : BurnolL2)) ((R₀^(phase-lag.val)) point) := by
  rw [executed_power observation nontrivial half depth phase,actual_input observation nontrivial half depth]
  exact physical_source_decoded_history c receiptSource phase lag

/-- The actual next outside field advances every paid lag and records its own new price. -/
theorem actual_registered_lag_successor (phase : Nat) (lag : Fin (phase+1)) :
    let current := (R₀^phase) written
    let next := R₀ current
    decodedLag c (phase+1) (O next) 0 = inner ℂ (fourierL2 (K c : BurnolL2)) current ∧
    decodedLag c (phase+1) (O next) lag.succ = decodedLag c phase (O current) lag := by
  dsimp only
  have successor : (R₀^(phase+1)) written = R₀ ((R₀^phase) written) := by
    rw [pow_succ',mul_apply_eq_comp]
  rw [← successor]
  constructor
  · rw [actual_registered_outside_history observation nontrivial half depth,Fin.val_zero,Nat.sub_zero,
      ← executed_power observation nontrivial half depth phase]
  · rw [actual_registered_outside_history observation nontrivial half depth,
      actual_registered_outside_history observation nontrivial half depth,Fin.val_succ,Nat.add_sub_add_right]

/-- The oldest paid outside coordinate is the original fixed two-end residual at every phase. -/
theorem actual_registered_oldest_fixed_residual (phase : Nat) :
    decodedLag c phase (O ((R₀^phase) written)) (Fin.last phase) = -originalResidual := by
  rw [actual_registered_outside_history observation nontrivial half depth,Fin.val_last,Nat.sub_self,pow_zero,
    one_apply_eq_self,actual_input observation nontrivial half depth,
    OriginalNextEndpointProgramme.original_fixedResidual_programme observation nontrivial half,
    ← generatedK_eq_original]
  exact input_price observation nontrivial half

/-- The original exterior cotest reads the fixed residual from the same registered successor. -/
theorem actual_registered_oldest_cotest (phase : Nat) :
    inner ℂ (outsideLagCotest c phase (Fin.last phase)) (O ((R₀^phase) written)) = 2*originalResidual := by
  have read := actual_registered_oldest_fixed_residual observation nontrivial half depth phase
  rw [decoded_lag_eq_cotest] at read
  linear_combination -2*read

/-- The original outside field pays the residual cost in its own Hilbert norm. -/
theorem actual_registered_outside_norm (phase : Nat) :
    2*‖originalResidual‖ ≤ ‖outsideLagCotest c phase (Fin.last phase)‖ * ‖O ((R₀^phase) written)‖ := by
  have bound := norm_inner_le_norm (𝕜 := ℂ) (outsideLagCotest c phase (Fin.last phase)) (O ((R₀^phase) written))
  rw [actual_registered_oldest_cotest observation nontrivial half depth phase,norm_mul] at bound
  simpa only [norm_ofNat] using bound

end OriginalWholeDebtRJointMobiusRegisteredRConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
