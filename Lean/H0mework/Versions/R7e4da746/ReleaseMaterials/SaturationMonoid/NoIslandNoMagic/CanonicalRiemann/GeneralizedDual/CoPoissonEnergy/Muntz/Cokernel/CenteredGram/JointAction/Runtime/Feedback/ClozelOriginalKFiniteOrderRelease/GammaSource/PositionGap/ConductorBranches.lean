import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionConductor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.GammaOutsideHistory
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.WindowLog.Physical

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.DivisionConductor

open BurnolPhysicalState MeasureTheory
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.FiniteLogCounting
open OriginalGamma.Source.ConductorDual OriginalGamma.Source.KGamma
open OriginalGamma.Source.WindowLog
open scoped InnerProductSpace

open private log_pair_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ConductorDualSource
open private logPair_sub from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource

local notation "P₀" => OriginalKCombPhysicalAction.physicalProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "R" => burnolDirectRightResolventCLM
local notation "F" => fourierL2
local notation "W" => OriginalKCrossParameterRAdjointSource.GammaOutsideHistory.write

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "totalGamma" => gammaAt observation half
local notation "totalPosition" => positionLogAt observation half
local notation "totalInverse" => inverseLogAt observation half

private def physicalPosition (ordinal : Nat) : BurnolL2 :=
  physicalProjectionPositionLog (raw ordinal) (totalPosition ordinal)

private def physicalInverse (ordinal : Nat) : BurnolL2 :=
  reflectL2 (physicalProjectionFourierLog (raw ordinal) (reflectL2 (totalInverse ordinal)))

/-- Both Gamma slots use the original projection, with its two logarithmic block corrections. -/
def branchGammaAt (ordinal : Nat) : BurnolL2 × BurnolL2 :=
  let physical := physicalPosition observation nontrivial half depth ordinal +
    F (physicalInverse observation nontrivial half depth ordinal)
  (physical, totalGamma ordinal - physical)

local notation "physPosition" => physicalPosition observation nontrivial half depth
local notation "physInverse" => physicalInverse observation nontrivial half depth
local notation "gamma" => branchGammaAt observation nontrivial half depth

private theorem literal_split (ordinal : Nat) : (P₀ (raw ordinal), O (raw ordinal)) = input ordinal := by
  cases ordinal with
  | zero =>
    rw [OriginalKCombFirstFullSourceDynamics.first_pair, OriginalKCombFirstFullSourceDynamics.raw_origin]
  | succ n =>
    rw [OriginalKCombFirstFullSourceDynamics.next_pair, OriginalKCombFirstFullSourceDynamics.raw_successor]

private theorem physical_logs (ordinal : Nat) :
    LogPair (input ordinal).1 (physPosition ordinal) ∧
      LogPair (fourierL2.symm (input ordinal).1) (physInverse ordinal) := by
  have paid := actual_division_conductor observation nontrivial half depth ordinal
  have frequency := log_pair_reflect _ _ paid.2.2
  rw [fourierL2_symm_eq_reflect_fourierL2, reflectL2_reflectL2] at frequency
  have projected := actual_physical_projection_log_pairs _ _ _ paid.2.1 frequency
  have position : LogPair (P₀ (raw ordinal)) (physPosition ordinal) := projected.1
  have inverse := log_pair_reflect _ _ projected.2
  rw [← fourierL2_symm_eq_reflect_fourierL2] at inverse
  have inverse' : LogPair (fourierL2.symm (P₀ (raw ordinal))) (physInverse ordinal) := inverse
  have physical : P₀ (raw ordinal) = (input ordinal).1 :=
    congrArg Prod.fst (literal_split observation nontrivial half depth ordinal)
  rw [physical] at position inverse'
  exact ⟨position, inverse'⟩

private theorem outside_logs (ordinal : Nat) :
    LogPair (input ordinal).2 (totalPosition ordinal - physPosition ordinal) ∧
      LogPair (fourierL2.symm (input ordinal).2) (totalInverse ordinal - physInverse ordinal) := by
  have paid := actual_division_conductor observation nontrivial half depth ordinal
  have projected := physical_logs observation nontrivial half depth ordinal
  have balance : (input ordinal).2 = raw ordinal - (input ordinal).1 := by
    change _ = (input ordinal).1 + (input ordinal).2 - (input ordinal).1
    simp
  rw [balance, map_sub]
  exact ⟨logPair_sub _ _ _ _ paid.2.1 projected.1,
    logPair_sub _ _ _ _ paid.2.2 projected.2⟩

theorem actual_division_branch_conductor (ordinal : Nat) :
    GammaPair (input ordinal).1 (gamma ordinal).1 ∧
      GammaPair (input ordinal).2 (gamma ordinal).2 := by
  have full := actual_division_conductor observation nontrivial half depth ordinal
  have projected := physical_logs observation nontrivial half depth ordinal
  have outside := outside_logs observation nontrivial half depth ordinal
  have total := gamma_value_of_log_pairs _ _ _ _ full.1 full.2.1 full.2.2
  refine ⟨gamma_pair_of_log_pairs _ _ _ projected.1 projected.2, ?_⟩
  have residual := gamma_pair_of_log_pairs _ _ _ outside.1 outside.2
  change GammaPair (input ordinal).2 (totalGamma ordinal - (physPosition ordinal + F (physInverse ordinal)))
  rw [total]
  have balance : totalPosition ordinal + F (totalInverse ordinal) -
      (physPosition ordinal + F (physInverse ordinal)) =
        (totalPosition ordinal - physPosition ordinal) + F (totalInverse ordinal - physInverse ordinal) := by
    rw [map_sub]
    abel
  rw [balance]
  exact residual

private theorem conductor_unique (value left right : BurnolL2)
    (a : GammaPair value left) (b : GammaPair value right) : left = right := by
  apply ext_inner_left ℂ
  intro cotest
  have dense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  refine dense.induction_on (p := fun u : BurnolL2 => inner ℂ u left = inner ℂ u right) cotest ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro test
    exact (a test).symm.trans (b test)

/-- The actual outside writer and the whole R write generate the two conductor slots of the next input. -/
theorem actual_division_branch_conductor_step (ordinal : Nat) :
    let outside := W c (raw ordinal, (gamma ordinal).2);
    gamma (ordinal+1) = (R c (totalGamma ordinal) - outside, outside) := by
  let outside := W c (raw ordinal, (gamma ordinal).2)
  have old := (actual_division_branch_conductor observation nontrivial half depth ordinal).2
  have oldSlot : O (raw ordinal) = (input ordinal).2 :=
    congrArg Prod.snd (literal_split observation nontrivial half depth ordinal)
  rw [← oldSlot] at old
  have next := (actual_division_branch_conductor observation nontrivial half depth (ordinal+1)).2
  have nextSlot : (input (ordinal+1)).2 = O (R c (raw ordinal)) :=
    congrArg Prod.snd (OriginalKCombFirstFullSourceDynamics.next_pair observation nontrivial half depth ordinal)
  rw [nextSlot] at next
  have written : GammaPair (O (R c (raw ordinal))) outside :=
    OriginalKCrossParameterRAdjointSource.GammaOutsideHistory.write_graph c observation.mathlibZero _ _ old
  have same : (gamma (ordinal+1)).2 = outside := conductor_unique _ _ _ next written
  have whole := (actual_division_conductor_step observation nontrivial half depth ordinal).1
  change gamma (ordinal+1) = (R c (totalGamma ordinal) - outside, outside)
  refine Prod.ext ?_ same
  rw [← same, ← whole]
  exact (sub_sub_cancel _ _).symm

/-- An independently chosen original K reads the conductor of both literal branch slots. -/
theorem actual_division_branch_K_price (ordinal : Nat) (test : BurnolCompletedMellinCoordinate) :
    let K : BurnolL2 := burnolCompletedMellinRieszVector test;
    inner ℂ (actualGammaKernel test) (input ordinal).1 = inner ℂ K (gamma ordinal).1 ∧
      inner ℂ (actualGammaKernel test) (input ordinal).2 = inner ℂ K (gamma ordinal).2 := by
  have original := actual_kernel_complete_log_sources test
  have graph := actual_division_branch_conductor observation nontrivial half depth ordinal
  have physical := physical_logs observation nontrivial half depth ordinal
  have outside := outside_logs observation nontrivial half depth ordinal
  exact ⟨whole_conductor_dual _ _ _ _ _ _ _ _ (actual_gamma_original_kernel test) graph.1
      original.1 original.2 physical.1 physical.2,
    whole_conductor_dual _ _ _ _ _ _ _ _ (actual_gamma_original_kernel test) graph.2
      original.1 original.2 outside.1 outside.2⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.DivisionConductor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
