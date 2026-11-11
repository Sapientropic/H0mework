import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixReadback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LogStockAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FiniteHeadInverse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.LogStock

open BurnolPhysicalState Filter DivisionConductor
open OriginalGamma.Source.ConductorDual OriginalGamma.Source.RelativeConductorGapReadback
open scoped InnerProductSpace lp Topology

open private finiteHeadData from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FiniteHeadInverse
open private current from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients
open private literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches

namespace Prefix
export SourceGeneratedFiniteGram.PrefixReadback (inverse inverse_tendsto)
end Prefix

local notation "R" => burnolDirectRightResolventCLM
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "F" => fourierL2
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate

private def graphCotest (c : BurnolCompletedMellinCoordinate) (i : Nat) : Whole :=
  carrier.orthogonalProjectionOnto
    (WithLp.toLp 2 (((basis c).repr.symm (hankelCotest c i) : BurnolL2), 0))

private theorem cotest_read (c : BurnolCompletedMellinCoordinate) (i : Nat) (x : Whole) :
    inner ℂ (graphCotest c i) x = hankel c (coordinates c x) i := by
  let probe := (basis c).repr.symm (hankelCotest c i)
  have actual := carrier.inner_orthogonalProjectionOnto_eq_of_mem_right x
    (WithLp.toLp 2 ((probe : BurnolL2), (0 : LogSlots)))
  change inner ℂ (graphCotest c i) x = inner ℂ (WithLp.toLp 2 ((probe : BurnolL2), (0 : LogSlots)))
    (x : AmbientStock) at actual
  rw [actual, WithLp.prod_inner_apply]
  change inner ℂ (probe : BurnolL2) (field x) + inner ℂ (0 : LogSlots) x.val.snd = _
  rw [inner_zero_left, add_zero, ← actual_hankel_cotest]
  have pulled := (basis c).repr.inner_map_map probe (⟨field x, field_mem x⟩ : PositionField)
  rw [show (basis c).repr probe = hankelCotest c i from (basis c).repr.apply_symm_apply _] at pulled
  exact pulled.symm

/-- The same finite head data drives the Gram action of the actual graph cotests. -/
def finiteGraphInverse (c : BurnolCompletedMellinCoordinate) (n : Nat) (heads : Nat → ℂ) : Whole :=
  Prefix.inverse (fun i : Fin n => graphCotest c i) (finiteHeadData c n heads)

theorem finiteGraphInverse_tendsto (c : BurnolCompletedMellinCoordinate) (x : Whole) :
    Tendsto (fun n => finiteGraphInverse c n (fourierHeadHistory c (coordinates c x))) atTop (𝓝 x) := by
  have separates : ∀ y : Whole, (∀ i : Nat, inner ℂ (graphCotest c i) y = 0) → y = 0 := by
    intro y silent
    apply coordinates_injective c
    apply hankel_injective c
    rw [map_zero, map_zero]
    exact lp.ext (funext fun i => (cotest_read c i y).symm.trans (silent i))
  have data (n : Nat) : finiteHeadData c n (fourierHeadHistory c (coordinates c x)) =
      Gram.rhs (fun i : Fin n => graphCotest c i) x := by
    ext i
    change waveFromHeads c (fourierHeadHistory c (coordinates c x)) (i : Nat) 0 = inner ℂ (graphCotest c i) x
    rw [actual_wave_from_heads, Function.iterate_zero, id_eq, cotest_read]
  simpa only [finiteGraphInverse, data] using Prefix.inverse_tendsto (graphCotest c) separates x

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "g" => branchGammaAt observation nontrivial half depth

/-- The complete graph at the literal current consumes the original Division's two generated log fields. -/
def actualAt (ordinal : Nat) : Whole :=
  let logs := actual_division_conductor observation nontrivial half depth ordinal
  ofLogs (current observation nontrivial half depth ordinal) _ _ logs.2.1 logs.2.2

local notation "actual" => actualAt observation nontrivial half depth

theorem actual_graph_next (ordinal : Nat) : advance c (actual ordinal) = actual (ordinal+1) := by
  apply field_injective
  rw [advance_field]
  change R c (raw ordinal) = raw (ordinal+1)
  exact (OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth ordinal).symm

theorem actual_graph_slots (ordinal : Nat) :
    let slots := split (actual ordinal);
    (field slots.1, field slots.2) = input ordinal ∧ (gamma slots.1, gamma slots.2) = g ordinal := by
  let slots := split (actual ordinal)
  let v := raw ordinal
  have balance : P v + O v = v :=
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal v
  have outside : v - P v = O v := sub_eq_iff_eq_add.mpr ((add_comm _ _).trans balance).symm
  have pair : (field slots.1, field slots.2) = input ordinal := by
    change (field (physical (actual ordinal)), field (actual ordinal - physical (actual ordinal))) = input ordinal
    rw [map_sub, physical_field]
    change (P v, v - P v) = input ordinal
    rw [outside]
    exact literal_split observation nontrivial half depth ordinal
  have paid := actual_division_branch_conductor observation nontrivial half depth ordinal
  have pos := congrArg Prod.fst pair
  have ext := congrArg Prod.snd pair
  change field slots.1 = (input ordinal).1 at pos
  change field slots.2 = (input ordinal).2 at ext
  rw [← pos, ← ext] at paid
  refine ⟨pair, Prod.ext ?_ ?_⟩
  · exact (gamma_value_of_log_pairs _ _ _ _ paid.1 (log_pairs slots.1).1 (log_pairs slots.1).2).symm
  · exact (gamma_value_of_log_pairs _ _ _ _ paid.2 (log_pairs slots.2).1 (log_pairs slots.2).2).symm

/-- One finite history recovers both original branch pairs, including their separate log fields, in norm. -/
theorem actual_division_finite_graph_recovery (ordinal : Nat) :
    let heads := fun time => normalization (d c) * M c (F (raw (ordinal+time)));
    Tendsto (fun n => split (finiteGraphInverse c n heads)) atTop (𝓝 (split (actual ordinal))) ∧
    Tendsto (fun n => split (advance c (finiteGraphInverse c n heads)))
      atTop (𝓝 (split (actual (ordinal+1)))) := by
  let heads := fun time => normalization (d c) * M c (F (raw (ordinal+time)))
  have history : fourierHeadHistory c (coordinates c (actual ordinal)) = heads :=
    funext (actual_division_head_history observation nontrivial half depth ordinal)
  have recovered := finiteGraphInverse_tendsto c (actual ordinal)
  rw [history] at recovered
  have first := (split.continuous.tendsto (actual ordinal)).comp recovered
  have second := ((split.comp (advance c)).continuous.tendsto (actual ordinal)).comp recovered
  change Tendsto (fun n => split (advance c (finiteGraphInverse c n heads))) atTop
    (𝓝 (split (advance c (actual ordinal)))) at second
  rw [actual_graph_next] at second
  exact ⟨first, second⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.LogStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
