import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedProgramSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.Consumer

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedDivision

open BurnolPhysicalState Filter Set SourceOperationEffects SourceOperationScalarInventoryLift
open scoped Topology BigOperators

open private seed from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedProgramTrace
open private index_pos tailStart compensation from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedContinuousInverse
open private scale gap gap_pos loss loss_pos from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedWord
open private clock q field_error relative_bound tail from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedFiniteFlow
open private meshTail_apply orbit phase step_nonneg scaleMass transportSpeed from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedMassMesh
open private right_quarter from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "R" => burnolDirectRightResolventCLM
local notation "I" => BoundaryCountedContinuousInverse.index
local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "word" => BoundaryCountedFiniteFlow.word

private def precision (n : Nat) : ℝ := ((n+1 : Nat) : ℝ)⁻¹

/-- All branches of the same source use a common count, mesh and word length. -/
def sharedLength (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) : Nat :=
  SourceGeneratedFiniteInverseWord.cutoff (loss (coordinate.value/2) n) 1 (precision n)

def commonWord (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) : End :=
  -word (coordinate.value/2) n (n+1) (sharedLength coordinate n)

private theorem precision_pos (n : Nat) : 0 < precision n := by
  unfold precision
  exact inv_pos.mpr (by exact_mod_cast Nat.succ_pos n)

private theorem precision_tendsto : Tendsto precision atTop (𝓝 0) := by
  have paid := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
  have same : (fun n : Nat => (1 : ℝ)/(n : ℝ)) ∘ (fun n : Nat => n+1) = precision := by
    funext n
    change (1 : ℝ)/((n+1 : Nat) : ℝ) = precision n
    exact one_div _
  rw [same] at paid
  exact paid

private theorem shared_tail (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
    (1-loss (coordinate.value/2) n)^sharedLength coordinate n ≤ precision n := by
  let z := coordinate.value/2
  have right : 1/4 < z.re := right_quarter coordinate
  have lossLe : loss z n ≤ 1 := sub_nonneg.mp
    ((norm_nonneg _).trans (relative_bound z right n (n+1) (Nat.succ_pos n)))
  have paid := SourceGeneratedFiniteInverseWord.cutoff_pays (loss z n) 1 (precision n)
    (loss_pos z right n) lossLe zero_le_one (precision_pos n)
  rw [mul_one] at paid
  exact paid.le

private theorem original_clock_tendsto (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    Tendsto (fun n : Nat => BoundaryCountedGenerator.clock (coordinate.value/2) (I (coordinate.value/2) n)
      (index_pos (coordinate.value/2) n) (-(R coordinate value))) atTop (𝓝 value) := by
  let z := coordinate.value/2
  have paid := (BoundaryCountedGenerator.clock_applied_tendsto z (right_quarter coordinate) value).comp
    (tendsto_add_atTop_nat (tailStart z))
  have same : (fun n : Nat => BoundaryCountedGenerator.clock z (I z n) (index_pos z n) (-(R coordinate value))) =
      (fun n : Nat => BoundaryCountedGenerator.clock z (n+1) (Nat.succ_pos n)
        (-burnolDirectRightResolvent z value)) ∘ (fun n : Nat => n+tailStart z) := by
    funext n
    change BoundaryCountedGenerator.clock z (I z n) (index_pos z n) (-burnolDirectRightResolvent z value) = _
    simp only [Function.comp_apply, BoundaryCountedContinuousInverse.index, Nat.add_comm n (tailStart z)]
  rw [same]
  exact paid

private theorem field_bound (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (n : Nat) :
    ‖commonWord coordinate n value-R coordinate value‖ ≤
      (gap (coordinate.value/2))⁻¹*
        (‖BoundaryCountedGenerator.clock (coordinate.value/2) (I (coordinate.value/2) n)
          (index_pos (coordinate.value/2) n) (-(R coordinate value))-value‖ +
         transportSpeed coordinate * ‖value‖ * precision n) +
      precision n * ‖R coordinate value‖ := by
  let z := coordinate.value/2
  let N := I z n
  let x := -(R coordinate value)
  let e := clock z n (n+1)
  let a := BoundaryCountedGenerator.clock z N (index_pos z n)
  let k := sharedLength coordinate n
  have right : 1/4 < z.re := right_quarter coordinate
  have xBorn : x = R coordinate (-value) := (map_neg _ _).symm
  have mesh := BoundaryCountedMassMesh.mesh_error coordinate (-value) N (n+1) (index_pos z n) (Nat.succ_pos n)
  rw [← xBorn, norm_neg, div_eq_mul_inv] at mesh
  have joined : e x-value = (a x-value) +
      (compensation N (index_pos z n) x-BoundaryCountedMassMesh.meshTail N (n+1) x) := by
    change (scale z n • x - BoundaryCountedMassMesh.meshTail N (n+1) x)-value =
      ((scale z n • x - compensation N (index_pos z n) x)-value) +
        (compensation N (index_pos z n) x-BoundaryCountedMassMesh.meshTail N (n+1) x)
    abel
  have clockError : ‖e x-value‖ ≤ ‖a x-value‖+transportSpeed coordinate*‖value‖*precision n := by
    rw [joined]
    exact (norm_add_le _ _).trans (add_le_add le_rfl mesh)
  have bound := field_error z right n (n+1) k (Nat.succ_pos n) value x
  change ‖-(word z n (n+1) k value)-R coordinate value‖ ≤ _
  rw [show -(word z n (n+1) k value)-R coordinate value = x-word z n (n+1) k value by
    dsimp only [x]; abel]
  calc
    _ ≤ (gap z)⁻¹*‖e x-value‖+(1-loss z n)^k*‖x‖ := bound
    _ ≤ _ := by
      have sameNorm : ‖x‖ = ‖R coordinate value‖ := norm_neg _
      rw [sameNorm]
      exact add_le_add (mul_le_mul_of_nonneg_left clockError (inv_nonneg.mpr (gap_pos z right).le))
        (mul_le_mul_of_nonneg_right (shared_tail coordinate n) (norm_nonneg _))

/-- The fully finite word converges on every input of the complete source carrier. -/
theorem common_tendsto (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    Tendsto (fun n : Nat => commonWord coordinate n value) atTop (𝓝 (R coordinate value)) := by
  let z := coordinate.value/2
  have clockError : Tendsto (fun n : Nat => ‖BoundaryCountedGenerator.clock z (I z n) (index_pos z n)
      (-(R coordinate value))-value‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((original_clock_tendsto coordinate value).sub (tendsto_const_nhds (x := value))).norm
  have mesh := precision_tendsto.const_mul (transportSpeed coordinate*‖value‖)
  have first := (clockError.add mesh).const_mul (gap z)⁻¹
  have second := precision_tendsto.mul_const ‖R coordinate value‖
  have total := first.add second
  simp only [mul_zero, zero_add, zero_mul] at total
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (field_bound coordinate value)) total

private theorem mesh_gap (N mesh : Nat) (value : BurnolL2) (inside : value ∈ G) :
    BoundaryCountedMassMesh.meshTail N mesh value ∈ G := by
  rw [meshTail_apply, SourceGeneratedUnitMesh.average]
  change ((N : ℂ) • ((scaleMass N : ℝ) : ℂ) • (((mesh : ℝ)⁻¹ : ℝ) : ℂ) •
    ∑ j ∈ Finset.range mesh, orbit N (SourceGeneratedUnitMesh.node mesh (j+1)) value) ∈ G
  refine Submodule.smul_mem G _ (Submodule.smul_mem G _ (Submodule.smul_mem G _ (Submodule.sum_mem G (fun j _ => ?_))))
  have address : 0 ≤ SourceGeneratedUnitMesh.node mesh (j+1) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have phaseNonneg : 0 ≤ phase N (SourceGeneratedUnitMesh.node mesh (j+1)) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (le_add_of_nonneg_right (mul_nonneg (step_nonneg N) address)))
  exact burnolMultiplicativeDilation_mem_locallyConstantFace_of_nonpositive _ (by norm_num [burnolUnscaledCommonGapRadius])
    _ (neg_nonpos.mpr phaseNonneg) value inside

/-- The complete finite action keeps the source position face before any projection. -/
theorem common_gap (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (value : BurnolL2)
    (inside : value ∈ G) : commonWord coordinate n value ∈ G := by
  let z := coordinate.value/2
  let d := tail z n (n+1)
  let p := q z n (n+1)
  have step (x : BurnolL2) (hx : x ∈ G) : p x ∈ G := by
    change (scale z n)⁻¹ • BoundaryCountedMassMesh.meshTail (I z n) (n+1) x ∈ G
    exact Submodule.smul_mem G _ (mesh_gap (I z n) (n+1) x hx)
  have powers (j : Nat) : (p^j) value ∈ G := by
    induction j with
    | zero => exact inside
    | succ j previous =>
      rw [pow_succ']
      exact step _ previous
  change -((scale z n)⁻¹ • (∑ j ∈ Finset.range (sharedLength coordinate n), p^j) : End) value ∈ G
  simp only [smul_apply, sum_apply]
  exact Submodule.neg_mem G (Submodule.smul_mem G _ (Submodule.sum_mem G (fun j _ => powers j)))

namespace Trace
export BoundaryCountedProgramTrace (Value Var environment expression expression_eval Stock)
end Trace

private theorem environment_add (x y : BurnolL2) : Trace.environment x + Trace.environment y = Trace.environment (x+y) := by
  funext slot name
  cases slot
  · rfl
  · change seed x + seed y = seed (x+y)
    exact (map_add seed x y).symm

def jointCode (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
    Expr.{0,0,0} (PairValue Trace.Value) Trace.Var .orbit :=
  liftExpr (Trace.expression (coordinate.value/2) n (n+1) (sharedLength coordinate n))

def jointEnvironment (x y : BurnolL2) : Env.{0,0,0} (PairValue Trace.Value) Trace.Var :=
  pairEnvironment (Trace.environment x) (Trace.environment y)

def decode (stock : Trace.Stock × Trace.Stock) : BurnolL2 × BurnolL2 :=
  (-(stock.1.2.1), -(stock.2.2.1))

/-- One paired operation carries the complete finite action on the two source legs. -/
def jointWord (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (x y : BurnolL2) : BurnolL2 × BurnolL2 :=
  decode ((jointCode coordinate n).eval (jointEnvironment x y))

theorem jointWord_read (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (x y : BurnolL2) :
    jointWord coordinate n x y = (commonWord coordinate n x, commonWord coordinate n y) := by
  let z := coordinate.value/2
  let m := sharedLength coordinate n
  let w := word z n (n+1) m
  let expr := Trace.expression z n (n+1) m
  let old := Trace.environment x
  let inc := Trace.environment y
  have first : expr.eval old = (x,w x,0) := Trace.expression_eval z n (n+1) m x
  have combined : expr.eval (old+inc) = (x+y,w (x+y),0) := by
    change expr.eval (Trace.environment x+Trace.environment y) = _
    rw [environment_add]
    exact Trace.expression_eval z n (n+1) m (x+y)
  have together := expr.eval_update old inc
  rw [first, combined] at together
  have split : ((x,w x,0) : Trace.Stock)+(y,w y,0) = (x+y,w (x+y),0) := by
    simp only [Prod.mk_add_mk, map_add, zero_add]
  rw [← split] at together
  have effect : expr.effect old inc = (y,w y,0) := (add_left_cancel together).symm
  have read := eval_liftExpr expr old inc
  rw [first, effect] at read
  change (-( (liftExpr expr).eval (pairEnvironment old inc)).1.2.1,
    -( (liftExpr expr).eval (pairEnvironment old inc)).2.2.1) = (-w x,-w y)
  rw [read]

namespace Division
export OriginalKDirectRCofinalDivision (sourceResponse source_response_value source_response_positionGap actual_R_source_split actual_Q_successor)
end Division

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "pa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth
local notation "response" => Division.sourceResponse observation nontrivial half depth
local notation "invisible" => OriginalKCombCofinalPaAction.invisible

/-- Both actual Division legs use one finite word, with the position face retained at every stage. -/
theorem actual_division (ordinal : Nat) :
    let applyBoth := fun n : Nat => jointWord c n (pa ordinal : BurnolL2) (invisible (raw ordinal))
    (∀ n : Nat, (applyBoth n).1 ∈ G) ∧
    Tendsto applyBoth atTop (𝓝 ((response ordinal : BurnolL2), OriginalKCombPhysicalAction.R observation nontrivial half
        (invisible (raw ordinal)))) ∧
    Tendsto (fun n : Nat => (applyBoth n).1+(applyBoth n).2) atTop (𝓝 (raw (ordinal+1))) := by
  dsimp only
  simp only [jointWord_read]
  have first := common_tendsto c (pa ordinal : BurnolL2)
  have second := common_tendsto c (invisible (raw ordinal))
  have written : (response ordinal : BurnolL2) = R c (pa ordinal : BurnolL2) := by
    rw [Division.source_response_value, OriginalKCombCofinalRAction.original_R_direct observation nontrivial half]
    rfl
  have hidden : OriginalKCombPhysicalAction.R observation nontrivial half (invisible (raw ordinal)) =
      R c (invisible (raw ordinal)) :=
    OriginalKCombCofinalRAction.original_R_direct observation nontrivial half _
  rw [← written] at first
  rw [← hidden] at second
  refine ⟨fun n => common_gap c n _ (pa ordinal).property.1.1, first.prodMk_nhds second, ?_⟩
  rw [Division.actual_R_source_split observation nontrivial half depth ordinal]
  exact first.add second

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedDivision
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
