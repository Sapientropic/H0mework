import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CofinalPaPriceMatrix

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.DenseDivisionPrice

open BurnolPhysicalState Filter Set
open scoped Matrix InnerProductSpace Topology

open private residualFrom residual_from_paid appendInverse emptyInverse from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CofinalPaPriceMatrix
open private residual_live from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CofinalPaCommonProbe
open private live_dense from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPriceCountable
open private continuous_probe_price from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPriceGrid
open private fullRead from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse

open private model_inventory_projection from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory
open private literal_split from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches

open CofinalPaPriceMatrix (Book Slots)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "BookAt" => Book observation nontrivial half depth
local notation "residual" => residualFrom observation nontrivial half depth
local notation "price" => PhysicalPriceCountable.price

private theorem height_in {n : Nat} (old : BookAt n) {U : Set ℝ} (openU : IsOpen U) (present : U.Nonempty) :
    ∃ height ∈ U, ∀ slots, price height (residual old slots) ≠ 0 := by
  let countable : Countable (Slots (n+1)) :=
    (show Function.Injective (fun slots : Slots (n+1) => (slots : Fin (n+1) → Nat)) from
      fun _ _ same => Function.Embedding.ext (fun i => congrFun same i)).countable
  let useful (slots : Slots (n+1)) : Set ℝ := {height | price height (residual old slots) ≠ 0}
  have live (slots : Slots (n+1)) : residual old slots ≠ 0 := by
    intro silent
    have rank := (LocalPaSmear.actual_division_Pa_linearIndependent observation nontrivial half depth).comp
      (slots : Fin (n+1) → Nat) slots.injective
    exact residual_live rank old.1
      ((residual_from_paid observation nontrivial half depth old slots).symm.trans silent)
  have dense : Dense (⋂ slots, useful slots) := dense_iInter_of_isOpen
    (fun slots => isOpen_ne_fun (continuous_probe_price (residual old slots)) continuous_const)
    (fun slots => live_dense (residual old slots) (live slots))
  obtain ⟨height, all, located⟩ := dense.exists_mem_open openU present
  exact ⟨height, located, fun slots => mem_iInter.mp all slots⟩

private def window (rank : Nat) : Set ℝ :=
  Metric.ball (PhysicalPriceGrid.height rank) (1/((rank : ℝ)+1))

private theorem in_window (n : Nat) : PhysicalPriceGrid.height n ∈ window n :=
  Metric.mem_ball_self (by positivity)

private theorem supplied {n : Nat} (old : BookAt n) :
    ∃ height ∈ window n, ∀ slots, price height (residual old slots) ≠ 0 :=
  height_in observation nontrivial half depth old Metric.isOpen_ball ⟨_,in_window n⟩

/-- Use the actual predecessor inverses and a prescribed neighborhood from the original line. -/
def append {n : Nat} (old : BookAt n) : BookAt (n+1) :=
  let supply := supplied observation nontrivial half depth old
  let height := Classical.choose supply
  ⟨Fin.snoc (α := fun _ : Fin (n+1) => ℝ) old.1 height,
    fun slots => appendInverse observation nontrivial half depth old slots height
      ((Classical.choose_spec supply).2 slots)⟩

local notation "step" => append observation nontrivial half depth

private theorem append_retains {n : Nat} (old : BookAt n) (i : Fin n) :
    (step old).1 i.castSucc = old.1 i := by
  simp only [append,Fin.snoc_castSucc]

private theorem append_in_window {n : Nat} (old : BookAt n) :
    (step old).1 (Fin.last n) ∈ window n := by
  simp only [append,Fin.snoc_last]
  exact (Classical.choose_spec (supplied observation nontrivial half depth old)).1

/-- Every prefix gives an inverse at every equally sized set of actual Division slots. -/
def run (rank : Nat) : BookAt rank :=
  Nat.rec (motive := BookAt)
    ⟨Fin.elim0,emptyInverse observation nontrivial half depth⟩ (fun _ old => step old) rank

local notation "bookAt" => run observation nontrivial half depth

def height (n : Nat) : ℝ := (bookAt (n+1)).1 (Fin.last n)

local notation "heightAt" => height observation nontrivial half depth

theorem read_prefix (rank : Nat) (i : Fin rank) :
    (bookAt rank).1 i = heightAt i.val := by
  induction rank with
  | zero => exact Fin.elim0 i
  | succ rank previous =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · exact (append_retains observation nontrivial half depth (bookAt rank) j).trans (previous j)

private theorem height_window (n : Nat) : heightAt n ∈ window n :=
  append_in_window observation nontrivial half depth (bookAt n)

/-- Every tail of the retained heights is dense on the actual original line. -/
theorem tail_dense (cutoff : Nat) : DenseRange (fun i => heightAt (cutoff+i)) := by
  refine Metric.denseRange_iff.mpr ?_
  intro target ε positive
  obtain ⟨q,near⟩ := Metric.denseRange_iff.mp Rat.denseRange_cast target (ε/2) (by positivity)
  obtain ⟨N,small⟩ := exists_nat_one_div_lt (show 0 < ε/2 by positivity)
  let n := Nat.pair ((Denumerable.eqv ℚ) q) (max N cutoff)
  have bound : max N cutoff ≤ n := Nat.right_le_pair _ _
  have after : cutoff ≤ n := (le_max_right _ _).trans bound
  have large : N ≤ n := (le_max_left _ _).trans bound
  have center : PhysicalPriceGrid.height n = (q : ℝ) := by
    simp only [PhysicalPriceGrid.height,n,Nat.unpair_pair,Equiv.symm_apply_apply]
  have realLarge : (N : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast Nat.succ_le_succ large
  have radius : 1/((n : ℝ)+1) < ε/2 :=
    (one_div_le_one_div_of_le (by positivity) realLarge).trans_lt small
  have close := height_window observation nontrivial half depth n
  change dist (heightAt n) (PhysicalPriceGrid.height n) < 1/((n : ℝ)+1) at close
  rw [center,dist_comm] at close
  refine ⟨n-cutoff,?_⟩
  rw [Nat.add_sub_of_le after]
  have split := dist_triangle target (q : ℝ) (heightAt n)
  exact split.trans_lt (by linarith [close.trans radius])

theorem dense_height : DenseRange heightAt := by
  simpa only [Nat.zero_add] using tail_dense observation nontrivial half depth 0

/-- The same retained K prices also separate arbitrary fields on the original physical line. -/
theorem separates (value : BurnolPaAmbientCarrier) (silent : ∀ n, price (heightAt n) value = 0) :
    value = 0 := by
  have everywhere : (fun y : ℝ => price y value) = fun _ => 0 := by
    apply Continuous.ext_on (dense_height observation nontrivial half depth)
      (continuous_probe_price value) continuous_const
    rintro _ ⟨n,rfl⟩
    exact silent n
  exact PhysicalPriceGrid.tail_separates value 0 (fun n => congrFun everywhere (PhysicalPriceGrid.height (0+n)))

open HilbertInventory HilbertInventory.SecondConductorStock
open HilbertInventory.SecondConductorStock.SingleSlot

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down

def address (n : Nat) : Probe :=
  ⟨PhysicalPriceCountable.coordinate (heightAt n),PhysicalPriceCountable.real_part (heightAt n)⟩

local notation "addressAt" => address observation nontrivial half depth

private def physicalRead (x : Wide) : BurnolPaAmbientCarrier :=
  burnolEvenAmbientProjection (fullRead (x : Ambient))

/-- Read the actual full projection used by the original closed graph. -/
def record (x : Wide) (tests : Finset Nat) : SourceGeneratedFiniteGram.Coordinates tests :=
  WithLp.toLp 2 (fun i : tests => price (heightAt i.val) (physicalRead x))

private theorem record_rhs (x : Wide) (tests : Finset Nat) :
    record observation nontrivial half depth x tests =
      SourceGeneratedFiniteGram.Projection.rhs (fun i : tests => covector (addressAt i.val)) x := by
  ext i
  change price (heightAt i.val) (physicalRead x) = inner ℂ (covector (addressAt i.val)) x
  exact (PhysicalPriceCountable.price_is_original_K (heightAt i.val) (physicalRead x)).trans
    (covector_read (addressAt i.val) x).symm

private theorem cotests_separate (x : Wide) (silent : ∀ n, inner ℂ (covector (addressAt n)) x = 0) :
    x = 0 := by
  have quiet (n : Nat) : price (heightAt n) (physicalRead x) = 0 :=
    (PhysicalPriceCountable.price_is_original_K (heightAt n) (physicalRead x)).trans
      ((covector_read (addressAt n) x).symm.trans (silent n))
  have zero := separates observation nontrivial half depth (physicalRead x) quiet
  apply observe_injective
  rw [map_zero]
  change ((physicalRead x : BurnolPaAmbientCarrier) : BurnolL2) = 0
  rw [zero]
  rfl

/-- The existing directed Gram inverse consumes the very same retained address stream. -/
def fit (tests : Finset Nat) (readings : SourceGeneratedFiniteGram.Coordinates tests) : Wide :=
  SourceGeneratedFiniteGram.PrefixReadback.inverse
    (fun i : tests => covector (addressAt i.val)) readings

local notation "fitAt" => fit observation nontrivial half depth
local notation "measureAt" => record observation nontrivial half depth

private def prefixFit (x : Wide) (n : Nat) : Wide :=
  fitAt (Finset.range n) (measureAt x (Finset.range n))

local notation "recover" => prefixFit observation nontrivial half depth

theorem graph_recovery (x : Wide) : Tendsto (recover x) atTop (𝓝 x) := by
  have actual := @SourceGeneratedFiniteGram.PrefixReadback.inverse_tendsto_finset Wide Nat
    (inferInstanceAs (NormedAddCommGroup Wide)) HilbertInventory.SecondConductorStock.SingleSlot.wideInner
    (inferInstanceAs (CompleteSpace Wide)) (inferInstanceAs (DecidableEq Nat))
    (fun n : Nat => covector (addressAt n)) (cotests_separate observation nontrivial half depth) x
  have directed : Tendsto (fun tests => fitAt tests (measureAt x tests)) atTop (𝓝 x) := by
    simpa only [fit,record_rhs] using actual
  exact directed.comp tendsto_finset_range

open OriginalKCofinalFullBranchFibre (SourcePair sourceStep)
namespace Action
export OriginalKCombPhysicalAction (physicalProjection physicalRemainder)
end Action

private def split (x : Wide) : SourcePair :=
  (Action.physicalProjection (fullRead (x : Ambient)),Action.physicalRemainder (fullRead (x : Ambient)))

/-- The graph read uses the actual full source field to regenerate both relation branches. -/
def relationStock (x : Wide) : WholeBranchStock :=
  (wholeCoordinates c (fullRead (x : Ambient)),Action.physicalRemainder (fullRead (x : Ambient)))

local notation "relations" => relationStock observation half

private theorem relation_from_pair (x : Wide) : relations x = branchCoordinates c (split x) := by
  change (wholeCoordinates c (fullRead (x : Ambient)),_) =
    (wholeCoordinates c ((split x).1+(split x).2),_)
  exact Prod.ext (congrArg (wholeCoordinates c)
    (OriginalKCombFullResidualAction.split_complete (fullRead (x : Ambient))).symm) rfl

private theorem relation_continuous : Continuous relations := by
  have raw : Continuous (fun x : Wide => fullRead (x : Ambient)) :=
    fullRead.continuous.comp continuous_subtype_val
  exact ((wholeCoordinates c).continuous.comp raw).prodMk (Action.physicalRemainder.continuous.comp raw)

include nontrivial in
theorem relation_advance (x : Wide) :
    advanceStock c (relations x) = relations (advanceWide c observation.mathlibZero x) := by
  let next := advanceWide c observation.mathlibZero x
  have full : fullRead (next : Ambient) =
      burnolDirectRightResolventCLM c (fullRead (x : Ambient)) :=
    LogStock.advance_field c (base (toWhole x))
  have sum : (split x).1 + (split x).2 = fullRead (x : Ambient) :=
    OriginalKCombFullResidualAction.split_complete _
  have pair : sourceStep observation nontrivial half (split x) = split next := by
    change (Action.physicalProjection (OriginalKCombPhysicalAction.R observation nontrivial half
      ((split x).1+(split x).2)),
      Action.physicalRemainder (OriginalKCombPhysicalAction.R observation nontrivial half ((split x).1+(split x).2))) =
      (Action.physicalProjection (fullRead (next : Ambient)),
       Action.physicalRemainder (fullRead (next : Ambient)))
    have native : OriginalKCombPhysicalAction.R observation nontrivial half (fullRead (x : Ambient)) =
        fullRead (next : Ambient) :=
      (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half _).trans full.symm
    rw [sum,native]
  calc
    _ = advanceStock c (branchCoordinates c (split x)) :=
      congrArg (advanceStock c) (relation_from_pair observation half x)
    _ = branchCoordinates c (sourceStep observation nontrivial half (split x)) :=
      actual_stock_source_step observation nontrivial half (split x)
    _ = branchCoordinates c (split next) := congrArg (branchCoordinates c) pair
    _ = relations next := (relation_from_pair observation half next).symm

local notation "graphAt" => actualWide observation nontrivial half depth
local notation "classAt" => Rel.sourceClass observation nontrivial half depth
local notation "stockAt" => relationInventory observation nontrivial half depth

private theorem relation_actual (ordinal : Nat) :
    relations (graphAt ordinal) = stockAt ordinal (classAt ordinal) := by
  let input := OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth ordinal
  have read : split (graphAt ordinal) = input :=
    literal_split observation nontrivial half depth ordinal
  have current : relations (graphAt ordinal) = branchCoordinates c input :=
    (relation_from_pair observation half (graphAt ordinal)).trans (congrArg (branchCoordinates c) read)
  have stock : stockAt ordinal (classAt ordinal) = branchCoordinates c input :=
    (congrArg (modelInventory observation nontrivial half)
      (Rel.factor_source_class observation nontrivial half depth ordinal)).trans
      (model_inventory_projection observation nontrivial half input)
  exact current.trans stock.symm

private theorem change_limit {Y : Type*} [TopologicalSpace Y] {f : Nat → Y} {x y : Y}
    (limit : Tendsto f atTop (𝓝 x)) (read : x = y) : Tendsto f atTop (𝓝 y) := by
  cases read
  exact limit

private theorem recovered_next (ordinal : Nat) :
    Tendsto (fun n => advanceWide c observation.mathlibZero (recover (graphAt ordinal) n)) atTop
      (𝓝 (graphAt (ordinal+1))) :=
  change_limit (((advanceWide c observation.mathlibZero).continuous.tendsto _).comp
    (graph_recovery observation nontrivial half depth (graphAt ordinal)))
    (actual_wide_next observation nontrivial half depth ordinal)

private theorem recovered_relation (ordinal : Nat) :
    Tendsto (fun n => relations (recover (graphAt ordinal) n)) atTop (𝓝 (stockAt ordinal (classAt ordinal))) :=
  change_limit (((relation_continuous observation half).tendsto _).comp
    (graph_recovery observation nontrivial half depth (graphAt ordinal)))
    (relation_actual observation nontrivial half depth ordinal)

private theorem recovered_relation_next (ordinal : Nat) :
    Tendsto (fun n => advanceStock c (relations (recover (graphAt ordinal) n))) atTop
      (𝓝 (stockAt (ordinal+1) (classAt (ordinal+1)))) := by
  let approximants := recover (graphAt ordinal)
  have read : Tendsto (fun n => relations (advanceWide c observation.mathlibZero (approximants n))) atTop
      (𝓝 (relations (graphAt (ordinal+1)))) :=
    ((relation_continuous observation half).tendsto _).comp
      (recovered_next observation nontrivial half depth ordinal)
  have moved := change_limit read (relation_actual observation nontrivial half depth (ordinal+1))
  exact moved.congr (fun n => (relation_advance observation nontrivial half (approximants n)).symm)

/-- The actual retained prefixes recover the full closed graph and relation stock at both native epochs. -/
theorem actual_current_next (ordinal : Nat) :
    let approximants := recover (graphAt ordinal)
    Tendsto approximants atTop (𝓝 (graphAt ordinal)) ∧
      Tendsto (fun n => advanceWide c observation.mathlibZero (approximants n)) atTop (𝓝 (graphAt (ordinal+1))) ∧
      Tendsto (fun n => relations (approximants n)) atTop (𝓝 (stockAt ordinal (classAt ordinal))) ∧
      Tendsto (fun n => advanceStock c (relations (approximants n))) atTop
        (𝓝 (stockAt (ordinal+1) (classAt (ordinal+1)))) :=
  ⟨graph_recovery observation nontrivial half depth (graphAt ordinal),
    recovered_next observation nontrivial half depth ordinal,
    recovered_relation observation nontrivial half depth ordinal,
    recovered_relation_next observation nontrivial half depth ordinal⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.DenseDivisionPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
