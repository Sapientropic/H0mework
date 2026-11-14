import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPriceGrid
import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.EmittedPaInnovation

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.EmittedPaPrices

open BurnolPhysicalState Finset
open HilbertInventory (modelInventory advanceStock)
open HilbertInventory.SecondConductorStock.SingleSlot
open EmittedPaInnovation
open private toRange from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private rebuildBirth from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback
open private replay_as_synthesis from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord

namespace Sparse
export SourceGeneratedFiniteGram.CofinalRecord
  (sample withBirth replay birthResidual priorFit decodeInsert columns
    Schedule schedule schedule_last pivotTime pivot_nonzero schedule_read_insert)
end Sparse

namespace Fit
export SourceGeneratedFiniteGram.Projection (synthesis predictable_source predictable_readback)
end Fit

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "Event" => RetainedRecord.Progress observation nontrivial half depth
local notation "State" => RetainedMatrix.MatrixState observation nontrivial half depth
local notation "pa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "paired" => physicalPair observation nontrivial half depth

private def clock {start n : Nat} (event : Event start n) : Nat :=
  event.record.times (Fin.last n)

private theorem clock_actual {start n : Nat} (event : Event start n) :
    clock observation nontrivial half depth event =
      candidateTime observation nontrivial half depth start n (paidPivot observation nontrivial half depth start n) :=
  (congrFun event.record.times_actual _).trans
    (actual_paid_pivot_time observation nontrivial half depth start n).symm

/-- The finite rows read the emitted material. The remaining indices use its existing cofinal continuation. -/
private def actorColumn {start n : Nat} (event : Event start n) (j : Nat) : BurnolPaAmbientCarrier :=
  if within : j < n+1 then (paired event ⟨j,within⟩).1
  else pa (start+j+clock observation nontrivial half depth event)

private theorem actor_column_actual {start n : Nat} (event : Event start n) (j : Nat) :
    actorColumn observation nontrivial half depth event j =
      pa (start+j+clock observation nontrivial half depth event) := by
  by_cases within : j < n+1
  · rw [actorColumn, dif_pos within, clock_actual]
    exact congrArg Prod.fst (physical_pair_actual observation nontrivial half depth event ⟨j,within⟩)
  · rw [actorColumn, dif_neg within]

private def columnPrices {start n : Nat} (event : Event start n) (j t : Nat) : ℂ :=
  PhysicalPriceGrid.price t (actorColumn observation nontrivial half depth event j)

local notation "source" => columnPrices observation nontrivial half depth

private theorem separates {start n : Nat} (event : Event start n) (cutoff : Nat) :
    LinearIndependent ℂ (fun j : Nat => fun t : Nat => source event j (cutoff+t)) := by
  apply PhysicalPriceGrid.independent_tail
  have actual : actorColumn observation nontrivial half depth event =
      fun j => pa (start+j+clock observation nontrivial half depth event) :=
    funext (actor_column_actual observation nontrivial half depth event)
  rw [actual]
  exact (LocalPaSmear.actual_division_Pa_linearIndependent observation nontrivial half depth).comp
    (fun j => start+j+clock observation nontrivial half depth event) (fun i j same => by
      change start+i+clock observation nontrivial half depth event =
        start+j+clock observation nontrivial half depth event at same
      omega)

abbrev Queries {start n : Nat} (event : Event start n) :=
  Σ retained : Sparse.Schedule (source event) n,
    {time : Nat // time = Sparse.pivotTime (source event)
      (separates observation nontrivial half depth event) retained.val}

/-- The existing cofinal schedule selects the next actual original K price on the paid physical row. -/
def queries {start n : Nat} (event : Event start n) : Queries observation nontrivial half depth event :=
  let retained := Sparse.schedule (source event) (separates observation nontrivial half depth event) n
  ⟨retained, ⟨Sparse.pivotTime (source event) (separates observation nontrivial half depth event) retained.val, rfl⟩⟩

local notation "Book" => Queries observation nontrivial half depth
local notation "choose" => queries observation nontrivial half depth

def sampleAt {start n : Nat} (event : Event start n) (book : Book event)
    (material : BurnolPaAmbientCarrier) : Record.Values n × ℂ :=
  (Sparse.sample book.1.val (fun i => PhysicalPriceGrid.price i material), PhysicalPriceGrid.price book.2.val material)

def recoverAt {start n : Nat} (event : Event start n) (book : Book event)
    (data : Record.Values n × ℂ) : Record.Values n × ℂ :=
  Sparse.decodeInsert (source event) book.1.val book.2.val data.1 data.2

private theorem old_residual_zero {start n : Nat} (event : Event start n) (book : Book event) (i : Fin n) :
    Sparse.birthResidual (source event) book.1.val (book.1.val i) = 0 := by
  let retained := book.1.val
  let synthesis := Fit.synthesis (Sparse.columns (source event) retained)
  let born := Sparse.sample retained (source event n)
  have onto : Function.Surjective synthesis := LinearMap.injective_iff_surjective.mp book.1.property
  have covered : born ∈ LinearMap.range synthesis := onto born
  have fits : synthesis (Sparse.priorFit (source event) retained) = born := by
    change Fit.synthesis (Sparse.columns (source event) retained)
      (SourceGeneratedFiniteGram.Projection.coefficients (Sparse.columns (source event) retained) born) = born
    rw [← Fit.predictable_source, Fit.predictable_readback, Submodule.starProjection_eq_self_iff.mpr covered]
  change Fit.synthesis (Sparse.columns (source event) retained)
    (Sparse.priorFit (source event) retained) = born at fits
  rw [replay_as_synthesis] at fits
  have actual := congrArg (fun data : Record.Values n => data i) fits
  exact sub_eq_zero.mpr actual.symm

/-- Although the rational clock repeats, the newborn query uses a different original K coordinate. -/
theorem chosen_coordinate_fresh {start n : Nat} (event : Event start n) (i : Fin n) :
    PhysicalPriceGrid.coordinate (choose event).2.val ≠ PhysicalPriceGrid.coordinate ((choose event).1.val i) := by
  let book := choose event
  have live : Sparse.birthResidual (source event) book.1.val book.2.val ≠ 0 := by
    rw [book.2.property]
    exact Sparse.pivot_nonzero (source event) (separates observation nontrivial half depth event) book.1.val
  intro same
  have prices (j : Nat) : source event j book.2.val = source event j (book.1.val i) :=
    congrArg (fun coordinate => burnolCompletedMellinEvaluator coordinate
      (actorColumn observation nontrivial half depth event j)) same
  have residual : Sparse.birthResidual (source event) book.1.val book.2.val =
      Sparse.birthResidual (source event) book.1.val (book.1.val i) := by
    simp only [Sparse.birthResidual, Sparse.replay, prices]
  exact live (residual.trans (old_residual_zero observation nontrivial half depth event book i))

private theorem mixture_price {start n : Nat} (event : Event start n) (a : Record.Values n) (b : ℂ) :
    (fun i => PhysicalPriceGrid.price i (physicalMixture (fun j => (paired event j).1) a b)) =
      Sparse.withBirth (source event) a b := by
  funext t
  have original (j : Fin (n+1)) :
      source event j.val t = PhysicalPriceGrid.price t (paired event j).1 := by
    change PhysicalPriceGrid.price t (actorColumn observation nontrivial half depth event j.val) = _
    rw [actorColumn, dif_pos j.isLt]
  change PhysicalPriceGrid.price t
      ((∑ j : Fin n, a j • (paired event j.castSucc).1) + b • (paired event (Fin.last n)).1) = _
  simp only [map_add, map_sum, map_smul, smul_eq_mul, Sparse.withBirth, Sparse.replay,
    ← original, Fin.val_castSucc, Fin.val_last]

theorem current_price_inverse {start n : Nat} (event : Event start n) (a : Record.Values n) (b : ℂ) :
    let book := choose event
    recoverAt observation nontrivial half depth event book
      (sampleAt observation nontrivial half depth event book
        (physicalMixture (fun j => (paired event j).1) a b)) = (a,b) := by
  let book := choose event
  let values := fun i => PhysicalPriceGrid.price i (physicalMixture (fun j => (paired event j).1) a b)
  change Sparse.decodeInsert (source event) book.1.val book.2.val (Sparse.sample book.1.val values) (values book.2.val) = _
  have observed : values = Sparse.withBirth (source event) a b :=
    mixture_price observation nontrivial half depth event a b
  rw [observed]
  have actual := Sparse.schedule_read_insert (source event) (separates observation nontrivial half depth event) a b
  dsimp only at actual
  rw [Sparse.schedule_last] at actual
  exact actual

/-- Only the current prices are supplied by the independent consumer. The next Pa row comes from the source. -/
def nextPrices {start n : Nat} (event : Event start n) (book : Book event)
    (data : Record.Values n × ℂ) : Record.Values n × ℂ :=
  let coeff := recoverAt observation nontrivial half depth event book data
  sampleAt observation nontrivial half depth event book
    (physicalMixture (fun j => (paired event j).2) coeff.1 coeff.2)

theorem next_prices_actual {start n : Nat} (event : Event start n) (a : Record.Values n) (b : ℂ) :
    let book := choose event
    let current := sampleAt observation nontrivial half depth event book
      (physicalMixture (fun j => (paired event j).1) a b)
    nextPrices observation nontrivial half depth event book current =
      sampleAt observation nontrivial half depth event book (physicalMixture (fun j => (paired event j).2) a b) := by
  let book := choose event
  let current := sampleAt observation nontrivial half depth event book
    (physicalMixture (fun j => (paired event j).1) a b)
  have paid : recoverAt observation nontrivial half depth event book current = (a,b) :=
    current_price_inverse observation nontrivial half depth event a b
  dsimp only [nextPrices]
  rw [paid]

def graphFromPrices {start ordinal : Nat} (event : Event start (ordinal+1))
    (book : Book event) (data : Record.Values (ordinal+1) × ℂ) :=
  let coeff := recoverAt observation nontrivial half depth event book data
  rebuildBirth observation nontrivial half depth start ordinal (toRange ordinal coeff.1,coeff.2)

theorem price_graph_writeback {start ordinal : Nat} (previous : State start (ordinal+1))
    (a : Record.Values (ordinal+1)) (b : ℂ) :
    let event := (InverseDrivenRecord.step observation nontrivial half depth previous).1
    let book := choose event
    let data := sampleAt observation nontrivial half depth event book
      (physicalMixture (fun j => (paired event j).1) a b)
    let old := graphFromPrices observation nontrivial half depth event book data
    let next := rebuildBirth observation nontrivial half depth (start+1) ordinal (toRange ordinal a,b)
    (advanceWide c observation.mathlibZero old.1, advanceStock c (modelInventory observation nontrivial half old.2)) =
      (next.1,modelInventory observation nontrivial half next.2) := by
  let event := (InverseDrivenRecord.step observation nontrivial half depth previous).1
  have physical := physical_readback observation nontrivial half depth event a b
  have written := physical_writeback observation nontrivial half depth previous a b
  dsimp only at physical written ⊢
  rw [physical.1, physical.2] at written
  rw [graphFromPrices, current_price_inverse]
  exact written

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.EmittedPaPrices
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
