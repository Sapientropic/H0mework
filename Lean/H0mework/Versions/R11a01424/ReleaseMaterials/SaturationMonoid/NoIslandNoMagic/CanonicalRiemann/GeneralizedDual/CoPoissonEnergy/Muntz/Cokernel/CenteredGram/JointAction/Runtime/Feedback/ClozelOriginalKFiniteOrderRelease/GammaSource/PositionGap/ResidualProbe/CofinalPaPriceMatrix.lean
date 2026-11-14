import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CofinalPaCommonProbe
import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.MatrixBorder

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.CofinalPaPriceMatrix

open BurnolPhysicalState
open scoped Matrix BigOperators InnerProductSpace
open EmittedPaInnovation
open private projectedFit residual_live from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CofinalPaCommonProbe
open private toRange from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private rebuildBirth from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback

namespace Block
export SourceGeneratedFiniteGram.MatrixBorder
  (border border_old_old border_old_new border_new_old border_new_new pivot borderInverse coefficients_from_inverse)
end Block
namespace Fit
export SourceGeneratedFiniteGram.Projection (synthesis)
end Fit

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "pa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth
local notation "price" => PhysicalPriceCountable.price

variable {n : Nat}

abbrev Slots (n : Nat) := Fin n ↪ Nat

/-- Only distinct literal ordinals of the original Division action are used as columns. -/
def matrix (tests : Fin n → ℝ) (slots : Slots n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i j => price (tests i) (pa (slots j)))

local notation "M" => matrix observation nontrivial half depth

abbrev Book (n : Nat) :=
  Σ tests : Fin n → ℝ, (slots : Slots n) → Invertible (M tests slots)

local notation "BookAt" => Book observation nontrivial half depth

private def prior (slots : Slots (n+1)) : Slots n :=
  (⟨Fin.castSucc,Fin.castSucc_injective n⟩ : Fin n ↪ Fin (n+1)).trans slots

private def right (tests : Fin n → ℝ) (slots : Slots (n+1)) : Fin n → ℂ :=
  fun i => price (tests i) (pa (slots (Fin.last n)))

private def bottom (height : ℝ) (slots : Slots (n+1)) : Fin n → ℂ :=
  fun j => price height (pa (slots j.castSucc))

private def corner (height : ℝ) (slots : Slots (n+1)) : ℂ :=
  price height (pa (slots (Fin.last n)))

local notation "col" => right observation nontrivial half depth
local notation "row" => bottom observation nontrivial half depth
local notation "cell" => corner observation nontrivial half depth

private theorem matrix_border (tests : Fin n → ℝ) (slots : Slots (n+1)) (height : ℝ) :
    M (Fin.snoc (α := fun _ : Fin (n+1) => ℝ) tests height) slots =
      Block.border (M tests (prior slots)) (col tests slots) (row height slots) (cell height slots) := by
  apply Matrix.ext
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [matrix, Matrix.of_apply, Fin.snoc_last, Block.border_new_new, corner]
    · simp only [matrix, Matrix.of_apply, Fin.snoc_last, Block.border_new_old, bottom]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [matrix, Matrix.of_apply, Fin.snoc_castSucc, Block.border_old_new, right]
    · simp only [matrix, Matrix.of_apply, Fin.snoc_castSucc, Block.border_old_old, prior,
        Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]

/-- The inverse of these retained columns acts on their actual new column. -/
private def residualFrom (old : BookAt n) (slots : Slots (n+1)) : BurnolPaAmbientCarrier :=
  pa (slots (Fin.last n)) - Fit.synthesis (fun j : Fin n => pa (slots j.castSucc))
    (WithLp.toLp 2 ((old.2 (prior slots)).invOf *ᵥ col old.1 slots))

local notation "residual" => residualFrom observation nontrivial half depth

private theorem residual_from_paid (old : BookAt n) (slots : Slots (n+1)) :
    residual old slots = CofinalPaCommonProbe.fieldResidual (pa ∘ slots) old.1 := by
  let inverse : Invertible (M old.1 (prior slots)) := old.2 (prior slots)
  have fit : WithLp.toLp 2 ((old.2 (prior slots)).invOf *ᵥ col old.1 slots) =
      projectedFit (pa ∘ slots) old.1 :=
    (Block.coefficients_from_inverse (M old.1 (prior slots)) (col old.1 slots)).symm
  exact congrArg (fun a : Record.Values n =>
    pa (slots (Fin.last n)) - Fit.synthesis (fun j : Fin n => pa (slots j.castSucc)) a) fit

private theorem paid_pivot (old : BookAt n) (slots : Slots (n+1)) (height : ℝ) :
    @Block.pivot ℂ n _ (M old.1 (prior slots)) (old.2 (prior slots)) (col old.1 slots)
        (row height slots) (cell height slots) = price height (residual old slots) := by
  change (cell height slots - dotProduct (row height slots)
      ((old.2 (prior slots)).invOf *ᵥ col old.1 slots)) =
    price height (pa (slots (Fin.last n)) -
      ∑ j : Fin n, ((old.2 (prior slots)).invOf *ᵥ col old.1 slots) j • pa (slots j.castSucc))
  simp only [corner, bottom, dotProduct, map_sub, map_sum, map_smul, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

@[instance_reducible]
private def appendInverse (old : BookAt n) (slots : Slots (n+1)) (height : ℝ)
    (live : price height (residual old slots) ≠ 0) :
    Invertible (M (Fin.snoc (α := fun _ : Fin (n+1) => ℝ) old.1 height) slots) := by
  letI : Invertible (M old.1 (prior slots)) := old.2 (prior slots)
  have paid : IsUnit (Block.pivot (M old.1 (prior slots)) (col old.1 slots)
      (row height slots) (cell height slots)) :=
    isUnit_iff_ne_zero.mpr (fun zero =>
      live ((paid_pivot observation nontrivial half depth old slots height).symm.trans zero))
  rw [matrix_border]
  exact Block.borderInverse _ _ _ _ paid

private def cutoff (tests : Fin n → ℝ) : ℝ := ∑ i, |tests i|

private theorem height_exists (old : BookAt n) :
    ∃ height : ℝ, cutoff old.1 < height ∧ ∀ slots, price height (residual old slots) ≠ 0 := by
  let countable : Countable (Slots (n+1)) :=
    (show Function.Injective (fun slots : Slots (n+1) => (slots : Fin (n+1) → Nat)) from
      fun _ _ same => Function.Embedding.ext (fun i => congrFun same i)).countable
  apply PhysicalPriceCountable.exists_after (residual old) _ (cutoff old.1)
  intro slots silent
  have rank := (LocalPaSmear.actual_division_Pa_linearIndependent observation nontrivial half depth).comp
    (slots : Fin (n+1) → Nat) slots.injective
  exact residual_live rank old.1
    ((residual_from_paid observation nontrivial half depth old slots).symm.trans silent)

/-- The same new K address updates every finite tuple, preserving all retained addresses. -/
def append (old : BookAt n) : BookAt (n+1) :=
  let supply := height_exists observation nontrivial half depth old
  let height := Classical.choose supply
  ⟨Fin.snoc (α := fun _ : Fin (n+1) => ℝ) old.1 height,
    fun slots => appendInverse observation nontrivial half depth old slots height
      ((Classical.choose_spec supply).2 slots)⟩

local notation "appendAt" => append observation nontrivial half depth

theorem append_retains (old : BookAt n) (i : Fin n) :
    (appendAt old).1 i.castSucc = old.1 i := by
  simp only [append, Fin.snoc_castSucc]

theorem append_increases (old : BookAt n) (i : Fin n) :
    old.1 i < (appendAt old).1 (Fin.last n) := by
  have within : |old.1 i| ≤ cutoff old.1 :=
    Finset.single_le_sum (fun j _ => abs_nonneg (old.1 j)) (Finset.mem_univ i)
  have after := (Classical.choose_spec (height_exists observation nontrivial half depth old)).1
  simp only [append, Fin.snoc_last]
  exact ((le_abs_self _).trans within).trans_lt after

@[instance_reducible]
private def emptyInverse (slots : Slots 0) : Invertible (M Fin.elim0 slots) :=
  ⟨1,by apply Matrix.ext; intro i _; exact Fin.elim0 i,
    by apply Matrix.ext; intro i _; exact Fin.elim0 i⟩

/-- At each finite rank the same retained schedule separates every set of actual Division columns. -/
def run (rank : Nat) : BookAt rank :=
  Nat.rec (motive := BookAt)
    ⟨Fin.elim0,emptyInverse observation nontrivial half depth⟩ (fun _ old => appendAt old) rank

theorem run_prefix {small large : Nat} (within : small ≤ large) (i : Fin small) :
    (run observation nontrivial half depth large).1 (i.castLE within) =
      (run observation nontrivial half depth small).1 i := by
  induction large, within using Nat.le_induction with
  | base => rfl
  | succ large within same =>
    let previous := run observation nontrivial half depth large
    change (appendAt previous).1 (i.castLE within).castSucc = _
    exact (append_retains observation nontrivial half depth previous _).trans same

def decode (book : BookAt n) (slots : Slots n) (data : Fin n → ℂ) : Fin n → ℂ :=
  (book.2 slots).invOf *ᵥ data

local notation "readBack" => decode observation nontrivial half depth

theorem decode_encoded (book : BookAt n) (slots : Slots n) (coeff : Fin n → ℂ) :
    readBack book slots (M book.1 slots *ᵥ coeff) = coeff := by
  let inverse : Invertible (M book.1 slots) := book.2 slots
  change (⅟(M book.1 slots)) *ᵥ (M book.1 slots *ᵥ coeff) = coeff
  rw [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec]

/-- Native cofinal windows use the actual receipt ordinal and its consecutive columns. -/
def window (ordinal rank : Nat) : Slots rank :=
  ⟨fun i => ordinal+i.val,fun _ _ same => Fin.ext (Nat.add_left_cancel same)⟩

def transport (book : BookAt n) (origin target : Nat) (data : Fin n → ℂ) : Fin n → ℂ :=
  M book.1 (window target n) *ᵥ readBack book (window origin n) data

local notation "move" => transport observation nontrivial half depth

theorem transport_self (book : BookAt n) (ordinal : Nat) (data : Fin n → ℂ) :
    move book ordinal ordinal data = data := by
  let slots := window ordinal n
  let inverse : Invertible (M book.1 slots) := book.2 slots
  change M book.1 slots *ᵥ ((⅟(M book.1 slots)) *ᵥ data) = data
  rw [Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]

theorem transport_comp (book : BookAt n) (origin middle target : Nat) (data : Fin n → ℂ) :
    move book middle target (move book origin middle data) = move book origin target data := by
  change M book.1 (window target n) *ᵥ (readBack book (window middle n)
    (M book.1 (window middle n) *ᵥ readBack book (window origin n) data)) = _
  rw [decode_encoded]
  rfl

local notation "Event" => RetainedRecord.Progress observation nontrivial half depth
local notation "paired" => physicalPair observation nontrivial half depth
local notation "bookAt" => run observation nontrivial half depth

/-- The native clock of the selected actual receipts gives the first physical column address. -/
def emittedOrdinal (start rank : Nat) : Nat :=
  start + candidateTime observation nontrivial half depth start rank
    (paidPivot observation nontrivial half depth start rank)

local notation "ordAt" => emittedOrdinal observation nontrivial half depth

def emittedPrices {start : Nat} (event : Event start n) (coeff : Fin (n+1) → ℂ) :
    (Fin (n+1) → ℂ) × (Fin (n+1) → ℂ) :=
  let book := bookAt (n+1)
  (fun i => price (book.1 i) (∑ j, coeff j • (paired event j).1),
   fun i => price (book.1 i) (∑ j, coeff j • (paired event j).2))

local notation "prices" => emittedPrices observation nontrivial half depth

private theorem read_synthesis (tests : Fin n → ℝ) (slots : Slots n) (coeff : Fin n → ℂ) :
    (fun i => price (tests i) (∑ j, coeff j • pa (slots j))) = M tests slots *ᵥ coeff := by
  funext i
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec_apply_eq_sum, matrix, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

private theorem emitted_rows {start : Nat} (event : Event start n) (coeff : Fin (n+1) → ℂ) :
    let tests := (bookAt (n+1)).1
    let ordinal := ordAt start n
    prices event coeff = (M tests (window ordinal (n+1)) *ᵥ coeff,M tests (window (ordinal+1) (n+1)) *ᵥ coeff) := by
  let time := candidateTime observation nontrivial half depth start n
    (paidPivot observation nontrivial half depth start n)
  let ordinal := start+time
  let tests := (bookAt (n+1)).1
  have before (j : Fin (n+1)) : (paired event j).1 = pa (ordinal+j.val) := by
    have read : (paired event j).1 = pa (start+j.val+time) :=
      congrArg Prod.fst (physical_pair_actual observation nontrivial half depth event j)
    have address : start+j.val+time = ordinal+j.val := by dsimp only [ordinal]; omega
    exact read.trans (congrArg pa address)
  have after (j : Fin (n+1)) : (paired event j).2 = pa (ordinal+1+j.val) := by
    have read : (paired event j).2 = pa (start+j.val+time+1) :=
      congrArg Prod.snd (physical_pair_actual observation nontrivial half depth event j)
    have address : start+j.val+time+1 = ordinal+1+j.val := by dsimp only [ordinal]; omega
    exact read.trans (congrArg pa address)
  apply Prod.ext
  · change (fun i => price (tests i) (∑ j, coeff j • (paired event j).1)) = M tests (window ordinal (n+1)) *ᵥ coeff
    simp only [before]
    exact read_synthesis observation nontrivial half depth tests (window ordinal (n+1)) coeff
  · change (fun i => price (tests i) (∑ j, coeff j • (paired event j).2)) = M tests (window (ordinal+1) (n+1)) *ᵥ coeff
    simp only [after]
    exact read_synthesis observation nontrivial half depth tests (window (ordinal+1) (n+1)) coeff

/-- Each actual leg independently recovers the original weights at the same retained addresses. -/
theorem actual_transport {start : Nat} (event : Event start n) (coeff : Fin (n+1) → ℂ) :
    let book := bookAt (n+1)
    let ordinal := ordAt start n
    let measured := prices event coeff
    readBack book (window ordinal (n+1)) measured.1 = coeff ∧
      readBack book (window (ordinal+1) (n+1)) measured.2 = coeff ∧
      move book ordinal (ordinal+1) measured.1 = measured.2 ∧
      move book (ordinal+1) ordinal measured.2 = measured.1 := by
  let book := bookAt (n+1)
  let ordinal := ordAt start n
  let measured := prices event coeff
  have rows : measured = (M book.1 (window ordinal (n+1)) *ᵥ coeff,M book.1 (window (ordinal+1) (n+1)) *ᵥ coeff) :=
    emitted_rows observation nontrivial half depth event coeff
  have before : readBack book (window ordinal (n+1)) measured.1 = coeff := by rw [rows]; exact decode_encoded _ _ _ _ _ _ _
  have after : readBack book (window (ordinal+1) (n+1)) measured.2 = coeff := by rw [rows]; exact decode_encoded _ _ _ _ _ _ _
  refine ⟨before,after,?_,?_⟩
  · change M book.1 (window (ordinal+1) (n+1)) *ᵥ readBack book (window ordinal (n+1)) measured.1 = measured.2
    exact (congrArg (fun x => M book.1 (window (ordinal+1) (n+1)) *ᵥ x) before).trans (congrArg Prod.snd rows).symm
  · change M book.1 (window ordinal (n+1)) *ᵥ readBack book (window (ordinal+1) (n+1)) measured.2 = measured.1
    exact (congrArg (fun x => M book.1 (window ordinal (n+1)) *ᵥ x) after).trans (congrArg Prod.fst rows).symm

open HilbertInventory (modelInventory advanceStock)
open HilbertInventory.SecondConductorStock.SingleSlot

local notation "State" => RetainedMatrix.MatrixState observation nontrivial half depth
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down

/-- The common cofinal schedule reads the original event back into its stock and relation write. -/
theorem actual_writeback {start ordinal : Nat} (previous : State start (ordinal+1))
    (a : Record.Values (ordinal+1)) (b : ℂ) :
    let event := (InverseDrivenRecord.step observation nontrivial half depth previous).1
    let book := bookAt (ordinal+2)
    let address := ordAt start (ordinal+1)
    let coeff := Fin.snoc (α := fun _ : Fin (ordinal+2) => ℂ) (fun i => a i) b
    let measured := prices event coeff
    let left := readBack book (window address (ordinal+2)) measured.1
    let right := readBack book (window (address+1) (ordinal+2)) measured.2
    let current := rebuildBirth observation nontrivial half depth start ordinal
      (toRange ordinal (WithLp.toLp 2 (fun i => left i.castSucc)), left (Fin.last (ordinal+1)))
    let next := rebuildBirth observation nontrivial half depth (start+1) ordinal
      (toRange ordinal (WithLp.toLp 2 (fun i => right i.castSucc)), right (Fin.last (ordinal+1)))
    (advanceWide c observation.mathlibZero current.1, advanceStock c (modelInventory observation nontrivial half current.2)) =
      (next.1,modelInventory observation nontrivial half next.2) := by
  let event := (InverseDrivenRecord.step observation nontrivial half depth previous).1
  let coeff := Fin.snoc (α := fun _ : Fin (ordinal+2) => ℂ) (fun i => a i) b
  have recovered := actual_transport observation nontrivial half depth event coeff
  have old : WithLp.toLp 2 (fun i : Fin (ordinal+1) => coeff i.castSucc) = a := by
    ext i
    change coeff i.castSucc = a i
    exact Fin.snoc_castSucc _ _ _
  have born : coeff (Fin.last (ordinal+1)) = b := Fin.snoc_last _ _
  have native := actual_born_price_writeback observation nontrivial half depth start ordinal (toRange ordinal a) b
  have written := native.2
  rw [native.1] at written
  dsimp only
  rw [recovered.1, recovered.2.1, old, born]
  exact written

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.CofinalPaPriceMatrix
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
