import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.RetainedMatrix

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.InverseDrivenRecord

open BurnolPhysicalState Matrix Finset
open scoped Matrix
open PacketFit RetainedRecord RetainedMatrix
open private PreparedAt PreparedAt.mk PreparedAt.source PreparedAt.cutoff PreparedAt.fuel
  PreparedAt.columns PreparedAt.fit PreparedAt.covers PreparedAt.cutoff_actual PreparedAt.fuel_actual
  PreparedAt.columns_actual PreparedAt.fit_actual RecordAt.mk Progress.mk
  prepare oldStop carryTo carried_covers oldColumnFrom old_column_from_actual firstFrom
  first_time_actual first_packets_actual candidateFrom from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.RetainedRecord
open private observed_column_actual birthColumn oldActorRow birthPrice emptyState MatrixState.mk from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.RetainedMatrix
open private nextCutoff from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord
open private oldFit from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedResidualProbe

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "Source" => RetainedRecord.RecordAt observation nontrivial half depth
local notation "Ready" => PreparedAt observation nontrivial half depth
local notation "Event" => RetainedRecord.Progress observation nontrivial half depth
local notation "StoredMatrix" => RetainedMatrix.MatrixState observation nontrivial half depth
local notation "observe" => RetainedMatrix.observed observation nontrivial half depth
local notation "cut" => sourceCutoff observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth
local notation "original" => paidPivot observation nontrivial half depth
local notation "next" => RetainedRecord.advance observation nontrivial half depth
local notation "newColumn" => birthColumn observation nontrivial half depth
local notation "newRow" => oldActorRow observation nontrivial half depth
local notation "newCorner" => birthPrice observation nontrivial half depth

/-- The stored inverse fits the new actor using only its column at the paid old addresses. -/
private def prepareFromInverse {start n : Nat} (previous : StoredMatrix start n) : Ready start n := by
  let old := previous.source
  let A := observe old
  letI : Invertible A := previous.inverse
  let before := carryTo observation nontrivial half depth old.source (oldStop observation nontrivial half depth old)
  have covered := carried_covers observation nontrivial half depth old.source (oldStop observation nontrivial half depth old)
  let birth := oldColumnFrom observation nontrivial half depth old before covered (Fin.last n)
  let columns : Fin (n+1) → Record.Values n := Fin.lastCases birth (Block.columns A)
  let rhs : Fin n → ℂ := fun j => birth j
  let fit := WithLp.toLp 2 (previous.inverse.invOf *ᵥ rhs)
  have oldColumns : Block.columns A =
      fun j => paidPriceRecord observation nontrivial half depth start n (start+j.val) :=
    funext (observed_column_actual observation nontrivial half depth old)
  have birthActual : birth = paidPriceRecord observation nontrivial half depth start n (start+n) :=
    old_column_from_actual observation nontrivial half depth old before covered (Fin.last n)
  have columnsActual (actor : Fin (n+1)) :
      columns actor = paidPriceRecord observation nontrivial half depth start n (start+actor.val) := by
    refine Fin.lastCases ?_ (fun j => ?_) actor
    · simpa only [columns,Fin.lastCases_last,Fin.val_last] using birthActual
    · simpa only [columns,Fin.lastCases_castSucc,Fin.val_castSucc] using congrFun oldColumns j
  have rhsActual : WithLp.toLp 2 rhs = birth := by ext i; rfl
  have fitActual : fit = paidOldFit observation nontrivial half depth start n := by
    have equation := Block.coefficients_from_inverse A rhs
    refine equation.symm.trans ?_
    unfold paidOldFit
    rw [oldColumns,rhsActual,birthActual]
  let cutoff := nextCutoff old.times
  have cutoffActual : cutoff = cut start n := by
    simp only [cutoff,sourceCutoff,old.times_actual]
  let fuel := probeFuel observation half (probeBase observation start cutoff) n
    (Fin.snoc (fun j => -fit j) 1) (‖xiOpening observation half‖/4)
  have fuelActual : fuel = residualFuel observation nontrivial half depth start n (cut start n) := by
    simp only [fuel,cutoffActual,fitActual,residualFuel,fittedCoefficients,oldFit,actual_paid_old_fit]
  let bound := n+cutoff+fuel
  let complete := carryTo observation nontrivial half depth before bound
  exact PreparedAt.mk complete cutoff fuel columns fit
    (carried_covers observation nontrivial half depth before bound)
    cutoffActual fuelActual columnsActual fitActual

private theorem ready_ext {start n : Nat} (left right : Ready start n)
    (sourceEq : PreparedAt.source left = PreparedAt.source right)
    (cutoffEq : PreparedAt.cutoff left = PreparedAt.cutoff right)
    (fuelEq : PreparedAt.fuel left = PreparedAt.fuel right)
    (columnsEq : PreparedAt.columns left = PreparedAt.columns right)
    (fitEq : PreparedAt.fit left = PreparedAt.fit right) : left = right := by
  rcases left with ⟨ls,lc,lf,lv,lu,lh,lhc,lhf,lhv,lhu⟩
  rcases right with ⟨rs,rc,rf,rv,ru,rh,rhc,rhf,rhv,rhu⟩
  change ls = rs at sourceEq
  change lc = rc at cutoffEq
  change lf = rf at fuelEq
  change lv = rv at columnsEq
  change lu = ru at fitEq
  cases sourceEq
  cases cutoffEq
  cases fuelEq
  cases columnsEq
  cases fitEq
  rfl

private theorem prepare_from_inverse_actual {start n : Nat} (previous : StoredMatrix start n) :
    prepareFromInverse observation nontrivial half depth previous =
      prepare observation nontrivial half depth previous.source := by
  let actual := prepareFromInverse observation nontrivial half depth previous
  let known := prepare observation nontrivial half depth previous.source
  let before := carryTo observation nontrivial half depth previous.source.source
    (oldStop observation nontrivial half depth previous.source)
  have sameCut : PreparedAt.cutoff actual = PreparedAt.cutoff known :=
    (PreparedAt.cutoff_actual actual).trans (PreparedAt.cutoff_actual known).symm
  have sameFuel : PreparedAt.fuel actual = PreparedAt.fuel known :=
    (PreparedAt.fuel_actual actual).trans (PreparedAt.fuel_actual known).symm
  have actualSource : PreparedAt.source actual =
      carryTo observation nontrivial half depth before (n+PreparedAt.cutoff actual+PreparedAt.fuel actual) := rfl
  have knownSource : PreparedAt.source known =
      carryTo observation nontrivial half depth before (n+PreparedAt.cutoff known+PreparedAt.fuel known) := rfl
  have sameStop := congrArg₂ (fun cutoff fuel : Nat => n+cutoff+fuel) sameCut sameFuel
  have sameSource := actualSource.trans
    ((congrArg (carryTo observation nontrivial half depth before) sameStop).trans knownSource.symm)
  have columns := funext (fun actor =>
    (PreparedAt.columns_actual actual actor).trans (PreparedAt.columns_actual known actor).symm)
  have fit := (PreparedAt.fit_actual actual).trans (PreparedAt.fit_actual known).symm
  exact ready_ext observation nontrivial half depth actual known sameSource sameCut sameFuel columns fit

private def assemble {start n : Nat} (previous : Source start n) (ready : Ready start n) : Event start n := by
  let picked := firstFrom observation nontrivial half depth ready
  let latest := PreparedAt.cutoff ready+picked.val
  let times := Fin.snoc (α := fun _ : Fin (n+1) => Nat) previous.times latest
  have timesActual : times = (schedule start (n+1)).val := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [times,Fin.snoc_last]
      exact first_time_actual observation nontrivial half depth ready
    · simp only [times,Fin.snoc_castSucc,previous.times_actual,priceSchedule,Record.schedule_prior]
  have paid (actor row : Fin (n+1)) : actor.val+times row ≤ (PreparedAt.source ready).last := by
    have actorWithin := Nat.le_of_lt_succ actor.isLt
    have covered := PreparedAt.covers ready
    have offsetWithin := Nat.le_of_lt_succ picked.isLt
    refine Fin.lastCases ?_ (fun j => ?_) row
    · simp only [times,Fin.snoc_last,latest]
      omega
    · simp only [times,Fin.snoc_castSucc]
      have earlier : previous.times j ≤ PreparedAt.cutoff ready := by
        rw [PreparedAt.cutoff_actual,sourceCutoff,← previous.times_actual]
        exact Nat.le_succ_of_le (Finset.le_sup (f := previous.times) (Finset.mem_univ j))
      omega
  let successor : Source start (n+1) :=
    RecordAt.mk (PreparedAt.source ready) times timesActual paid
  exact Progress.mk successor (PreparedAt.columns ready)
    (fun actor => candidateFrom observation nontrivial half depth ready actor picked)
    (PreparedAt.columns_actual ready) (first_packets_actual observation nontrivial half depth ready)

private theorem assemble_original {start n : Nat} (previous : Source start n) :
    assemble observation nontrivial half depth previous (prepare observation nontrivial half depth previous) =
      next previous :=
  rfl

/-- The inverse of the previous actual record generates the next selection on the same source. -/
def emitFromInverse {start n : Nat} (previous : StoredMatrix start n) : Event start n :=
  assemble observation nontrivial half depth previous.source
    (prepareFromInverse observation nontrivial half depth previous)

theorem emitted_same_source {start n : Nat} (previous : StoredMatrix start n) :
    emitFromInverse observation nontrivial half depth previous = next previous.source :=
  (congrArg (assemble observation nontrivial half depth previous.source)
    (prepare_from_inverse_actual observation nontrivial half depth previous)).trans
    (assemble_original observation nontrivial half depth previous.source)

/-- Generate the next source record and update its inverse using the same emitted row. -/
def step {start n : Nat} (previous : StoredMatrix start n) : Event start n × StoredMatrix start (n+1) := by
  let event := emitFromInverse observation nontrivial half depth previous
  let A := observe previous.source
  letI : Invertible A := previous.inverse
  let residual := Block.pivot A (newColumn event) (newRow event) (newCorner event)
  have same : event = next previous.source :=
    emitted_same_source observation nontrivial half depth previous
  have paid : residual = paidCandidateResidual observation nontrivial half depth start n (original start n) :=
    (congrArg (fun actual : Event start n => Block.pivot A (newColumn actual) (newRow actual) (newCorner actual)) same).trans
      (generated_pivot observation nontrivial half depth previous.source)
  have live : residual ≠ 0 := fun zero =>
    actual_paid_pivot_live observation nontrivial half depth start n (paid.symm.trans zero)
  let assembled := Block.border A (newColumn event) (newRow event) (newCorner event)
  have installed : observe event.record = assembled :=
    (congrArg (fun e : Event start n => observe e.record) same).trans
      ((observed_next observation nontrivial half depth previous.source).trans
        (congrArg (fun e : Event start n => Block.border A (newColumn e) (newRow e) (newCorner e)) same.symm))
  let inverse := Block.borderInverse A (newColumn event) (newRow event) (newCorner event)
    (isUnit_iff_ne_zero.mpr live)
  have determinant : previous.determinant*residual = (observe event.record).det := calc
    _ = A.det*residual := congrArg (fun value => value*residual) previous.determinant_actual
    _ = assembled.det := (Block.border_det A (newColumn event) (newRow event) (newCorner event)).symm
    _ = (observe event.record).det := congrArg Matrix.det installed.symm
  let continued : StoredMatrix start (n+1) :=
    MatrixState.mk event.record
      (Eq.mp (congrArg (fun m : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => Invertible m) installed.symm) inverse)
      (previous.determinant*residual) determinant
  exact (event,continued)

private theorem same_matrix_state {start n : Nat} (left right : StoredMatrix start n)
    (actual : left.source = right.source) : left = right := by
  rcases left with ⟨ls,li,ld,lp⟩
  rcases right with ⟨rs,ri,rd,rp⟩
  change ls = rs at actual
  cases actual
  have inverse : li = ri := Subsingleton.elim _ _
  have determinant : ld = rd := lp.trans rp.symm
  cases inverse
  cases determinant
  rfl

theorem step_state_actual {start n : Nat} (previous : StoredMatrix start n) :
    (step observation nontrivial half depth previous).2 =
      extendMatrix observation nontrivial half depth previous := by
  apply same_matrix_state
  have actual : (step observation nontrivial half depth previous).2.source =
      (emitFromInverse observation nontrivial half depth previous).record := rfl
  exact actual.trans
    ((congrArg Progress.record (emitted_same_source observation nontrivial half depth previous)).trans
      (extend_matrix_source observation nontrivial half depth previous).symm)

/-- All ranks consume the inverse produced by their preceding actual record. -/
def runUsingInverse (start : Nat) : (n : Nat) → StoredMatrix start n :=
  Nat.rec (motive := StoredMatrix start) (emptyState observation nontrivial half depth start)
    (fun _ previous => (step observation nontrivial half depth previous).2)

theorem run_using_inverse_actual (start n : Nat) :
    runUsingInverse observation nontrivial half depth start n =
      runMatrix observation nontrivial half depth start n := by
  induction n with
  | zero => rfl
  | succ n previous =>
    exact (step_state_actual observation nontrivial half depth
      (runUsingInverse observation nontrivial half depth start n)).trans
        (congrArg (extendMatrix observation nontrivial half depth (start := start) (n := n)) previous)

/-- The same step's inverse consumes the actual price records emitted by its selection. -/
theorem step_inverse_reads {start n : Nat} (previous : StoredMatrix start n)
    (a : Record.Values n) (b : ℂ) :
    let actual := step observation nontrivial half depth previous
    let paid := sourceRecords observation nontrivial half depth actual.1 a b
    actual.2.inverse.invOf *ᵥ Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => paid.1 j) paid.2 =
      Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => a j) b := by
  let read (pair : Event start n × StoredMatrix start (n+1)) : Fin (n+1) → ℂ :=
    let paid := sourceRecords observation nontrivial half depth pair.1 a b
    pair.2.inverse.invOf *ᵥ Fin.snoc (α := fun _ : Fin (n+1) => ℂ) (fun j => paid.1 j) paid.2
  have event : (step observation nontrivial half depth previous).1 = next previous.source :=
    emitted_same_source observation nontrivial half depth previous
  have same : step observation nontrivial half depth previous =
      (next previous.source,extendMatrix observation nontrivial half depth previous) :=
    Prod.ext event (step_state_actual observation nontrivial half depth previous)
  exact (congrArg read same).trans (inverse_reads_emitted observation nontrivial half depth previous a b)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.InverseDrivenRecord
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
