import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgramBudget

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineBudget
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal PreparationVacuumEngineSmooth
open PreparationVacuumClockSymbol
open scoped BigOperators ContDiff
variable {x : SourcePhase}

structure SourceJetInputs (x : SourcePhase) where
  principal : ∀ j,SymbolEstimate (engineSource 0 j) x
  first : ∀ j,SymbolEstimate (engineSource 1 j) x
  zero : ∀ j,SymbolEstimate (engineSource 2 j) x
  clock : SymbolEstimate sourceClock x
  inverseClock : SymbolEstimate (fun y => (sourceClock y)⁻¹) x
  inverseJacobian : ∀ a b,SymbolEstimate (fun y => (principalForceJacobian y)⁻¹ a b) x

def sourceSlotEstimate (input : SourceJetInputs x) (n : ℕ) (slot : Fin 13) : SymbolEstimate (engineSource n slot) x := by
  cases n with
  | zero => exact input.principal slot
  | succ n =>
    cases n with
    | zero => exact input.first slot
    | succ n =>
      cases n with
      | zero => exact input.zero slot
      | succ n => exact symbolZero x

def traceEstimate (x : SourcePhase) (hx : x∈poleDomain) (input : SourceJetInputs x) (n : ℕ) : SymbolEstimate (engineTrace n) x :=
  symbolAdd (smoothSymbol_add (engineSource_smooth n 4) (engineSource_smooth n 5)) (engineSource_smooth n 6)
    x hx (symbolAdd (engineSource_smooth n 4) (engineSource_smooth n 5) x hx
      (sourceSlotEstimate input n 4) (sourceSlotEstimate input n 5)) (sourceSlotEstimate input n 6)

def sourceSeriesEstimate (input : SourceJetInputs x) (slot : Fin 13) :
    SeriesEstimate ((smooth_program_const% "sourceSeries") slot) x := by
  intro n
  cases n with
  | zero => exact polynomialConstant (input.principal slot)
  | succ n =>
    cases n with
    | zero => exact polynomialConstant (input.first slot)
    | succ n =>
      cases n with
      | zero => exact polynomialConstant (input.zero slot)
      | succ n => exact polynomialZero x

def traceSeriesEstimate (x : SourcePhase) (hx : x∈poleDomain) (input : SourceJetInputs x) :
    SeriesEstimate (smooth_program_const% "traceSeries") x := by
  intro n
  cases n with
  | zero => exact polynomialConstant (traceEstimate x hx input 0)
  | succ n =>
    cases n with
    | zero => exact polynomialConstant (traceEstimate x hx input 1)
    | succ n =>
      cases n with
      | zero => exact polynomialConstant (traceEstimate x hx input 2)
      | succ n => exact polynomialZero x

def sourceAffineEstimate {k : ℕ} (depth : ℕ) {clock : ClockAt k} (sc : SmoothClock clock)
    (x : SourcePhase) (hx : x∈poleDomain) (bc : ClockEstimate clock x) (input : SourceJetInputs x)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) :
    SymbolEstimate ((smooth_program_const% "affine") depth clock equation n) x := by
  cases equation with
  | none =>
    apply symbolSum
    · intro a _
      exact smoothSeries_getD (sourceJ_program_smooth depth sc a (sourceSeries_smooth _)) n.val 0
    · exact hx
    · intro a _
      exact ⟨(sourceJEstimate depth sc x hx bc (sourceSeries_smooth _) (sourceSeriesEstimate input _) a n.val).upper 0,
        (sourceJEstimate depth sc x hx bc (sourceSeries_smooth _) (sourceSeriesEstimate input _) a n.val).bound 0⟩
  | some a =>
    exact symbolNeg (smoothSeries_getD (sourceSeries_smooth (Fin.castAdd 9 a)) n.val 0) x hx
      ⟨(sourceSeriesEstimate input (Fin.castAdd 9 a) n.val).upper 0,
        (sourceSeriesEstimate input (Fin.castAdd 9 a) n.val).bound 0⟩

def sourceEquationEstimate {k : ℕ} (depth : ℕ) {clock : ClockAt k} (sc : SmoothClock clock)
    (x : SourcePhase) (hx : x∈poleDomain) (bc : ClockEstimate clock x) (input : SourceJetInputs x)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) : SymbolEstimate (forceOrEnergy depth clock equation n) x := by
  let trace := (smooth_program_const% "applyT") depth clock 0 0 equation (smooth_program_const% "traceSeries") n
  let diagonal : Fin 3 → RealSymbol := fun i => fun y => (1/2 : ℝ)*
    (smooth_program_const% "applyT") depth clock (Fin.succ i) (Fin.succ i) equation
      ((smooth_program_const% "sourceSeries") ⟨4+i.val,by omega⟩) n y
  let cross : Fin 3 → RealSymbol := fun i =>
    (smooth_program_const% "applyT") depth clock (Fin.succ ((smooth_program_const% "crossFirst") i))
      (Fin.succ ((smooth_program_const% "crossSecond") i)) equation
      ((smooth_program_const% "sourceSeries") ((smooth_program_const% "crossSlot") i)) n
  let shift : Fin 3 → RealSymbol := fun i => (smooth_program_const% "applyT") depth clock 0 (Fin.succ i) equation
    ((smooth_program_const% "sourceSeries") ⟨10+i.val,by omega⟩) n
  have traceSmooth : SmoothSymbol trace := sourceTable_program_smooth depth sc 0 0 equation traceSeries_smooth n
  have diagonalSmooth (i : Fin 3) : SmoothSymbol (diagonal i) := contDiffOn_const.mul
    (sourceTable_program_smooth depth sc (Fin.succ i) (Fin.succ i) equation (sourceSeries_smooth _) n)
  have crossSmooth (i : Fin 3) : SmoothSymbol (cross i) := sourceTable_program_smooth depth sc _ _ equation (sourceSeries_smooth _) n
  have shiftSmooth (i : Fin 3) : SmoothSymbol (shift i) := sourceTable_program_smooth depth sc _ _ equation (sourceSeries_smooth _) n
  let headEstimate := symbolAdd (sourceAffine_program_smooth depth sc equation n) (contDiffOn_const.mul traceSmooth) x hx
    (sourceAffineEstimate depth sc x hx bc input equation n)
    (symbolScale (1/2) traceSmooth x hx
      (sourceTableEstimate depth sc x hx bc input.inverseClock 0 0 equation traceSeries_smooth (traceSeriesEstimate x hx input) n))
  let diagonalEstimate := symbolSum Finset.univ diagonal (fun i _ => diagonalSmooth i) x hx (fun i _ =>
    symbolScale (1/2) (sourceTable_program_smooth depth sc (Fin.succ i) (Fin.succ i) equation (sourceSeries_smooth _) n) x hx
      (sourceTableEstimate depth sc x hx bc input.inverseClock (Fin.succ i) (Fin.succ i) equation
        (sourceSeries_smooth _) (sourceSeriesEstimate input _) n))
  let crossEstimate := symbolSum Finset.univ cross (fun i _ => crossSmooth i) x hx (fun i _ =>
    sourceTableEstimate depth sc x hx bc input.inverseClock _ _ equation (sourceSeries_smooth _) (sourceSeriesEstimate input _) n)
  let shiftEstimate := symbolSum Finset.univ shift (fun i _ => shiftSmooth i) x hx (fun i _ =>
    sourceTableEstimate depth sc x hx bc input.inverseClock _ _ equation (sourceSeries_smooth _) (sourceSeriesEstimate input _) n)
  change SymbolEstimate (((((smooth_program_const% "affine") depth clock equation n+
    (fun y => (1/2 : ℝ)*trace y))-∑ i : Fin 3,diagonal i)-∑ i : Fin 3,cross i)-∑ i : Fin 3,shift i) x
  let firstEstimate := symbolSub (smoothSymbol_add (sourceAffine_program_smooth depth sc equation n) (contDiffOn_const.mul traceSmooth))
    (smoothSymbol_sum _ _ (fun i _ => diagonalSmooth i)) x hx headEstimate diagonalEstimate
  let secondEstimate := symbolSub
    (smoothSymbol_sub (smoothSymbol_add (sourceAffine_program_smooth depth sc equation n) (contDiffOn_const.mul traceSmooth))
      (smoothSymbol_sum _ _ (fun i _ => diagonalSmooth i)))
    (smoothSymbol_sum _ _ (fun i _ => crossSmooth i)) x hx firstEstimate crossEstimate
  exact symbolSub
    (smoothSymbol_sub
      (smoothSymbol_sub (smoothSymbol_add (sourceAffine_program_smooth depth sc equation n) (contDiffOn_const.mul traceSmooth))
        (smoothSymbol_sum _ _ (fun i _ => diagonalSmooth i)))
      (smoothSymbol_sum _ _ (fun i _ => crossSmooth i)))
    (smoothSymbol_sum _ _ (fun i _ => shiftSmooth i)) x hx secondEstimate shiftEstimate


private def clockFromEntries {k : ℕ} (clock : ClockAt k)
    (entries : ∀ a j,SymbolEstimate (clock a j) x) : ClockEstimate clock x := by
  intro a i
  change SymbolEstimate (if h : i<k+1 then clock a ⟨i,h⟩ else 0) x
  split_ifs
  · exact entries _ _
  · exact symbolZero x

def sourceEngineEstimate (x : SourcePhase) (hx : x∈poleDomain) (input : SourceJetInputs x) (k : ℕ) :
    ∀ a j,SymbolEstimate (sourceEngine k a j) x :=
  Nat.rec (motive:=fun k => ∀ a j,SymbolEstimate (sourceEngine k a j) x)
    (by
      intro a j
      have first : j=(0 : Fin 1) := by
        apply Fin.ext
        change j.val=0
        have bound := j.isLt
        change j.val<1 at bound
        omega
      rw [first,sourceEngine_initial]
      split_ifs
      · exact input.clock
      · exact symbolZero x)
    (fun k previous => by
      intro a j
      by_cases old : j.val<k+1
      · have same : j=Fin.castSucc ⟨j.val,old⟩ := Fin.ext rfl
        rw [same,sourceEngine_preserves]
        exact previous _ _
      · have same : j=Fin.last (k+1) := by apply Fin.ext; have := j.isLt; simp only [Fin.val_last]; omega
        rw [same]
        let residual : Fin 4 → RealSymbol := fun b =>
          forceOrEnergy (k+1) (sourceEngine k) (some b) (Fin.last (k+1))
        have residualSmooth (b : Fin 4) : SmoothSymbol (residual b) :=
          forceOrEnergy_program_smooth (k+1) (sourceEngine_smooth k) (some b) (Fin.last (k+1))
        let residualEstimate (b : Fin 4) : SymbolEstimate (residual b) x :=
          sourceEquationEstimate (k+1) (sourceEngine_smooth k) x hx
            (clockFromEntries (sourceEngine k) previous) input (some b) (Fin.last (k+1))
        have productSmooth (b : Fin 4) : SmoothSymbol (fun y => (principalForceJacobian y)⁻¹ a b*residual b y) :=
          (source_engineInverse_smooth a b).mul (residualSmooth b)
        let estimate := symbolNeg (smoothSymbol_sum Finset.univ _ (fun b _ => productSmooth b)) x hx
          (symbolSum Finset.univ _ (fun b _ => productSmooth b) x hx (fun b _ =>
            symbolProduct (source_engineInverse_smooth a b) (residualSmooth b) x hx
              (input.inverseJacobian a b) (residualEstimate b)))
        have generated : sourceEngine (k+1) a (Fin.last (k+1))=
            -(∑ b : Fin 4,(fun y => (principalForceJacobian y)⁻¹ a b)*residual b) := by
          funext y
          exact sourceEngine_generated k a y
        rw [generated]
        exact estimate) k

def actualEnergyEstimate (x : SourcePhase) (hx : x∈poleDomain) (input : SourceJetInputs x) (k : ℕ) :
    SymbolEstimate (sourceEngineEnergy k) x := by
  cases k with
  | zero =>
    exact sourceEquationEstimate 0 (sourceEngine_smooth 0) x hx
      (clockFromEntries (sourceEngine 0) (sourceEngineEstimate x hx input 0)) input none (Fin.last 0)
  | succ k =>
    rw [PreparationVacuumEnginePaidDepth.sourceEngineEnergy_newestExcluded k]
    exact sourceEquationEstimate (k+1) (sourceEngine_smooth k) x hx
      (clockFromEntries (sourceEngine k) (sourceEngineEstimate x hx input k)) input none (Fin.last (k+1))

def actualEnergyMajorant (x : SourcePhase) (hx : x∈poleDomain) (input : SourceJetInputs x) (k m : ℕ) : ℝ :=
  (actualEnergyEstimate x hx input k).upper m

def actualClockMajorant (x : SourcePhase) (hx : x∈poleDomain) (input : SourceJetInputs x)
    (k : ℕ) (a : Fin 4) (j : Fin (k+1)) (m : ℕ) : ℝ := (sourceEngineEstimate x hx input k a j).upper m

theorem actualEnergyMajorant_bound (x : SourcePhase) (hx : x∈poleDomain) (input : SourceJetInputs x)
    (k m : ℕ) (w : Word m) : |jet m (sourceEngineEnergy k) w x|≤actualEnergyMajorant x hx input k m :=
  (actualEnergyEstimate x hx input k).bound m w

theorem actualClockMajorant_bound (x : SourcePhase) (hx : x∈poleDomain) (input : SourceJetInputs x)
    (k : ℕ) (a : Fin 4) (j : Fin (k+1)) (m : ℕ) (w : Word m) :
    |jet m (sourceEngine k a j) w x|≤actualClockMajorant x hx input k a j m :=
  (sourceEngineEstimate x hx input k a j).bound m w

end LowEnergy.PreparationVacuumEngineBudget
