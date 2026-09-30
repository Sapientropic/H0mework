import H0mework.Versions.X.NavierStokes.StressDynamics.RawAction

set_option autoImplicit false
open scoped ContDiff BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeSourcePolynomialAction

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open NativeCompleteStressBilinear NativeRawStressAction NativeRecoveryTimeGramAction

noncomputable section

inductive Kind | state | stress | scalar | row

abbrev Value : Kind → Type
  | .state => ComplexVorticityHilbertState
  | .stress => NativeCompleteStressCarrier.Space
  | .scalar => ℂ
  | .row => ComplexCoordinateVector

instance (s : Kind) : NormedAddCommGroup (Value s) := by cases s <;> exact inferInstance
instance (s : Kind) : NormedSpace ℝ (Value s) := by cases s <;> exact inferInstance

inductive Expr : Kind → Type
  | input : Expr .state
  | zero {s} : Expr s
  | add {s} : Expr s → Expr s → Expr s
  | linear {a b} : (Value a →L[ℝ] Value b) → Expr a → Expr b
  | bilinear {a b c} : (Value a →L[ℝ] Value b →L[ℝ] Value c) → Expr a → Expr b → Expr c

def eval {s : Kind} (e : Expr s) (value : ComplexVorticityHilbertState) : Value s :=
  match e with
  | .input => value
  | .zero => 0
  | .add a b => eval a value + eval b value
  | .linear L a => L (eval a value)
  | .bilinear B a b => B (eval a value) (eval b value)

def act (generator : Expr .state) {s : Kind} : Expr s → Expr s
  | .input => generator
  | .zero => .zero
  | .add a b => .add (act generator a) (act generator b)
  | .linear L a => .linear L (act generator a)
  | .bilinear B a b => .add (.bilinear B (act generator a) b) (.bilinear B a (act generator b))

def degree {s : Kind} : Expr s → ℕ
  | .input => 1
  | .zero => 0
  | .add a b => max (degree a) (degree b)
  | .linear _ a => degree a
  | .bilinear _ a b => degree a + degree b

theorem eval_act_hasDerivAt {s : Kind} (generator : Expr .state) (e : Expr s)
    {path : ℝ → ComplexVorticityHilbertState} {time : ℝ}
    (actual : HasDerivAt path (eval generator (path time)) time) :
    HasDerivAt (fun t => eval e (path t)) (eval (act generator e) (path time)) time := by
  induction e with
  | input => exact actual
  | zero => exact hasDerivAt_const _ _
  | add a b ha hb => exact ha.add hb
  | linear L a ha => exact L.hasFDerivAt.comp_hasDerivAt time ha
  | bilinear B a b ha hb => exact (B.hasFDerivAt.comp_hasDerivAt time ha).clm_apply hb

theorem degree_act {s : Kind} (generator : Expr .state) (quadratic : degree generator ≤ 2)
    (e : Expr s) : degree (act generator e) ≤ degree e + 1 := by
  induction e with
  | input => exact quadratic
  | zero => simp [act, degree]
  | add a b ha hb =>
      simp only [act, degree]
      omega
  | linear L a ha => exact ha
  | bilinear B a b ha hb =>
      simp only [act, degree]
      omega

def sum {s : Kind} : List (Expr s) → Expr s
  | [] => .zero
  | e :: es => .add e (sum es)

theorem eval_sum {s : Kind} (es : List (Expr s)) (value : ComplexVorticityHilbertState) :
    eval (sum es) value = (es.map (fun e => eval e value)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sum, eval, ih]

def finiteSum {s : Kind} {I : Type} (indices : Finset I) (terms : I → Expr s) : Expr s :=
  sum (indices.toList.map terms)

theorem eval_finiteSum {s : Kind} {I : Type} (indices : Finset I) (terms : I → Expr s)
    (value : ComplexVorticityHilbertState) :
    eval (finiteSum indices terms) value = ∑ i ∈ indices, eval (terms i) value := by
  simp [finiteSum, eval_sum, List.map_map, Function.comp_def]

def dotCLM (wave : IntegerWavevector) : ComplexCoordinateVector →L[ℝ] ℂ :=
  ∑ i : Coordinate, (complexWavevector wave i) • ContinuousLinearMap.proj i

theorem dotCLM_apply (wave : IntegerWavevector) (row : ComplexCoordinateVector) :
    dotCLM wave row = complexWavevector wave ⬝ᵥ row := by
  simp [dotCLM, dotProduct, smul_eq_mul]

def row (wave : IntegerWavevector) : Expr .row :=
  .linear (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave) .input

def velocityRow (wave : IntegerWavevector) : Expr .row :=
  .linear (biotSavartVelocityCLM wave) (row wave)

def pair (first second : IntegerWavevector) : Expr .row :=
  let contraction : Expr .row → Expr .scalar :=
    Expr.linear ((Complex.I * (2 * Real.pi : ℂ)) • dotCLM second)
  .add (.bilinear (ContinuousLinearMap.lsmul ℝ ℂ) (contraction (row first)) (velocityRow second))
    (.linear (-ContinuousLinearMap.id ℝ ComplexCoordinateVector)
      (.bilinear (ContinuousLinearMap.lsmul ℝ ℂ) (contraction (velocityRow first)) (row second)))

def generator (modes : Finset IntegerWavevector) (viscosity : ℝ) : Expr .state :=
  finiteSum modes fun output =>
    .linear (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 output)
      (.add (finiteSum modes fun first => finiteSum modes fun second =>
        if first + second = output then pair first second else .zero)
        (.linear (-(viscosity * integerWaveViscousMultiplier output) •
          ContinuousLinearMap.id ℝ ComplexCoordinateVector) (row output)))

theorem eval_generator (modes : Finset IntegerWavevector) (viscosity : ℝ)
    (value : ComplexVorticityHilbertState) :
    eval (generator modes viscosity) value = finiteStateVorticityGenerator modes viscosity value := by
  simp only [generator, eval_finiteSum, eval]
  unfold finiteStateVorticityGenerator finiteStateVorticityNonlinearCoefficientAt
  congr 1
  funext output
  congr 1
  simp only [row, velocityRow, pair, eval,
    smul_apply, ContinuousLinearMap.id_apply, neg_smul, sub_eq_add_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  split_ifs <;> simp [eval, finiteStateVorticityNonlinearPairContribution,
    finiteStateVelocityCoefficient, dotCLM_apply, sub_eq_add_neg]
  rfl

theorem degree_finiteSum {s : Kind} {I : Type} (indices : Finset I) (terms : I → Expr s)
    (bound : ℕ) (bounded : ∀ i ∈ indices, degree (terms i) ≤ bound) :
    degree (finiteSum indices terms) ≤ bound := by
  suffices ∀ es : List (Expr s), (∀ e ∈ es, degree e ≤ bound) → degree (sum es) ≤ bound by
    apply this
    simpa using bounded
  intro es
  induction es with
  | nil => simp [sum, degree]
  | cons e es ih =>
      intro h
      exact max_le (h e (by simp)) (ih (fun a ha => h a (by simp [ha])))

theorem generator_degree (modes : Finset IntegerWavevector) (viscosity : ℝ) :
    degree (generator modes viscosity) ≤ 2 := by
  apply degree_finiteSum
  intro output _
  change max _ _ ≤ 2
  apply max_le _ (by simp [degree, row])
  apply degree_finiteSum
  intro first _
  apply degree_finiteSum
  intro second _
  split_ifs <;> simp [pair, velocityRow, row, degree]

def word (modes : Finset IntegerWavevector) (viscosity : ℝ) {s : Kind} (e : Expr s) (n : ℕ) : Expr s :=
  (act (generator modes viscosity))^[n] e

theorem word_degree (modes : Finset IntegerWavevector) (viscosity : ℝ) {s : Kind}
    (e : Expr s) (order : ℕ) : degree (word modes viscosity e order) ≤ degree e + order := by
  induction order with
  | zero => simp [word]
  | succ order previous =>
      simp only [word, Function.iterate_succ_apply']
      change degree (act (generator modes viscosity) (word modes viscosity e order)) ≤ _
      exact (degree_act _ (generator_degree modes viscosity) _).trans (by omega)

def velocity : Expr .state := .linear biotSavartCLM .input
def stress : Expr .stress := .bilinear mixedCLM velocity velocity

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativeRecoveryCoverage NativeRecoveryEscapeStress

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def sourceWord (source : StressAt escape) (index : ℕ) {s : Kind} (e : Expr s)
    (order : ℕ) (time : ℝ) : Value s :=
  eval (word (wholeRestartModes (NativeRecoveryEscapeCarrier.radius escape (source.refinement index)))
    nu.coeff e order) ((stage source index).trajectory time)

theorem sourceWord_hasDerivAt (source : StressAt escape) (index : ℕ) {s : Kind} (e : Expr s)
    (order : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (sourceWord source index e order) (sourceWord source index e (order + 1) time) time := by
  unfold sourceWord
  simp only [word, Function.iterate_succ_apply']
  apply eval_act_hasDerivAt
  rw [eval_generator]
  exact ((stage source index).physical time inside).1

theorem sourceWord_velocity (source : StressAt escape) (index : ℕ) (time : ℝ) :
    sourceWord source index velocity 0 time = rawField source index time := rfl

theorem sourceWord_velocityRate (source : StressAt escape) (index : ℕ) (time : ℝ) :
    sourceWord source index velocity 1 time = rawRate source index time := by
  change biotSavartCLM (eval (generator _ _) _) = _
  rw [eval_generator]
  rfl

theorem sourceWord_continuousOn (source : StressAt escape) (index : ℕ) {s : Kind} (e : Expr s)
    (order : ℕ) : ContinuousOn (sourceWord source index e order) (Icc (0 : ℝ) 1) :=
  fun time inside => (sourceWord_hasDerivAt source index e order time inside).continuousAt.continuousWithinAt

theorem sourceWord_stress (source : StressAt escape) (index : ℕ) (time : ℝ) :
    sourceWord source index stress 0 time = rawStress source index time := rfl

theorem sourceWord_stressRate (source : StressAt escape) (index : ℕ) (time : ℝ) :
    sourceWord source index stress 1 time = rawStressRate source index time := by
  change mixed (biotSavartCLM (eval (generator _ _) _)) (rawField source index time) +
    mixed (rawField source index time) (biotSavartCLM (eval (generator _ _) _)) = _
  rw [eval_generator]
  rfl

theorem sourceWord_integral (source : StressAt escape) (index : ℕ) {s : Kind} (e : Expr s)
    (order : ℕ) (first last : Icc (0 : ℝ) 1) :
    (∫ time in first.1..last.1, sourceWord source index e (order + 1) time) =
      sourceWord source index e order last.1 - sourceWord source index e order first.1 := by
  let : CompleteSpace (Value s) := by cases s <;> exact inferInstance
  have subset : uIcc first.1 last.1 ⊆ Icc (0 : ℝ) 1 := uIcc_subset_Icc first.2 last.2
  have continuous : ContinuousOn (sourceWord source index e (order + 1)) (Icc (0 : ℝ) 1) :=
    fun time inside => (sourceWord_hasDerivAt source index e (order + 1) time inside).continuousAt.continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time inside => sourceWord_hasDerivAt source index e order time (subset inside))
    (continuous.mono subset).intervalIntegrable

theorem source_stress_word_work (source : StressAt escape) (pointLe : point ≤ 1)
    (first last : NativeRecoveryTimeGramRaw.TimeNode) (wave : IntegerWavevector)
    (output input : Coordinate) :
    Tendsto (fun index => NativeCompleteStressCarrier.read
      (∫ time in (NativeRecoveryTimeGramRaw.timeAt escape pointLe (source.refinement index) first).1..
        (NativeRecoveryTimeGramRaw.timeAt escape pointLe (source.refinement index) last).1,
        sourceWord source index stress 1 time) wave output input)
      ((NativeRecoveryJointTimeKernel.generated source pointLe).refinement : Filter ℕ)
      (𝓝 (NativeRecoveryTimeGramReadout.stressRead source pointLe last wave output input -
        NativeRecoveryTimeGramReadout.stressRead source pointLe first wave output input)) := by
  simpa only [sourceWord_stressRate, rawWork] using
    source_stress_work source pointLe first last wave output input

end
end SaturationMonoid.NavierStokes.NativeSourcePolynomialAction
