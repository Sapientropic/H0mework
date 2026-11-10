import H0mework.Versions.Ra4744604.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceEndpointRecyclingRha0300.SourceR0006.SourceEndpointWords300
import H0mework.Versions.Ra4744604.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceOpenFieldKernelRha0299.SourceR0006.SourceExactDensityFlow299

/-! The original159 material has two different roles: its exact source syntax
and numerical centres accompanied by prices. This interpreter uses the former.
Its real parameters remain open; neither a finished flow nor a dissipation
identity is a field. Bath coordinates retain G[nu,mu], not a chosen square root.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
open Set
open scoped BigOperators Topology

namespace SourceOpenProgramme301
open SourceNativeKrausWindow292 SourceOpenFieldKernel299
open SourceKrausSurvival285 SourceHiddenWordFlow286

abbrev Atom := SourceNativeKrausWindow292.AtomicHilbert
abbrev Op := Atom →L[ℂ] Atom
abbrev Action := Op →L[ℂ] Op

/-- Real source coefficients, rather than rational approximants to a theta point. -/
structure Exponential where
  realQuadratic : ℝ
  realLinear : ℝ
  realConstant : ℝ
  imaginaryLinear : ℝ
  imaginaryConstant : ℝ

def Exponential.value (raw : Exponential) (time : ℝ) : ℂ :=
  Complex.exp (((raw.realQuadratic : ℂ) * (time : ℂ)^2 +
    (raw.realLinear : ℂ) * (time : ℂ) + (raw.realConstant : ℂ)) +
      Complex.I * ((raw.imaginaryLinear : ℂ) * (time : ℂ) +
        (raw.imaginaryConstant : ℂ)))

theorem Exponential.continuous (raw : Exponential) : Continuous raw.value := by
  unfold Exponential.value
  fun_prop

inductive Scalar where
  | constant : ℂ → Scalar
  | squareRoot : ℝ → Scalar
  | exponential : Exponential → Scalar
  | add : Scalar → Scalar → Scalar
  | multiply : Scalar → Scalar → Scalar
  | conjugate : Scalar → Scalar

def Scalar.value : Scalar → ℝ → ℂ
  | .constant z, _ => z
  | .squareRoot r, _ => Real.sqrt r
  | .exponential raw, time => raw.value time
  | .add left right, time => left.value time + right.value time
  | .multiply left right, time => left.value time * right.value time
  | .conjugate raw, time => star (raw.value time)

theorem Scalar.continuous (raw : Scalar) : Continuous raw.value := by
  induction raw with
  | constant => exact continuous_const
  | squareRoot => exact continuous_const
  | exponential raw => exact raw.continuous
  | add left right hl hr => exact hl.add hr
  | multiply left right hl hr => exact hl.mul hr
  | conjugate raw h => exact continuous_star.comp h

def fourier (frequency epoch : ℝ) : Scalar :=
  .exponential ⟨0, 0, 0, -frequency, frequency * epoch⟩

theorem fourier_value (frequency epoch time : ℝ) :
    (fourier frequency epoch).value time =
      Complex.exp (-Complex.I*(frequency : ℂ)*((time-epoch : ℝ) : ℂ)) := by
  unfold fourier Scalar.value Exponential.value
  congr 1
  push_cast
  ring

def gaussian (origin centre sigmaSquared carrier phase : ℝ) : Scalar :=
  .exponential ⟨-(4*sigmaSquared)⁻¹,
    (origin+centre)/(2*sigmaSquared), -(origin+centre)^2/(4*sigmaSquared),
    -carrier, carrier*origin+phase⟩

/-- The source convention is the amplitude Gaussian, with 4 sigma squared. -/
theorem gaussian_value (origin centre sigmaSquared carrier phase time : ℝ) :
    (gaussian origin centre sigmaSquared carrier phase).value time =
      Complex.exp (((-(time-origin-centre)^2/(4*sigmaSquared) : ℝ) : ℂ) +
        Complex.I * ((-carrier*(time-origin)+phase : ℝ) : ℂ)) := by
  unfold gaussian Scalar.value Exponential.value
  congr 1
  push_cast
  by_cases zeroVariance : (sigmaSquared : ℂ) = 0
  · simp only [zeroVariance, mul_zero, zero_mul, inv_zero, div_zero,
      neg_zero, zero_add, add_zero]
    ring
  · field_simp [zeroVariance]
    ring

theorem frame_fourier_phase (frequency epoch frameOmega frameOrigin flight arrival : ℝ) :
    Complex.exp (Complex.I*(frameOmega : ℂ)*
      ((arrival-flight-frameOrigin : ℝ) : ℂ)) *
        (fourier frequency epoch).value (arrival-flight) =
      Complex.exp (Complex.I*
        (((frameOmega-frequency)*arrival+frequency*(epoch+flight)-
          frameOmega*(frameOrigin+flight) : ℝ) : ℂ)) := by
  rw [fourier_value, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Original68's carrier becomes zero with exactly this phase and origin. -/
theorem frame_gaussian_phase (origin centre sigmaSquared omega phase frameOrigin flight arrival : ℝ) :
    Complex.exp (Complex.I*(omega : ℂ)*((arrival-flight-frameOrigin : ℝ) : ℂ)) *
        (gaussian origin centre sigmaSquared omega phase).value (arrival-flight) =
      (gaussian (origin+flight) centre sigmaSquared 0
        (phase+omega*(origin-frameOrigin))).value arrival := by
  rw [gaussian_value, gaussian_value, ← Complex.exp_add]
  congr 1
  push_cast
  ring

inductive OperatorExpr where
  | zero : OperatorExpr
  | identity : OperatorExpr
  | atom : Fin 2 → SparseAtom → OperatorExpr
  | add : OperatorExpr → OperatorExpr → OperatorExpr
  | multiply : OperatorExpr → OperatorExpr → OperatorExpr
  | scale : Scalar → OperatorExpr → OperatorExpr
  | adjoint : OperatorExpr → OperatorExpr
  | translate : ℝ → OperatorExpr → OperatorExpr

def OperatorExpr.value : OperatorExpr → ℝ → Op
  | .zero, _ => 0
  | .identity, _ => 1
  | .atom side raw, _ => Matrix.toEuclideanCLM (n := JointIndex) (𝕜 := ℂ)
      (embed side (atomMatrix raw))
  | .add left right, time => left.value time + right.value time
  | .multiply left right, time => left.value time * right.value time
  | .scale coefficient raw, time => coefficient.value time • raw.value time
  | .adjoint raw, time => (raw.value time).adjoint
  | .translate offset raw, time => raw.value (time-offset)

theorem OperatorExpr.continuous (raw : OperatorExpr) : Continuous raw.value := by
  induction raw with
  | zero => exact continuous_const
  | identity => exact continuous_const
  | atom => exact continuous_const
  | add left right hl hr => exact hl.add hr
  | multiply left right hl hr => exact hl.mul hr
  | scale coefficient raw h => exact coefficient.continuous.smul h
  | adjoint raw h =>
      exact (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Atom) (F := Atom)).continuous.comp h
  | translate offset raw h => exact h.comp (continuous_id.sub continuous_const)

structure NonnegativeReal where
  value : ℝ
  nonnegative : 0 ≤ value

structure SourceUnit where
  secondsPerUnit : ℝ
  positive : 0 < secondsPerUnit

/-- Source93's width/u. Numerical pi enclosure radii are not new coordinates. -/
def naturalFromWidth (unit : SourceUnit) (width : NonnegativeReal)
    (side : Fin 2) (normalizedOperator : SparseAtom) : OperatorExpr :=
  .scale (.squareRoot (width.value/unit.secondsPerUnit)) (.atom side normalizedOperator)

theorem natural_width_rate (unit : SourceUnit) (width : NonnegativeReal) :
    (Real.sqrt (width.value/unit.secondsPerUnit))^2 = width.value/unit.secondsPerUnit :=
  Real.sq_sqrt (div_nonneg width.nonnegative unit.positive.le)

def captureFromUnit (unit : SourceUnit) (coupling : ℂ) (occupation : NonnegativeReal)
    (side : Fin 2) (normalizedOperator : SparseAtom) : OperatorExpr :=
  .scale (.constant (coupling*(Real.sqrt occupation.value : ℂ)/
      (Real.sqrt unit.secondsPerUnit : ℂ)))
    (.atom side normalizedOperator)

/-- An SI-valued jump amplitude receives no additional unit quotient. -/
def fixedSIJump (amplitude : ℂ) (side : Fin 2) (normalizedOperator : SparseAtom) : OperatorExpr :=
  .scale (.constant amplitude) (.atom side normalizedOperator)

def sumOperators (terms : List OperatorExpr) : OperatorExpr :=
  terms.foldr OperatorExpr.add .zero

structure FourierDrive where
  angularFrequencyPerSecond : ℝ
  phaseEpochSeconds : ℝ
  raisingPerSecond : OperatorExpr

def FourierDrive.expression (raw : FourierDrive) : OperatorExpr :=
  .scale (fourier raw.angularFrequencyPerSecond raw.phaseEpochSeconds) raw.raisingPerSecond

structure GaussianDrive where
  originSeconds : ℝ
  centreSeconds : ℝ
  sigmaSquaredSeconds : ℝ
  positiveVariance : 0 < sigmaSquaredSeconds
  carrierPerSecond : ℝ
  phaseRadians : ℝ
  raisingPerSecond : OperatorExpr

def GaussianDrive.expression (raw : GaussianDrive) : OperatorExpr :=
  .scale (gaussian raw.originSeconds raw.centreSeconds raw.sigmaSquaredSeconds
    raw.carrierPerSecond raw.phaseRadians) raw.raisingPerSecond

structure HamiltonianRecipe where
  staticPerSecond : OperatorExpr
  Fourier : List FourierDrive
  Gaussian : List GaussianDrive

/-- H is this half plus its adjoint. A duration does not truncate a Gaussian. -/
def HamiltonianRecipe.expression (raw : HamiltonianRecipe) : OperatorExpr :=
  .add (.scale (.constant (1/2 : ℂ)) raw.staticPerSecond)
    (sumOperators ((raw.Fourier.map FourierDrive.expression) ++
      (raw.Gaussian.map GaussianDrive.expression)))

structure RetardedClocks where
  flight : Fin 2 → NonnegativeReal
  origin : Fin 2 → ℝ
  omega : Fin 2 → ℝ

def d2Sparse (isD2 : AtomIndex → Bool) : SparseAtom :=
  List.ofFn fun coordinate : AtomIndex =>
    ⟨coordinate, coordinate,
      ⟨[⟨1, if isD2 coordinate then 1 else 0⟩], []⟩⟩

def modeSide (mode : Fin 6) : Fin 2 := if mode.val < 3 then 0 else 1

def modePolarization (mode : Fin 6) : Fin 3 :=
  ⟨mode.val % 3, Nat.mod_lt _ (by decide)⟩

def detectorWing (port : Fin 4) : Fin 2 := if port.val < 2 then 0 else 1

def detectorPolarization (port : Fin 4) : Fin 2 :=
  ⟨port.val % 2, Nat.mod_lt _ (by decide)⟩

def modeCode (side : Fin 2) (q : Fin 3) : Fin 6 :=
  ⟨3*side.val+q.val, by omega⟩

def detectorCode (wing polarization : Fin 2) : Fin 4 :=
  ⟨2*wing.val+polarization.val, by omega⟩

structure OpticalRecipe where
  splitter : Matrix (Fin 2) (Fin 2) ℂ
  collection : Fin 2 → Matrix (Fin 2) (Fin 3) ℂ
  efficiency : Fin 4 → NonnegativeReal

/-- Original93: splitter times collection times square-root detector efficiency. -/
def OpticalRecipe.transfer (raw : OpticalRecipe) : Matrix (Fin 4) (Fin 6) ℂ :=
  fun port mode => raw.splitter (detectorWing port) (modeSide mode) *
    raw.collection (modeSide mode) (detectorPolarization port) (modePolarization mode) *
      (Real.sqrt (raw.efficiency port).value : ℂ)

theorem OpticalRecipe.original_row_column (raw : OpticalRecipe)
    (wing polarization side : Fin 2) (q : Fin 3) :
    raw.transfer (detectorCode wing polarization) (modeCode side q) =
      raw.splitter wing side * raw.collection side polarization q *
        (Real.sqrt (raw.efficiency (detectorCode wing polarization)).value : ℂ) := by
  fin_cases wing <;> fin_cases polarization <;> fin_cases side <;> fin_cases q <;> rfl

/-- This uses emission = arrival-flight, never a common arrival cut. -/
def RetardedClocks.naturalPhase (clock : RetardedClocks) (isD2 : Bool)
    (side : Fin 2) (arrival : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (if isD2 then (clock.omega side : ℂ) else 0) *
    ((arrival-(clock.flight side).value-clock.origin side : ℝ) : ℂ))

theorem RetardedClocks.naturalPhase_continuous (clock : RetardedClocks)
    (isD2 : Bool) (side : Fin 2) : Continuous (clock.naturalPhase isD2 side) := by
  unfold RetardedClocks.naturalPhase
  fun_prop

theorem RetardedClocks.D2_phase (clock : RetardedClocks) (side : Fin 2) (arrival : ℝ) :
    clock.naturalPhase true side arrival =
      Complex.exp (-Complex.I * (clock.omega side : ℂ) *
        ((arrival-(clock.flight side).value-clock.origin side : ℝ) : ℂ)) := rfl

structure Material (Group : Type*) where
  begin : ℝ
  finish : ℝ
  ordered : begin ≤ finish
  clocks : RetardedClocks
  active : Fin 2 → Bool
  isD2 : AtomIndex → Bool
  laboratoryHalfHamiltonian : Fin 2 → HamiltonianRecipe
  groupIsD2 : Group → Bool
  naturalEmission : Group → Fin 6 → OperatorExpr
  captures : Fin 2 → List OperatorExpr
  ions : Fin 2 → List OperatorExpr
  optics : OpticalRecipe
  detectorBeta : Fin 4 → NonnegativeReal

variable {Group : Type*} [Fintype Group] [DecidableEq Group]

def Material.transfer (raw : Material Group) : Matrix (Fin 4) (Fin 6) ℂ := raw.optics.transfer

def Material.projector (raw : Material Group) (side : Fin 2) : Op :=
  (OperatorExpr.atom side (d2Sparse raw.isD2)).value 0

def Material.frameSide (raw : Material Group) (side : Fin 2) (arrival : ℝ) : Op :=
  Complex.exp (Complex.I * (raw.clocks.omega side : ℂ) *
    ((arrival-(raw.clocks.flight side).value-raw.clocks.origin side : ℝ) : ℂ)) •
      raw.projector side + (1-raw.projector side)

omit [Fintype Group] [DecidableEq Group] in
theorem Material.frameSide_continuous (raw : Material Group) (side : Fin 2) :
    Continuous (raw.frameSide side) := by
  unfold Material.frameSide
  fun_prop

/-- H_rot = U H U* - omega P, hence K_rot has +i omega P. -/
def Material.halfHamiltonian (raw : Material Group) (arrival : ℝ) : Op :=
  ∑ side : Fin 2,
    if raw.active side then (raw.frameSide side arrival *
      (raw.laboratoryHalfHamiltonian side).expression.value (arrival-(raw.clocks.flight side).value) *
        (raw.frameSide side arrival).adjoint -
      ((raw.clocks.omega side / 2 : ℝ) : ℂ) • raw.projector side) else 0

omit [Fintype Group] [DecidableEq Group] in
theorem Material.halfHamiltonian_continuous (raw : Material Group) :
    Continuous raw.halfHamiltonian := by
  unfold Material.halfHamiltonian
  apply continuous_finsetSum Finset.univ
  intro side _
  split_ifs
  swap
  · exact continuous_const
  exact (((raw.frameSide_continuous side).mul
    ((raw.laboratoryHalfHamiltonian side).expression.continuous.comp
      (continuous_id.sub continuous_const))).mul
        ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Atom) (F := Atom)).continuous.comp
          (raw.frameSide_continuous side))).sub continuous_const

def Material.natural (raw : Material Group) (group : Group) (mode : Fin 6)
    (arrival : ℝ) : Op :=
  if raw.active (modeSide mode) then
    raw.clocks.naturalPhase (raw.groupIsD2 group) (modeSide mode) arrival •
    (raw.naturalEmission group mode).value
      (arrival-(raw.clocks.flight (modeSide mode)).value) else 0

omit [Fintype Group] [DecidableEq Group] in
theorem Material.natural_continuous (raw : Material Group) (group : Group) (mode : Fin 6) :
    Continuous (raw.natural group mode) := by
  unfold Material.natural
  split_ifs
  swap
  · exact continuous_const
  exact (raw.clocks.naturalPhase_continuous _ _).smul
    ((raw.naturalEmission group mode).continuous.comp (continuous_id.sub continuous_const))

abbrev CaptureIndex (raw : Material Group) := Σ side : Fin 2, Fin (raw.captures side).length
abbrev IonIndex (raw : Material Group) := Σ side : Fin 2, Fin (raw.ions side).length
abbrev JumpIndex (raw : Material Group) := (Group × Fin 6) ⊕ (CaptureIndex raw ⊕ IonIndex raw)

def Material.localJump (raw : Material Group) (side : Fin 2) (op : OperatorExpr)
    (arrival : ℝ) : Op :=
  if raw.active side then
    raw.frameSide side arrival * op.value (arrival-(raw.clocks.flight side).value) *
      (raw.frameSide side arrival).adjoint else 0

omit [Fintype Group] [DecidableEq Group] in
theorem Material.localJump_continuous (raw : Material Group) (side : Fin 2)
    (op : OperatorExpr) : Continuous (raw.localJump side op) := by
  unfold Material.localJump
  split_ifs
  swap
  · exact continuous_const
  exact ((raw.frameSide_continuous side).mul
    (op.continuous.comp (continuous_id.sub continuous_const))).mul
      ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Atom) (F := Atom)).continuous.comp
        (raw.frameSide_continuous side))

def Material.jump (raw : Material Group) (index : JumpIndex raw) (arrival : ℝ) : Op :=
  match index with
  | .inl entry => raw.natural entry.1 entry.2 arrival
  | .inr (.inl entry) => raw.localJump entry.1 ((raw.captures entry.1).get entry.2) arrival
  | .inr (.inr entry) => raw.localJump entry.1 ((raw.ions entry.1).get entry.2) arrival

omit [Fintype Group] [DecidableEq Group] in
theorem Material.jump_continuous (raw : Material Group) (index : JumpIndex raw) :
    Continuous (raw.jump index) := by
  rcases index with entry | (entry | entry)
  · exact raw.natural_continuous entry.1 entry.2
  · exact raw.localJump_continuous _ _
  · exact raw.localJump_continuous _ _

def Material.window (raw : Material Group) : RawKrausWindow Atom (JumpIndex raw) where
  left := raw.begin
  right := raw.finish
  ordered := raw.ordered
  halfHamiltonian := raw.halfHamiltonian
  jumps := fun time index => raw.jump index time
  halfHamiltonian_continuous := raw.halfHamiltonian_continuous.continuousOn
  jumps_continuous := fun index => (raw.jump_continuous index).continuousOn

omit [DecidableEq Group] in
/-- No R/K/dissipation-law field occurs in Material: all are generated here. -/
theorem Material.coefficient_exact (raw : Material Group) (time : ℝ) :
    raw.window.coefficient time =
      (-Complex.I) • (raw.halfHamiltonian time + (raw.halfHamiltonian time).adjoint) -
        (1/2 : ℂ) • ∑ j : JumpIndex raw, (raw.jump j time).adjoint * raw.jump j time := rfl

omit [DecidableEq Group] in
theorem Material.complete_jump_energy (raw : Material Group) (time : ℝ) (x : Atom) :
    2 * (inner ℂ x (raw.window.coefficient time x)).re =
      -(∑ j : JumpIndex raw, ‖raw.jump j time x‖^2) :=
  generator_energy (raw.halfHamiltonian time) (fun j => raw.jump j time) x

def portGram (transfer : Matrix (Fin 4) (Fin 6) ℂ) (mu nu : Fin 6) : ℂ :=
  ∑ port : Fin 4, transfer port mu * star (transfer port nu)

/-- The original passive_transfer complement, with its original matrix indices. -/
def lossGram (transfer : Matrix (Fin 4) (Fin 6) ℂ) (nu mu : Fin 6) : ℂ :=
  (if nu = mu then 1 else 0) - ∑ port : Fin 4, star (transfer port nu) * transfer port mu

theorem lossGram_source_complement (transfer : Matrix (Fin 4) (Fin 6) ℂ)
    (nu mu : Fin 6) :
    lossGram transfer nu mu =
      (1-transfer.conjTranspose*transfer : Matrix (Fin 6) (Fin 6) ℂ) nu mu := by
  simp [lossGram, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

theorem all_bath_delta (transfer : Matrix (Fin 4) (Fin 6) ℂ) (mu nu : Fin 6) :
    portGram transfer mu nu + lossGram transfer nu mu = if mu = nu then 1 else 0 := by
  classical
  have same : (∑ port : Fin 4, star (transfer port nu) * transfer port mu) =
      portGram transfer mu nu := by
    unfold portGram
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [lossGram, same]
  simp only [eq_comm]
  ring

/-- Independent left/right source arms are retained before a bath contraction. -/
def crossContraction (weight : Fin 6 → Fin 6 → ℂ) (left right : Fin 6 → Op)
    (rho : Op) : Op :=
  ∑ mu : Fin 6, ∑ nu : Fin 6, weight mu nu • (left mu * rho * (right nu).adjoint)

theorem crossContraction_add (a b : Fin 6 → Fin 6 → ℂ) (left right : Fin 6 → Op)
    (rho : Op) :
    crossContraction a left right rho + crossContraction b left right rho =
      crossContraction (fun mu nu => a mu nu+b mu nu) left right rho := by
  unfold crossContraction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mu _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro nu _
  exact (add_smul (a mu nu) (b mu nu)
    (left mu * rho * (right nu).adjoint)).symm

/-- The two legs need not be equal: this is a coherent kernel identity. -/
theorem six_bath_contraction (transfer : Matrix (Fin 4) (Fin 6) ℂ)
    (left right : Fin 6 → Op) (rho : Op) :
    crossContraction (portGram transfer) left right rho +
      crossContraction (fun mu nu => lossGram transfer nu mu) left right rho =
        ∑ mu : Fin 6, left mu * rho * (right mu).adjoint := by
  classical
  rw [crossContraction_add]
  unfold crossContraction
  apply Finset.sum_congr rfl
  intro mu _
  calc
    _ = ∑ nu : Fin 6, (if mu = nu then left mu * rho * (right nu).adjoint else 0) := by
      apply Finset.sum_congr rfl
      intro nu _
      change (portGram transfer mu nu + lossGram transfer nu mu) •
        (left mu * rho * (right nu).adjoint) =
          (if mu = nu then left mu * rho * (right nu).adjoint else 0)
      rw [all_bath_delta]
      split_ifs
      · exact one_smul ℂ _
      · exact zero_smul ℂ (left mu * rho * (right nu).adjoint : Op)
    _ = _ := by simp

omit [DecidableEq Group] in
theorem grouped_six_bath_contraction (transfer : Matrix (Fin 4) (Fin 6) ℂ)
    (left right : Group → Fin 6 → Op) (rho : Op) :
    (∑ group : Group, crossContraction (portGram transfer) (left group) (right group) rho) +
      (∑ group : Group, crossContraction (fun mu nu => lossGram transfer nu mu)
        (left group) (right group) rho) =
      ∑ group : Group, ∑ mu : Fin 6, left group mu * rho * (right group mu).adjoint := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun group _ => six_bath_contraction transfer _ _ rho

def Material.survivalCapture (raw : Material Group) (time : ℝ) (rho : Op) : Op :=
  raw.window.coefficient time * rho + rho * (raw.window.coefficient time).adjoint +
    ∑ j : CaptureIndex raw, raw.jump (.inr (.inl j)) time * rho *
      (raw.jump (.inr (.inl j)) time).adjoint

def Material.unobservedNatural (raw : Material Group) (time : ℝ) (rho : Op) : Op :=
  ∑ group : Group, crossContraction (fun mu nu => lossGram raw.transfer nu mu)
    (raw.natural group · time) (raw.natural group · time) rho

def Material.detectedNatural (raw : Material Group) (time : ℝ) (rho : Op) : Op :=
  ∑ group : Group, crossContraction (portGram raw.transfer)
    (raw.natural group · time) (raw.natural group · time) rho

def Material.background (raw : Material Group) (rho : Op) : Op :=
  ((∑ port : Fin 4, (raw.detectorBeta port).value : ℝ) : ℂ) • rho

def Material.quietAt (raw : Material Group) (time : ℝ) (rho : Op) : Op :=
  raw.survivalCapture time rho + raw.unobservedNatural time rho - raw.background rho

def Material.detectedAllAt (raw : Material Group) (time : ℝ) (rho : Op) : Op :=
  raw.detectedNatural time rho + raw.background rho

def Material.inclusiveAt (raw : Material Group) (time : ℝ) (rho : Op) : Op :=
  raw.survivalCapture time rho +
    ∑ group : Group, ∑ mode : Fin 6,
      raw.natural group mode time * rho * (raw.natural group mode time).adjoint

omit [DecidableEq Group] in
/-- Original quiet plus all four detector forks is inclusive, with APD BG
cancelled and natural recycling restored once. K is not modified or rebuilt. -/
theorem Material.quiet_detected_inclusive (raw : Material Group) (time : ℝ) (rho : Op) :
    raw.quietAt time rho + raw.detectedAllAt time rho = raw.inclusiveAt time rho := by
  have gram := grouped_six_bath_contraction raw.transfer
    (fun group mode => raw.natural group mode time)
    (fun group mode => raw.natural group mode time) rho
  change raw.detectedNatural time rho + raw.unobservedNatural time rho = _ at gram
  unfold Material.quietAt Material.detectedAllAt Material.inclusiveAt
  calc
    _ = raw.survivalCapture time rho +
        (raw.detectedNatural time rho + raw.unobservedNatural time rho) := by abel
    _ = _ := congrArg (fun value : Op => raw.survivalCapture time rho + value) gram

def wordPortGram (transfer : Matrix (Fin 4) (Fin 6) ℂ) (n : ℕ)
    (left right : Fin n → Fin 6) : ℂ :=
  ∏ i : Fin n, (portGram transfer (left i) (right i) + lossGram transfer (right i) (left i))

/-- Every word length including zero; no number cutoff enters the Gram identity. -/
theorem full_word_bath_delta (transfer : Matrix (Fin 4) (Fin 6) ℂ) (n : ℕ)
    (left right : Fin n → Fin 6) :
    wordPortGram transfer n left right = if left = right then 1 else 0 := by
  classical
  unfold wordPortGram
  simp only [all_bath_delta]
  by_cases same : left = right
  · subst right
    simp
  · obtain ⟨i, different⟩ : ∃ i, left i ≠ right i := by
      by_contra h
      apply same
      funext i
      exact not_not.mp (not_exists.mp h i)
    rw [if_neg same]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg different)

/-- c L rho R is bilinear in the trace pairing. Duality does not conjugate c. -/
structure Term where
  coefficient : ℂ
  left : Op
  right : Op

def Term.action (term : Term) : Action :=
  term.coefficient •
    ((ContinuousLinearMap.compL ℂ Atom Atom Atom term.left).comp
      ((ContinuousLinearMap.compL ℂ Atom Atom Atom).flip term.right))

def Term.dual (term : Term) : Term := ⟨term.coefficient, term.right, term.left⟩

theorem Term.action_apply (term : Term) (rho : Op) :
    term.action rho = term.coefficient • (term.left * rho * term.right) := rfl

theorem Term.dual_dual (term : Term) : term.dual.dual = term := by cases term; rfl

def termsAction (terms : List Term) : Action := (terms.map Term.action).sum
def dualTerms (terms : List Term) : List Term := terms.map Term.dual

end SourceOpenProgramme301
