import H0mework.Versions.R5a407445.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceHiddenWordFlowRha0286.SourceR0009.SourceHiddenWordFlow286
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The native emitter's literal raw recipe produces its finite-window source.

The data format follows original76.native_operator_inventory: two complete
33-state atoms, raw static/Fourier matrices, natural/capture/ion operators,
and four detector-time Poisson rates. It contains neither a completed flow
nor a Gram, density, mass, measure or normalization certificate. A separately
frozen exporter of the independently accepted same-C closed records must
issue a closed value of NativeWindowData;
the generic interpreter itself does not claim that such an actual value has
already been issued.

Natural modes are kept before optical transfer. Only their labels carry the
two physical flight offsets. Detector BG remains on its detector clock; the
later mature Bernoulli BG markers are a different source interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set
open scoped BigOperators Matrix.Norms.L2Operator

namespace SourceNativeKrausWindow292

open SourceKrausSurvival285 SourceHiddenWordFlow286

abbrev AtomIndex := Fin 33
abbrev JointIndex := AtomIndex × AtomIndex
abbrev AtomMatrix := Matrix AtomIndex AtomIndex ℂ
abbrev JointMatrix := Matrix JointIndex JointIndex ℂ
abbrev AtomicHilbert := EuclideanSpace ℂ JointIndex

structure RadicalTerm where
  radicand : ℕ
  coefficient : ℚ

abbrev RealLiteral := List RadicalTerm

def realValue (literal : RealLiteral) : ℝ :=
  (literal.map fun term => (term.coefficient : ℝ) * Real.sqrt term.radicand).sum

structure ComplexLiteral where
  realPart : RealLiteral
  imaginaryPart : RealLiteral

def complexValue (literal : ComplexLiteral) : ℂ :=
  (realValue literal.realPart : ℂ) + Complex.I * (realValue literal.imaginaryPart : ℂ)

structure SparseEntry where
  row : AtomIndex
  column : AtomIndex
  value : ComplexLiteral

abbrev SparseAtom := List SparseEntry

def atomMatrix (entries : SparseAtom) : AtomMatrix := fun i j =>
  (entries.map fun entry => if entry.row = i ∧ entry.column = j then complexValue entry.value else 0).sum

structure NonnegativeRate where
  value : ℚ
  nonnegative : 0 ≤ value

def rateAmplitude (rate : NonnegativeRate) : ℂ := Real.sqrt (rate.value : ℝ)

theorem rateAmplitude_squared (rate : NonnegativeRate) :
    rateAmplitude rate ^ 2 = (rate.value : ℂ) := by
  have positive : 0 ≤ (rate.value : ℝ) := by exact_mod_cast rate.nonnegative
  simpa only [rateAmplitude, ← Complex.ofReal_pow, Complex.ofReal_ratCast] using
    congrArg Complex.ofReal (Real.sq_sqrt positive)

structure RawJump where
  normalizedOperator : SparseAtom
  rate : NonnegativeRate

structure NaturalEntry where
  line : String
  excitedF : ℕ
  groundF : ℕ
  sphericalComponent : Fin 3
  jump : RawJump

structure CaptureEntry where
  groundF : ℕ
  groundM : ℤ
  jump : RawJump

structure IonEntry where
  sourceExcitedCoordinate : AtomIndex
  jump : RawJump

structure RawTone where
  angularFrequencyPerSecond : ℚ
  raisingOperatorPerSecond : SparseAtom

structure NativeSideData where
  staticHamiltonianPerSecond : SparseAtom
  tones : List RawTone
  natural : List NaturalEntry
  captures : List CaptureEntry
  ions : List IonEntry

structure NativeWindowData where
  startSeconds : ℚ
  firstReadySeconds : ℚ
  timeOrder : startSeconds ≤ firstReadySeconds
  actualPhaseEpochSeconds : ℚ
  sides : Fin 2 → NativeSideData
  flightSeconds : Fin 2 → NonnegativeRate
  detectorBetaPerSecond : Fin 4 → NonnegativeRate
  originalJointBasis : JointIndex

def embed (side : Fin 2) (M : AtomMatrix) : JointMatrix :=
  if side = 0 then Matrix.kronecker M 1 else Matrix.kronecker 1 M

def phase (frequency epoch : ℚ) (time : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (frequency : ℂ) * ((time - (epoch : ℝ) : ℝ) : ℂ))

theorem phase_continuous (frequency epoch : ℚ) : Continuous (phase frequency epoch) := by
  unfold phase
  fun_prop

def halfHamiltonianMatrix (data : NativeWindowData) (time : ℝ) : JointMatrix :=
  ∑ side : Fin 2,
    ((1/2 : ℂ) • embed side (atomMatrix (data.sides side).staticHamiltonianPerSecond) +
      ∑ index : Fin (data.sides side).tones.length,
        phase ((data.sides side).tones.get index).angularFrequencyPerSecond data.actualPhaseEpochSeconds time •
          embed side (atomMatrix ((data.sides side).tones.get index).raisingOperatorPerSecond))

theorem halfHamiltonianMatrix_continuous (data : NativeWindowData) :
    Continuous (halfHamiltonianMatrix data) := by
  unfold halfHamiltonianMatrix
  apply continuous_finsetSum Finset.univ
  intro side _
  apply continuous_const.add
  apply continuous_finsetSum Finset.univ
  intro index _
  exact (phase_continuous _ _).smul continuous_const

abbrev NaturalIndex (data : NativeWindowData) := Σ side : Fin 2, Fin (data.sides side).natural.length
abbrev CaptureIndex (data : NativeWindowData) := Σ side : Fin 2, Fin (data.sides side).captures.length
abbrev IonIndex (data : NativeWindowData) := Σ side : Fin 2, Fin (data.sides side).ions.length
abbrev JumpIndex (data : NativeWindowData) :=
  NaturalIndex data ⊕ (CaptureIndex data ⊕ (IonIndex data ⊕ Fin 4))

def embeddedJump (side : Fin 2) (jump : RawJump) : JointMatrix :=
  rateAmplitude jump.rate • embed side (atomMatrix jump.normalizedOperator)

def jumpMatrix (data : NativeWindowData) : JumpIndex data → JointMatrix
  | .inl index => embeddedJump index.1 ((data.sides index.1).natural.get index.2).jump
  | .inr (.inl index) => embeddedJump index.1 ((data.sides index.1).captures.get index.2).jump
  | .inr (.inr (.inl index)) => embeddedJump index.1 ((data.sides index.1).ions.get index.2).jump
  | .inr (.inr (.inr port)) => rateAmplitude (data.detectorBetaPerSecond port) • 1

def naturalFlightOffset (data : NativeWindowData) : JumpIndex data → ℝ
  | .inl index => (data.flightSeconds index.1).value
  | .inr _ => 0

theorem detector_background_clock (data : NativeWindowData) (port : Fin 4) :
    naturalFlightOffset data (.inr (.inr (.inr port))) = 0 := rfl

def halfHamiltonian (data : NativeWindowData) (time : ℝ) :
    AtomicHilbert →L[ℂ] AtomicHilbert := (Matrix.toEuclideanCLM (n := JointIndex) (𝕜 := ℂ)) (halfHamiltonianMatrix data time)

def jumps (data : NativeWindowData) (index : JumpIndex data) :
    AtomicHilbert →L[ℂ] AtomicHilbert := (Matrix.toEuclideanCLM (n := JointIndex) (𝕜 := ℂ)) (jumpMatrix data index)

theorem halfHamiltonian_continuous (data : NativeWindowData) : Continuous (halfHamiltonian data) :=
  (Matrix.toEuclideanCLM (n := JointIndex) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous.comp
    (halfHamiltonianMatrix_continuous data)

/-- The seven source fields are generated directly from literal coefficients. -/
def window (data : NativeWindowData) : RawKrausWindow AtomicHilbert (JumpIndex data) where
  left := data.startSeconds
  right := data.firstReadySeconds
  ordered := by exact_mod_cast data.timeOrder
  halfHamiltonian := halfHamiltonian data
  jumps := fun _ => jumps data
  halfHamiltonian_continuous := (halfHamiltonian_continuous data).continuousOn
  jumps_continuous := fun _ => continuous_const.continuousOn

theorem coefficient_exact (data : NativeWindowData) (time : ℝ) :
    (window data).coefficient time =
      (-Complex.I) • (halfHamiltonian data time + (halfHamiltonian data time).adjoint) -
        (1/2 : ℂ) • ∑ j : JumpIndex data, (jumps data j).adjoint * jumps data j := rfl

theorem complete_jump_energy (data : NativeWindowData) (time : ℝ) (x : AtomicHilbert) :
    2 * (inner ℂ x ((window data).coefficient time x)).re =
      -(∑ j : JumpIndex data, ‖jumps data j x‖^2) :=
  generator_energy (halfHamiltonian data time) (jumps data) x

def initialVector (data : NativeWindowData) : AtomicHilbert :=
  (EuclideanSpace.basisFun JointIndex ℂ) data.originalJointBasis

theorem initialVector_norm (data : NativeWindowData) : ‖initialVector data‖ = 1 :=
  (EuclideanSpace.basisFun JointIndex ℂ).orthonormal.norm_eq_one data.originalJointBasis

end SourceNativeKrausWindow292
