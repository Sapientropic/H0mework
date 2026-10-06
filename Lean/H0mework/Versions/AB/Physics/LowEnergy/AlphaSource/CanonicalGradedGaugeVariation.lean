import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalGradedVariation

/-! The generated native current supplies its own self-adjoint perturbation;
the derivative is taken through the same finite Gauss occurrence. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedGaugeVariation
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreDifferential GaussCoreHilbert
open GaussQuantumMultiplier CanonicalGradedCurrent
open SourceFamilyOperator
open GaussUnitaryHistory (HistorySpace reader sourceFilter)
open scoped Topology InnerProductSpace ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder

local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

theorem gaugeMatrix_hermitian (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) :
    (gaugeMatrix z mu a).conjTranspose = gaugeMatrix z mu a := by
  cases mu with
  | temporal =>
    simp only [gaugeMatrix, Matrix.conjTranspose_smul, GaussNativeMatter.nativeFull_skew,
      Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]
  | spatial i =>
    simp only [gaugeMatrix, Matrix.conjTranspose_neg, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul, GaussMatterCore.matrixTerm_hermitian,
      Complex.star_def, Complex.conj_ofReal]

theorem boundedMatrix_symmetric (A : Matrix Mode Mode ℂ) (hermitian : A.conjTranspose=A) :
    (boundedMatrix A).toLinearMap.IsSymmetric := by
  intro x y
  have hx : Set.EqOn (fun x => inner ℂ (boundedMatrix A x) y)
      (fun x => inner ℂ x (boundedMatrix A y)) (Core : Set H) := by
    intro x hx
    obtain ⟨f,hf⟩ := embed_surjective_core ⟨x,hx⟩
    change embed f=x at hf
    rw [← hf]
    have hy : Set.EqOn (fun y => inner ℂ (boundedMatrix A (embed f)) y)
        (fun y => inner ℂ (embed f) (boundedMatrix A y)) (Core : Set H) := by
      intro y hy
      obtain ⟨g,hg⟩ := embed_surjective_core ⟨y,hy⟩
      change embed g=y at hg
      rw [← hg]
      dsimp only
      rw [boundedMatrix_core, boundedMatrix_core]
      exact (action_pair (fun _ => A) (fun _ => contDiffAt_const) (fun _ => hermitian) f g).symm
    exact hy.closure (by fun_prop) (by fun_prop) (GaussHistoryHilbert.fockTestDomain_dense y)
  exact hx.closure (by fun_prop) (by fun_prop) (GaussHistoryHilbert.fockTestDomain_dense x)

theorem gaugeReader_selfAdjoint (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) :
    IsSelfAdjoint (gaugeReader z mu a) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (boundedMatrix_symmetric (gaugeMatrix z mu a) (gaugeMatrix_hermitian z mu a))

def gaugeTime (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) (parameter t : ℝ) :
    HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (CanonicalGradedVariation.timeFamily GaussGradedCompression.compression
    GaussGradedCompression.compression_selfAdjoint (gaugeReader z mu a)
    (gaugeReader_selfAdjoint z mu a) parameter t)

def gaugeVariation (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) (t : ℝ) :
    HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (CanonicalGradedVariation.variationFamily GaussGradedCompression.compression
    GaussGradedCompression.compression_selfAdjoint (gaugeReader z mu a) t)

theorem gaugeTime_zero_parameter (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) (t : ℝ) :
    gaugeTime z mu a 0 t=GaussGradedUnitary.time t := by
  apply lift_congr sourceFilter
  intro F
  simp only [CanonicalGradedVariation.timeFamily, GaussGradedUnitary.finiteTime, zero_smul, add_zero]

theorem gaugeTime_derivative (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => gaugeTime z mu a parameter t) (gaugeVariation z mu a t) 0 :=
  CanonicalGradedVariation.lifted_parameter_derivative sourceFilter GaussGradedCompression.compression
    GaussGradedCompression.compression_selfAdjoint (gaugeReader z mu a)
    (gaugeReader_selfAdjoint z mu a) t

def currentOperator (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (parameter t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  gaugeTime z nu b parameter (-t) * reader (gaugeReader z mu a) * gaugeTime z nu b parameter t

def currentDerivative (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  gaugeVariation z nu b (-t) * reader (gaugeReader z mu a) * GaussGradedUnitary.time t +
    GaussGradedUnitary.time (-t) * reader (gaugeReader z mu a) * gaugeVariation z nu b t

theorem currentOperator_derivative (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => currentOperator z mu nu a b parameter t)
      (currentDerivative z mu nu a b t) 0 := by
  have h := ((gaugeTime_derivative z nu b (-t)).mul_const (reader (gaugeReader z mu a))).mul
    (gaugeTime_derivative z nu b t)
  simp only [gaugeTime_zero_parameter] at h
  convert h using 1 <;> rfl

def currentObservation (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (parameter t : ℝ) (x y : HistorySpace) : ℂ :=
  inner ℂ (historyProjection x) (currentOperator z mu nu a b parameter t (historyProjection y))

theorem currentObservation_derivative (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (t : ℝ) (x y : HistorySpace) :
    HasDerivAt (fun parameter : ℝ => currentObservation z mu nu a b parameter t x y)
      (inner ℂ (historyProjection x) (currentDerivative z mu nu a b t (historyProjection y))) 0 := by
  have h := ((ContinuousLinearMap.apply ℂ HistorySpace (historyProjection y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (currentOperator_derivative z mu nu a b t)
  convert (hasDerivAt_const (0 : ℝ) (historyProjection x)).inner ℂ h using 1
  all_goals first | rfl | (simp only [inner_zero_left, add_zero]; rfl)

#print axioms gaugeReader_selfAdjoint
#print axioms gaugeTime_derivative
#print axioms currentObservation_derivative
end LowEnergy.CanonicalGradedGaugeVariation
