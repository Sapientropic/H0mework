import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeSeed
import Mathlib.MeasureTheory.Function.L2Space

/-! Original Gauss half-density contact of the scalar--Canonical charged
fields. The full configuration-dependent scalar Gram is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoreHilbert GaussCoreDifferential GaussHalfDensity GaussHistoryHilbert GaussFockLift
open MeasureTheory Filter
open scoped InnerProductSpace ContDiff BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder

def flatValue (v : Flat) (z : physicalChart) : FockFiber :=
  WithLp.toLp 2 (fun word => v word z)

def weightedValue (f : QuantumTest) (z : physicalChart) : FockFiber :=
  WithLp.toLp 2 (fun word => (halfDensity word.card z : ℂ)*f z word)

theorem flat_value_inner_integrable (v w : Flat) :
    Integrable (fun z => inner ℂ (flatValue v z) (flatValue w z)) GaussHistoryHilbert.chartMeasure := by
  have h := integrable_finsetSum Finset.univ
    (fun word _ => L2.integrable_inner (𝕜 := ℂ) (v word) (w word))
  simpa only [flatValue,PiLp.inner_apply] using h

theorem flat_inner_integral (v w : Flat) :
    inner ℂ v w = ∫ z, inner ℂ (flatValue v z) (flatValue w z) ∂GaussHistoryHilbert.chartMeasure := by
  simp only [PiLp.inner_apply,L2.inner_def]
  exact (integral_finsetSum Finset.univ
    (fun word _ => L2.integrable_inner (𝕜 := ℂ) (v word) (w word))).symm

theorem flat_embed_value (f : QuantumTest) :
    ∀ᵐ z ∂GaussHistoryHilbert.chartMeasure, flatValue (fockHalfDensityEquiv (embed f)) z=weightedValue f z := by
  have each (word : Occupation) : ∀ᵐ z ∂GaussHistoryHilbert.chartMeasure,
      (fockHalfDensityEquiv (embed f)) word z = (halfDensity word.card z : ℂ)*f z word := by
    filter_upwards [fockHalfDensityEquiv_apply (embed f) word,
      (embed_ae f word).filter_mono (weighted_null_sets word.card).ae_le] with z hu hf
    rw [hu]
    change (halfDensity word.card z : ℂ)*(embed f word z) = _
    rw [hf]
  filter_upwards [ae_all_iff.mpr each] with z hz
  exact PiLp.ext (fun word => hz word)

theorem fiber_entry_apply (A : FiberOp) (f : FockFiber) (output : Occupation) :
    A f output = ∑ input : Occupation, entry A output input*f input := by
  have expansion : f=∑ input : Occupation, f input • EuclideanSpace.single input 1 := by
    apply PiLp.ext
    intro word
    simp [WithLp.ofLp_sum,Finset.sum_apply,EuclideanSpace.single,Pi.single_apply]
  conv_lhs => rw [expansion,map_sum]
  simp only [map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,entry]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem flat_lift_value (A : FiberOp) (v : Flat) :
    ∀ᵐ z ∂GaussHistoryHilbert.chartMeasure, flatValue (flatLift A v) z=A (flatValue v z) := by
  have each (output : Occupation) : ∀ᵐ z ∂GaussHistoryHilbert.chartMeasure,
      flatLift A v output z = A (flatValue v z) output := by
    rw [flatLift_apply]
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun input : Occupation => entry A output input • v input),
      ae_all_iff.mpr (fun input : Occupation => Lp.coeFn_smul (entry A output input) (v input))]
      with z hs hc
    rw [hs,fiber_entry_apply]
    apply Finset.sum_congr rfl
    intro input _
    rw [hc input]
    rfl
  filter_upwards [ae_all_iff.mpr each] with z hz
  exact PiLp.ext (fun word => hz word)

theorem flat_value_sum (v : Fin 3 → Flat) :
    ∀ᵐ z ∂GaussHistoryHilbert.chartMeasure, flatValue (∑ i, v i) z=∑ i, flatValue (v i) z := by
  have each (word : Occupation) : ∀ᵐ z ∂GaussHistoryHilbert.chartMeasure,
      (∑ i, v i) word z=(∑ i, flatValue (v i) z) word := by
    simp only [WithLp.ofLp_sum,Finset.sum_apply]
    exact Lp.coeFn_fun_finsetSum Finset.univ (fun i => v i word)
  filter_upwards [ae_all_iff.mpr each] with z hz
  exact PiLp.ext (fun word => hz word)

theorem weighted_scalar_value (c : SourceCoordinateSlice → ℂ)
    (smooth : ContDiff ℝ ∞ c) (f : QuantumTest) (z : physicalChart) :
    weightedValue (scalarMultiplier c smooth f) z=c z • weightedValue f z := by
  apply PiLp.ext
  intro word
  change (halfDensity word.card z : ℂ)*(c z*f z word)=c z*((halfDensity word.card z : ℂ)*f z word)
  ring

theorem source_sum_value (A : Fin 3 → FiberOp) (c : Fin 3 → SourceCoordinateSlice → ℂ)
    (smooth : ∀ i, ContDiff ℝ ∞ (c i)) (f : QuantumTest) :
    ∀ᵐ z ∂GaussHistoryHilbert.chartMeasure,
      flatValue (fockHalfDensityEquiv (∑ i, lift (A i) (embed (scalarMultiplier (c i) (smooth i) f)))) z =
        (∑ i, c i z • A i) (weightedValue f z) := by
  simp only [map_sum,lift_apply,LinearIsometryEquiv.apply_symm_apply]
  filter_upwards [flat_value_sum (fun i => flatLift (A i)
      (fockHalfDensityEquiv (embed (scalarMultiplier (c i) (smooth i) f)))),
    ae_all_iff.mpr (fun i => flat_lift_value (A i)
      (fockHalfDensityEquiv (embed (scalarMultiplier (c i) (smooth i) f)))),
    ae_all_iff.mpr (fun i => flat_embed_value (scalarMultiplier (c i) (smooth i) f))]
    with z hs ha hf
  rw [hs]
  simp only [sum_apply,smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ha i,hf i,weighted_scalar_value,map_smul]

theorem annihilation_source_value (channel spin : Fin 2) (f : QuantumTest) :
    ∀ᵐ z ∂GaussHistoryHilbert.chartMeasure,
      flatValue (fockHalfDensityEquiv (annihilationSource channel spin f)) z =
        fiberAnnihilation channel spin (GaussNativePotential.scalarField z) (weightedValue f z) := by
  simpa only [annihilation_source_apply,GaussCARHistory.annihilate,coefficient,fiberAnnihilation] using
    source_sum_value (fun color => GaussCARHistory.annihilateFiber (mode spin color))
      (coefficient channel) (coefficient_smooth channel) f

theorem creation_source_value (channel spin : Fin 2) (f : QuantumTest) :
    ∀ᵐ z ∂GaussHistoryHilbert.chartMeasure,
      flatValue (fockHalfDensityEquiv (creationSource channel spin f)) z =
        fiberCreation channel spin (GaussNativePotential.scalarField z) (weightedValue f z) := by
  simpa only [creationSource,LinearMap.sum_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,
    GaussCARHistory.create,coefficient,fiberCreation] using
    source_sum_value (fun color => GaussCARHistory.createFiber (mode spin color))
      (fun color z => star (coefficient channel color z))
      (fun color => ((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.contDiff).comp
        (coefficient_smooth channel color)) f

theorem fiber_creation_pair (channel spin : Fin 2) (phi : SourceQuantumScalarChart.Scalar)
    (v w : FockFiber) : inner ℂ (fiberCreation channel spin phi v) w =
      inner ℂ v (fiberAnnihilation channel spin phi w) := by
  simp only [fiberCreation,fiberAnnihilation,sum_apply,smul_apply,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right]
  apply Finset.sum_congr rfl
  intro color _
  have h : inner ℂ (GaussCARHistory.createFiber (mode spin color) v) w =
      inner ℂ v (GaussCARHistory.annihilateFiber (mode spin color) w) :=
    SourceCARBound.create_adjoint (mode spin color) v w
  rw [h]
  simp

theorem fiber_annihilation_pair (channel spin : Fin 2) (phi : SourceQuantumScalarChart.Scalar)
    (v w : FockFiber) : inner ℂ (fiberAnnihilation channel spin phi v) w =
      inner ℂ v (fiberCreation channel spin phi w) := by
  have h := congrArg (starRingEnd ℂ) (fiber_creation_pair channel spin phi w v)
  simpa only [inner_conj_symm] using h.symm

def contactCoefficient (a s b t : Fin 2) (z : SourceCoordinateSlice) : ℂ :=
  if s=t then scalarGram a b (GaussNativePotential.scalarField z) (GaussNativePotential.scalarField z) else 0

theorem contact_coefficient_smooth (a s b t : Fin 2) : ContDiff ℝ ∞ (contactCoefficient a s b t) := by
  change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice =>
    if s=t then scalarGram a b (GaussNativePotential.scalarField z) (GaussNativePotential.scalarField z) else 0)
  by_cases spin : s=t
  · simp only [if_pos spin,scalarGram]
    apply ContDiff.sum
    intro color _
    exact (coefficient_smooth a color).mul
      (((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.contDiff).comp (coefficient_smooth b color))
  · simpa only [if_neg spin] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : SourceCoordinateSlice => (0 : ℂ)))

def contactSource (a s b t : Fin 2) : QuantumTest →ₗ[ℂ] QuantumTest :=
  scalarMultiplier (contactCoefficient a s b t) (contact_coefficient_smooth a s b t)

theorem fiber_contact_pair (a s b t : Fin 2) (z : SourceCoordinateSlice) (v w : FockFiber) :
    inner ℂ (fiberCreation a s (GaussNativePotential.scalarField z) v)
      (fiberCreation b t (GaussNativePotential.scalarField z) w) +
    inner ℂ (fiberAnnihilation b t (GaussNativePotential.scalarField z) v)
      (fiberAnnihilation a s (GaussNativePotential.scalarField z) w) =
    contactCoefficient a s b t z * inner ℂ v w := by
  rw [fiber_creation_pair,fiber_annihilation_pair,←inner_add_right]
  have h := congrArg (fun A : FiberOp => A w)
    (fiber_contact a b s t (GaussNativePotential.scalarField z) (GaussNativePotential.scalarField z))
  change fiberAnnihilation a s _ (fiberCreation b t _ w)+
    fiberCreation b t _ (fiberAnnihilation a s _ w) = _ at h
  rw [h]
  by_cases spin : s=t <;> simp [contactCoefficient,spin,inner_smul_right]

end LowEnergy.GaussComposite
