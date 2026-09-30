import H0mework.NavierStokes.WindowHistoryCreation.Form
import H0mework.NavierStokes.StressEvolutionRegeneration.Affine
import H0mework.NavierStokes.WindowEnergyAugmented.Gradient

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCreationGeometry
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowOperatorGreen
open NativePhysicalFourier
open NativeWindowStressHeatSource (physical)
open NativeWindowFiniteGramFourier (fourierRead)
open NativeWindowStressOseenTest (evaluate evaluate_apply)
open NativeWindowAugmentedGradient (derivative derivative_apply)
open NativePhysicalGradient (multiplier)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem evaluate_synthesis (M : Finset IntegerWavevector) (v : physicalSpace M) (i : Coordinate) :
    evaluate M M i v=NativeWindowHighPressurePhysical.realSynthesis M (fun k => v.1 k i) := by rw [evaluate_apply]; rfl

theorem evaluate_complex (M : Finset IntegerWavevector) (closed : FiniteModeNegClosed M)
    (v : physicalSpace M) (i : Coordinate) (point : Torus) :
    (evaluate M M i v point : ℂ)=∑ k∈M,UnitAddTorus.mFourier k point*v.1 k i := by
  have reality (k : IntegerWavevector) : v.1 (waveNeg k) i=conj (v.1 k i) :=
    congrFun (physical_reality (fun {_} member => closed _ member) v k) i
  have source:=congrArg (fun f : C(Torus,ℂ) => f point)
    (NativeWindowHighPressurePhysical.realSynthesis_complex M closed (fun k => v.1 k i) reality)
  change (NativeWindowHighPressurePhysical.realSynthesis M (fun k => v.1 k i) point : ℂ)=
    NativeWindowStressHeatSource.polynomial M (fun k => v.1 k i) 0 0 point at source
  rw [evaluate_synthesis]
  simpa only [NativeWindowStressHeatSource.polynomial,pow_zero,one_mul,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,mul_comm] using source

theorem product_fourier (M : Finset IntegerWavevector) (closed : FiniteModeNegClosed M)
    (u v : physicalSpace M) (j i : Coordinate) (k : IntegerWavevector) :
    fourierRead k (evaluate M M j u*evaluate M M i v)=
      ∑ q∈M,if k-q∈M then u.1 (k-q) j*v.1 q i else 0 := by
  rw [evaluate_synthesis,evaluate_synthesis]
  exact NativeWindowHighPressurePhysical.real_product_coefficient M closed _ _
    (fun k => congrFun (physical_reality (fun {_} member => closed _ member) u k) j)
    (fun k => congrFun (physical_reality (fun {_} member => closed _ member) v k) i) k

def advection (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (u v : physicalSpace M) (i : Coordinate) : C(Torus,ℝ) :=
  -∑ j : Coordinate,evaluate M M j u*evaluate M M i (derivative M zero closed j v)

theorem advection_fourier (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (u v : physicalSpace M) (i : Coordinate) (k : IntegerWavevector) :
    fourierRead k (advection M zero closed u v i)=convectionCLM M (curlLift M u.1) k v.1 i := by
  simp only [advection,map_neg,map_sum,product_fourier M closed,derivative_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm,← Finset.sum_neg_distrib]
  simp only [convectionCLM,sum_apply,Finset.sum_apply,DFunLike.ite_apply,zero_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q included
  have same (p : IntegerWavevector) : p+q=k ↔ p=k-q := eq_sub_iff_add_eq.symm
  simp only [same,ite_apply,Pi.zero_apply]
  rw [Finset.sum_ite_eq']
  by_cases inside : k-q∈M
  · simp only [if_pos inside]
    have read:(lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 q) v.1=v.1 q := rfl
    simp only [pairCLM,smul_apply,evaluation,read,Pi.smul_apply,smul_eq_mul]
    rw [curlLift_reads M zero u.1 (physical_transverse u) (k-q) inside]
    simp only [dotProduct,Fin.sum_univ_three,multiplier,complexWavevector]
    ring
  · simp only [if_neg inside,Finset.sum_const_zero,neg_zero]

def transport (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (nu : Viscosity) (u v : physicalSpace M) : physicalSpace M :=
  convection M zero closed nu (curlLift M u.1)
    (curlLift_reality M closed u.1 (physical_reality (fun {_} member => closed _ member) u)) v

theorem transport_row (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (nu : Viscosity) (u v : physicalSpace M) (k : IntegerWavevector) :
    (transport M zero closed nu u v).1 k=if k∈M then transverseProjection k
      (fun i => fourierRead k (advection M zero closed u v i)) else 0 := by
  change ((frozenOperator M nu (curlLift M u.1)-frozenOperator M nu 0) v.1) k=_
  rw [NativeAffineTransport.difference_row]
  simp only [advection_fourier]
  rfl

theorem fourier_square (f : C(Torus,ℝ)) (M : Finset IntegerWavevector) :
    (∑ k∈M,‖fourierRead k f‖^2)≤‖physical f‖^2 := by
  let c:=(UnitAddTorus.mFourierBasis (d := Coordinate)).repr (physical f)
  have read (k : IntegerWavevector) : c k=fourierRead k f := by
    simp only [c,UnitAddTorus.mFourierBasis_repr,NativeWindowTraceTerminalCubic.physical_fourier]
  have paid:=(NativeWindowGreenTestForm.square_summable c).sum_le_tsum M (fun _ _ => sq_nonneg _)
  rw [← NativeWindowGreenTestForm.norm_square,LinearIsometryEquiv.norm_map] at paid
  simpa only [read] using paid

theorem pressure_contraction (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (nu : Viscosity) (u v : physicalSpace M) :
    ‖coefficients M (transport M zero closed nu u v)‖^2≤
      ∑ i : Coordinate,‖physical (advection M zero closed u v i)‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  change pairing M (transport M zero closed nu u v) (transport M zero closed nu u v)≤_
  rw [pairing_eq]
  simp only [complexCoordinateRealInner_self,transport_row]
  calc
    _≤∑ k∈M,complexCoordinateVectorNormSq (fun i => fourierRead k (advection M zero closed u v i)) := by
      apply Finset.sum_le_sum
      intro k inside
      rw [if_pos inside]
      exact transverseProjection_amplitudeSq_le k (fun h => zero (h ▸ inside)) _
    _=∑ i : Coordinate,∑ k∈M,‖fourierRead k (advection M zero closed u v i)‖^2 := by
      simp only [complexCoordinateVectorNormSq,Complex.normSq_eq_norm_sq]
      rw [Finset.sum_comm]
    _≤_ := Finset.sum_le_sum fun i _ => fourier_square _ M

def square (M : Finset IntegerWavevector) (v : physicalSpace M) : C(Torus,ℝ) :=
  ∑ i : Coordinate,evaluate M M i v*evaluate M M i v

def gradientSquare (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (v : physicalSpace M) : C(Torus,ℝ) :=
  ∑ j : Coordinate,square M (derivative M zero closed j v)

theorem transport_bound (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (nu : Viscosity) (u v : physicalSpace M) :
    ‖coefficients M (transport M zero closed nu u v)‖^2≤
      ∫point : Torus,square M u point*gradientSquare M zero closed v point := by
  apply (pressure_contraction M zero closed nu u v).trans
  simp only [NativeWindowTraceTerminalSynthesis.physical_square]
  have rowPaid (i : Coordinate):Integrable (fun point : Torus => (advection M zero closed u v i point)^2) := by
    exact ((advection M zero closed u v i).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_finsetSum Finset.univ (fun i _ => rowPaid i)]
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (((square M u).continuous.mul (gradientSquare M zero closed v).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  filter_upwards with point
  have row (i : Coordinate): (advection M zero closed u v i point)^2≤
      (∑ j : Coordinate,(evaluate M M j u point)^2)*(∑ j : Coordinate,(evaluate M M i (derivative M zero closed j v) point)^2) := by
    simpa only [advection,ContinuousMap.neg_apply,ContinuousMap.sum_apply,ContinuousMap.mul_apply,neg_sq] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Coordinate)
        (fun j => evaluate M M j u point) (fun j => evaluate M M i (derivative M zero closed j v) point)
  apply (Finset.sum_le_sum fun i _ => row i).trans_eq
  change (∑ i : Coordinate,(∑ j : Coordinate,(evaluate M M j u point)^2)*
    (∑ j : Coordinate,(evaluate M M i (derivative M zero closed j v) point)^2))=
      (∑ j : Coordinate,evaluate M M j u point*evaluate M M j u point)*
      (∑ j : Coordinate,∑ i : Coordinate,evaluate M M i (derivative M zero closed j v) point*
        evaluate M M i (derivative M zero closed j v) point)
  simp only [← pow_two,← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem pairing_mass (M : Finset IntegerWavevector) (v : physicalSpace M) :
    pairing M v v=∑ k∈M,∑ i : Coordinate,‖v.1 k i‖^2 := by
  simp only [pairing_eq,complexCoordinateRealInner_self,complexCoordinateVectorNormSq,Complex.normSq_eq_norm_sq]

theorem curl_mass (M : Finset IntegerWavevector) (zero : 0∉M) (v : physicalSpace M) :
    curlPair M v.1 v.1=(2*Real.pi)^2*(∑ k∈M,integerWaveNormSq k*(∑ i : Coordinate,‖v.1 k i‖^2)) := by
  rw [curlPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k inside
  rw [← curl_pair_row k (fun h => zero (h ▸ inside)) _ _ (physical_transverse v k inside) (physical_transverse v k inside)]
  simp only [complexCoordinateRealInner_self,complexCoordinateVectorNormSq,Complex.normSq_eq_norm_sq,integerWaveViscousMultiplier]
  ring

theorem derivative_mass (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M) (v : physicalSpace M) :
    (∑ j : Coordinate,pairing M (derivative M zero closed j v) (derivative M zero closed j v))=curlPair M v.1 v.1 := by
  simp only [pairing_mass,derivative_apply,Pi.smul_apply,smul_eq_mul,norm_mul,mul_pow]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,← Finset.sum_mul,NativePhysicalGradient.multiplier_sum_norm_sq]
  rw [curl_mass M zero]
  simp only [mul_assoc,← Finset.mul_sum]

theorem square_absorption (f : C(Torus,ℝ)) (M : Finset IntegerWavevector) (zero : 0∉M)
    (closed : FiniteModeNegClosed M) (v : physicalSpace M) (epsilon : ℝ) (positive : 0<epsilon) :
    (∫point : Torus,f point*square M v point)≤epsilon*curlPair M v.1 v.1+
      NativeWindowHistoryCreationForm.budget ‖physical f‖ (epsilon*(2*Real.pi)^2)*pairing M v v := by
  have rowPaid (i : Coordinate):Integrable (fun x : Torus => f x*(evaluate M M i v x)^2) :=
    (f.continuous.mul ((evaluate M M i v).continuous.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have written:(∫point : Torus,f point*square M v point)=∑ i : Coordinate,∫point : Torus,f point*(evaluate M M i v point)^2 := by
    rw [← integral_finsetSum Finset.univ (fun i _ => rowPaid i)]
    apply integral_congr_ae
    filter_upwards with point
    change f point*(∑ i : Coordinate,evaluate M M i v point*evaluate M M i v point)=_
    simp only [Finset.mul_sum,pow_two]
  rw [written]
  have positiveScale:0<epsilon*(2*Real.pi)^2 := mul_pos positive (sq_pos_of_pos (by positivity))
  have paid:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun i _ =>
    (le_abs_self _).trans (NativeWindowHistoryCreationForm.physical_absorption f (evaluate M M i v) M (fun k => v.1 k i)
      (evaluate_complex M closed v i) (epsilon*(2*Real.pi)^2) positiveScale)
  apply paid.trans_eq
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_comm (s := Finset.univ) (t := M)]
  simp only [← Finset.mul_sum,pairing_mass,curl_mass M zero]
  ring

theorem gradient_absorption (f : C(Torus,ℝ)) (M : Finset IntegerWavevector) (zero : 0∉M)
    (closed : FiniteModeNegClosed M) (nu : Viscosity) (v : physicalSpace M) (epsilon : ℝ) (positive : 0<epsilon) :
    (∫point : Torus,f point*gradientSquare M zero closed v point)≤
      epsilon*pairing M (laplacian M zero closed nu v) (laplacian M zero closed nu v)+
      NativeWindowHistoryCreationForm.budget ‖physical f‖ (epsilon*(2*Real.pi)^2)*curlPair M v.1 v.1 := by
  have rowPaid (j : Coordinate):Integrable (fun x : Torus => f x*square M (derivative M zero closed j v) x) :=
    (f.continuous.mul (square M (derivative M zero closed j v)).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have written:(∫point : Torus,f point*gradientSquare M zero closed v point)=
      ∑ j : Coordinate,∫point : Torus,f point*square M (derivative M zero closed j v) point := by
    rw [← integral_finsetSum Finset.univ (fun j _ => rowPaid j)]
    apply integral_congr_ae
    filter_upwards with point
    change f point*(∑ j : Coordinate,square M (derivative M zero closed j v) point)=_
    rw [Finset.mul_sum]
  rw [written]
  have paid:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun j _ =>
    square_absorption f M zero closed (derivative M zero closed j v) epsilon positive
  exact paid.trans_eq (by
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,NativeWindowAugmentedGradient.palinstrophy_original (nu := nu),derivative_mass])

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCreationGeometry
