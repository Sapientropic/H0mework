import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeMomentumCurvature
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceHamiltonianVolume
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeDoubleGramCurvatureForm
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeJointScalarGaugeCoefficientForm
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceNativeDensityTrace
open GaussLiveMomentum GaussCoreDifferential GaussCoreHilbert GaussHistoryHilbert
open GaussNativeEnergy GaussDensityCore GaussScalarTransport GaussFockPair
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceNativeMomentumCurvature SourceCoframeVolume SourceHamiltonianVolume
open scoped ContDiff Topology

private theorem density_ne (N : ℕ) (z : physicalChart) : complexDensity N z.val≠0 := by
  change (density N z.val : ℂ)≠0
  exact_mod_cast (density_pos N z).ne'

def coordinateDivergence (v : Ambient) (z : SourceCoordinateSlice) : ℂ :=
  ∑ i : FrameIndex,fderiv ℝ (fun x => (coefficient v i x : ℂ)) z (frame i)

def logarithmicDensity (N : ℕ) (v : Ambient) (z : SourceCoordinateSlice) : ℂ :=
  (complexDensity N z)⁻¹*fderiv ℝ (complexDensity N) z (direction v z)

private theorem frame_derivative_sum (N : ℕ) (v : Ambient) (z : SourceCoordinateSlice) :
    (∑ i : FrameIndex,(coefficient v i z : ℂ)*fderiv ℝ (complexDensity N) z (frame i))=
      fderiv ℝ (complexDensity N) z (direction v z) := by
  calc
    _ = ∑ i : FrameIndex,fderiv ℝ (complexDensity N) z (coefficient v i z • frame i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul,RCLike.real_smul_eq_coe_mul (K := ℂ)]
      rfl
    _ = fderiv ℝ (complexDensity N) z (∑ i : FrameIndex,coefficient v i z • frame i) :=
      (map_sum (fderiv ℝ (complexDensity N) z) _ _).symm
    _ = _ := congrArg (fderiv ℝ (complexDensity N) z) (frame.sum_repr (direction v z))

private theorem divergence_split (N : ℕ) (v : Ambient) (z : physicalChart) :
    divergenceCoefficient N v z.val=coordinateDivergence v z.val+logarithmicDensity N v z.val := by
  have hr := density_ne N z
  have hterm (i : FrameIndex) : (complexDensity N z.val)⁻¹*
      fderiv ℝ (fun x => complexDensity N x*(coefficient v i x : ℂ)) z.val (frame i)=
      fderiv ℝ (fun x => (coefficient v i x : ℂ)) z.val (frame i)+
        (complexDensity N z.val)⁻¹*((coefficient v i z.val : ℂ)*fderiv ℝ (complexDensity N) z.val (frame i)) := by
    rw [fderiv_fun_mul ((complexDensity_smooth N z).differentiableAt (by simp))
      ((coefficient_smooth v i z).differentiableAt (by simp))]
    change (complexDensity N z.val)⁻¹*
      (complexDensity N z.val*fderiv ℝ (fun x => (coefficient v i x : ℂ)) z.val (frame i)+
        (coefficient v i z.val : ℂ)*fderiv ℝ (complexDensity N) z.val (frame i))=_
    field_simp [hr]
  simp only [divergenceCoefficient,hterm,Finset.sum_add_distrib,←Finset.mul_sum,frame_derivative_sum,
    coordinateDivergence,logarithmicDensity]

def complexJacobian (z : SourceCoordinateSlice) : ℂ := jacobian (z.2.2 : Gauge)

private theorem jacobian_smooth (z : physicalChart) : ContDiffAt ℝ ∞ complexJacobian z.val := by
  have hg : ContDiff ℝ ∞ (fun x : SourceCoordinateSlice => (x.2.2 : Gauge)) :=
    coordinateSlice.subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have hj : ContDiffAt ℝ ∞ (fun x : SourceCoordinateSlice => jacobian (x.2.2 : Gauge)) z.val :=
    ContDiffAt.comp (g := jacobian) (f := fun x : SourceCoordinateSlice => (x.2.2 : Gauge))
      z.val (GaussDensityCore.jacobian_smooth z) hg.contDiffAt
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp z.val hj

private theorem density_factor (N : ℕ) (z : SourceCoordinateSlice) :
    complexDensity N z=complexJacobian z*(volume z : ℂ)^(N+2) := by
  simp only [complexDensity,density,complexJacobian,volume,Complex.ofReal_mul,Complex.ofReal_pow]

private theorem jacobian_ne (z : physicalChart) : complexJacobian z.val≠0 := by
  have h := density_ne 0 z
  rw [density_factor] at h
  exact (mul_ne_zero_iff.mp h).1

private theorem density_native_derivative (N : ℕ) (v : Ambient) (z : physicalChart) :
    fderiv ℝ (complexDensity N) z.val (direction v z.val)=
      (volume z.val : ℂ)^(N+2)*fderiv ℝ complexJacobian z.val (direction v z.val) := by
  have ht : HasDerivAt (fun t : ℝ => z.val+t • direction v z.val) (direction v z.val) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (direction v z.val)).const_add z.val
  have hd := ((complexDensity_smooth N z).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 ht (by simp)
  have hj := ((jacobian_smooth z).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 ht (by simp)
  have hp := hj.const_mul ((volume z.val : ℂ)^(N+2))
  have he : (fun t : ℝ => complexDensity N (z.val+t • direction v z.val))=
      fun t : ℝ => (volume z.val : ℂ)^(N+2)*complexJacobian (z.val+t • direction v z.val) := by
    funext t
    rw [density_factor]
    have hv : volume (z.val+t • direction v z.val)=volume z.val := by
      simp only [volume,direction,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
    rw [hv,mul_comm]
  change HasDerivAt (fun t : ℝ => complexDensity N (z.val+t • direction v z.val))
    (fderiv ℝ (complexDensity N) z.val (direction v z.val)) 0 at hd
  rw [he] at hd
  exact hd.unique hp

private theorem logarithmic_density_source (N : ℕ) (v : Ambient) (z : physicalChart) :
    logarithmicDensity N v z.val=(complexJacobian z.val)⁻¹*fderiv ℝ complexJacobian z.val (direction v z.val) := by
  have hJ := jacobian_ne z
  have hV : (volume z.val : ℂ)≠0 := by exact_mod_cast (volume_pos z).ne'
  rw [logarithmicDensity,density_native_derivative,density_factor]
  field_simp [hJ,hV]

/-- The original native divergence loses all Number/volume powers inside the same source coefficient. -/
theorem original_density_number_cancel (N : ℕ) (v : Ambient) (z : physicalChart) :
    divergenceCoefficient N v z.val=coordinateDivergence v z.val+
      (complexJacobian z.val)⁻¹*fderiv ℝ complexJacobian z.val (direction v z.val) := by
  rw [divergence_split,logarithmic_density_source]

private theorem determinant_trace_derivative {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.det≠0) :
    fderiv ℝ (fun M : Matrix ι ι ℝ => M.det) A B=A.det*Matrix.trace (B*A⁻¹) := by
  let D : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
    { toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
      cont := continuous_id.matrix_det }
  have hd := congrArg (fun L : (Matrix ι ι ℝ) →L[ℝ] ℝ => L B) (D.hasFDerivAt A).fderiv
  have he := hd.trans (D.linearDeriv_apply A B)
  change fderiv ℝ (fun M : Matrix ι ι ℝ => M.det) A B=∑ i : ι,(A.updateRow i (B i)).det at he
  rw [he]
  have hr (i : ι) : (A.updateRow i (B i)).det=(B*A⁻¹) i i*A.det := by
    have he : B i=∑ k : ι,(B*A⁻¹) i k • A k := by
      have hm := Matrix.nonsing_inv_mul_cancel_right (A := A) B (isUnit_iff_ne_zero.mpr hA)
      have hv := congrArg (fun M : Matrix ι ι ℝ => M i) hm.symm
      rw [hv]
      funext j
      simp only [Matrix.mul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [he,Matrix.det_updateRow_sum,smul_eq_mul]
  simp only [hr,←Finset.sum_mul,Matrix.trace,Matrix.diag]
  ring

/-- The actual differentiated inverse chart, with the coframe component identically zero. -/
def sourceDirectionalJacobian (v : Ambient) (z : SourceCoordinateSlice) : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice :=
  -(ContinuousLinearMap.prod (0 : SourceCoordinateSlice →L[ℝ] Coframe)
    ((ContinuousLinearMap.snd ℝ NativeLie Slice).comp
      ((inverseL z).comp (variationL.flip (inverseL z v)))))

private theorem direction_derivative (z : physicalChart) (u : Ambient) (h : SourceCoordinateSlice) :
    fderiv ℝ (direction u) z.val h=(0,(fderiv ℝ inverseL z.val h u).2) := by
  have hi := ((inverse_smooth z).differentiableAt (by simp)).hasFDerivAt
  have hv := hi.clm_apply (hasFDerivAt_const u z.val)
  have hp := (hasFDerivAt_const (0 : Coframe) z.val).prodMk hv.snd
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice => D h) hp.fderiv
  simp only [ContinuousLinearMap.coe_snd',ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,add_apply,zero_apply,map_zero,zero_add] at he
  change fderiv ℝ (fun x => ((0 : Coframe),(inverseL x u).2)) z.val h=_
  exact he

private theorem directional_jacobian_source (v : Ambient) (z : physicalChart) :
    fderiv ℝ (direction v) z.val=sourceDirectionalJacobian v z.val := by
  apply ContinuousLinearMap.ext
  intro h
  rw [direction_derivative,inverse_derivative]
  simp only [sourceDirectionalJacobian,neg_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.coe_snd',zero_apply,
    Prod.neg_mk,Prod.snd_neg,neg_zero]

private theorem coordinate_divergence_trace (v : Ambient) (z : physicalChart) :
    coordinateDivergence v z.val=
      (LinearMap.trace ℝ SourceCoordinateSlice (sourceDirectionalJacobian v z.val).toLinearMap : ℂ) := by
  have hc (i : FrameIndex) : fderiv ℝ (fun x => (coefficient v i x : ℂ)) z.val (frame i)=
      (frame.coord i (sourceDirectionalJacobian v z.val (frame i)) : ℂ) := by
    let L : SourceCoordinateSlice →L[ℝ] ℂ := Complex.ofRealCLM.comp (frame.coord i).toContinuousLinearMap
    have hd := ((direction_smooth v z).differentiableAt (by simp)).hasFDerivAt
    have hL : HasFDerivAt L L (direction v z.val) := L.hasFDerivAt
    have he := congrArg (fun T : SourceCoordinateSlice →L[ℝ] ℂ => T (frame i)) (hL.comp z.val hd).fderiv
    change fderiv ℝ (fun x => (coefficient v i x : ℂ)) z.val (frame i)=
      (frame.coord i (fderiv ℝ (direction v) z.val (frame i)) : ℂ) at he
    rw [directional_jacobian_source] at he
    exact he
  simp only [coordinateDivergence,hc,LinearMap.trace_eq_matrix_trace ℝ frame,Matrix.trace,Matrix.diag,
    LinearMap.toMatrix_apply,Complex.ofReal_sum]
  rfl

/-- The complete native density coefficient is the original inverse-chart trace plus the original gauge Jacobian current. -/
theorem original_density_inverse_trace (N : ℕ) (v : Ambient) (z : physicalChart) :
    divergenceCoefficient N v z.val=
      (LinearMap.trace ℝ SourceCoordinateSlice (sourceDirectionalJacobian v z.val).toLinearMap : ℂ)+
      (complexJacobian z.val)⁻¹*fderiv ℝ complexJacobian z.val (direction v z.val) := by
  rw [original_density_number_cancel,coordinate_divergence_trace]

abbrev GaugeMatrixIndex := Fin (Module.finrank ℝ OrbitSlice)

local instance : NormedAddCommGroup (Matrix GaugeMatrixIndex GaugeMatrixIndex ℝ) :=
  inferInstanceAs (NormedAddCommGroup (GaugeMatrixIndex → GaugeMatrixIndex → ℝ))
local instance : NormedSpace ℝ (Matrix GaugeMatrixIndex GaugeMatrixIndex ℝ) :=
  inferInstanceAs (NormedSpace ℝ (GaugeMatrixIndex → GaugeMatrixIndex → ℝ))

def relativeField (z : SourceCoordinateSlice) : Matrix GaugeMatrixIndex GaugeMatrixIndex ℝ :=
  relativeMatrix (z.2.2 : Gauge)

def realJacobian (z : SourceCoordinateSlice) : ℝ := jacobian (z.2.2 : Gauge)

private theorem relative_field_smooth : ContDiff ℝ ∞ relativeField := by
  have hm : ContDiff ℝ ∞ relativeMatrix := contDiff_pi.mpr (fun i => contDiff_pi.mpr (relativeMatrix_smooth i))
  have hg : ContDiff ℝ ∞ (fun x : SourceCoordinateSlice => (x.2.2 : Gauge)) :=
    coordinateSlice.subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd)
  exact hm.comp hg

private theorem real_jacobian_smooth (z : physicalChart) : ContDiffAt ℝ ∞ realJacobian z.val := by
  have hg : ContDiff ℝ ∞ (fun x : SourceCoordinateSlice => (x.2.2 : Gauge)) :=
    coordinateSlice.subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd)
  exact ContDiffAt.comp (g := jacobian) (f := fun x : SourceCoordinateSlice => (x.2.2 : Gauge))
    z.val (GaussDensityCore.jacobian_smooth z) hg.contDiffAt

private theorem determinant_differentiable {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    DifferentiableAt ℝ (fun M : Matrix ι ι ℝ => M.det) A := by
  let D : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
    { toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
      cont := continuous_id.matrix_det }
  exact (D.hasFDerivAt A).differentiableAt

def relativeGaugeTrace (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  Matrix.trace (fderiv ℝ relativeField z (direction v z)*(relativeField z)⁻¹)

private theorem real_jacobian_current (v : Ambient) (z : physicalChart) :
    fderiv ℝ realJacobian z.val (direction v z.val)=realJacobian z.val*relativeGaugeTrace v z.val := by
  have hn : (relativeField z.val).det≠0 := by
    simpa only [relativeField,relativeMatrix,LinearMap.det_toMatrix] using residual_relative_det z
  have hR := (relative_field_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have hD := (determinant_differentiable (relativeField z.val)).hasFDerivAt.comp z.val hR
  by_cases hpos : 0<(relativeField z.val).det
  · have hJ := (hD.abs_of_pos hpos).const_mul sourceJacobian
    have he := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℝ => L (direction v z.val)) hJ.fderiv
    change fderiv ℝ realJacobian z.val (direction v z.val)=sourceJacobian*
      fderiv ℝ (fun M : Matrix GaugeMatrixIndex GaugeMatrixIndex ℝ => M.det) (relativeField z.val)
        (fderiv ℝ relativeField z.val (direction v z.val)) at he
    rw [determinant_trace_derivative _ _ hn] at he
    change _=(sourceJacobian*|(relativeField z.val).det|)*relativeGaugeTrace v z.val
    rw [abs_of_pos hpos]
    exact he.trans (mul_assoc _ _ _).symm
  · have hneg : (relativeField z.val).det<0 := lt_of_le_of_ne (le_of_not_gt hpos) hn
    have hJ := (hD.abs_of_neg hneg).const_mul sourceJacobian
    have he := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℝ => L (direction v z.val)) hJ.fderiv
    change fderiv ℝ realJacobian z.val (direction v z.val)=sourceJacobian*
      (-fderiv ℝ (fun M : Matrix GaugeMatrixIndex GaugeMatrixIndex ℝ => M.det) (relativeField z.val)
        (fderiv ℝ relativeField z.val (direction v z.val))) at he
    rw [determinant_trace_derivative _ _ hn] at he
    change _=(sourceJacobian*|(relativeField z.val).det|)*relativeGaugeTrace v z.val
    rw [abs_of_neg hneg,he]
    simp only [relativeGaugeTrace]
    ring

private theorem complex_jacobian_current (v : Ambient) (z : physicalChart) :
    fderiv ℝ complexJacobian z.val (direction v z.val)=complexJacobian z.val*(relativeGaugeTrace v z.val : ℂ) := by
  have hR := ((real_jacobian_smooth z).differentiableAt (by simp)).hasFDerivAt
  have hC : HasFDerivAt Complex.ofRealCLM Complex.ofRealCLM (realJacobian z.val) := Complex.ofRealCLM.hasFDerivAt
  have he := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L (direction v z.val)) (hC.comp z.val hR).fderiv
  change fderiv ℝ complexJacobian z.val (direction v z.val)=
    (fderiv ℝ realJacobian z.val (direction v z.val) : ℂ) at he
  rw [real_jacobian_current,Complex.ofReal_mul] at he
  exact he

/-- Both terms of the original density current are now traces of the same source inverse geometry. -/
theorem original_density_two_traces (N : ℕ) (v : Ambient) (z : physicalChart) :
    divergenceCoefficient N v z.val=
      ((LinearMap.trace ℝ SourceCoordinateSlice (sourceDirectionalJacobian v z.val).toLinearMap+
        relativeGaugeTrace v z.val : ℝ) : ℂ) := by
  rw [original_density_inverse_trace,complex_jacobian_current,Complex.ofReal_add]
  field_simp [jacobian_ne z]

open GaussInverseSecond SourceQuantumResidualGaugeSlice
open SaturationMonoid.PhysicsCore StageNineHolonomicField StageNineCoframeGravityGaugeRegularity
open StageNineP286GaugeConnectionVariationDensity StageNineP286LinkedActiveGaugeBFAlgebra
open scoped InnerProductSpace

private theorem trace_skew {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] E)
    (hA : ∀ x y,inner ℝ (A x) y+inner ℝ x (A y)=0) : LinearMap.trace ℝ E A=0 := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  change (∑ i,LinearMap.toMatrix b.toBasis b.toBasis A i i)=0
  apply Finset.sum_eq_zero
  intro i _
  simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.repr_apply_apply]
  have h := hA (b i) (b i)
  rw [real_inner_comm (b i) (A (b i))] at h
  linarith

private theorem scalar_action_trace (a : NativeLie) :
    LinearMap.trace ℝ Scalar (scalarP286ActionBilinear a)=0 := by
  apply trace_skew
  intro x y
  have h := StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm a)) x y
  rw [original_scalar_pairing,original_scalar_pairing] at h
  exact h

private theorem gauge_action_trace (a : NativeLie) : LinearMap.trace ℝ Gauge (nativeGauge a)=0 := by
  apply trace_skew
  intro x y
  change (∑ i : Fin 3,inner ℝ (show NativeLie from jointP286CoordinateLieBracket a (gaugeCoordinates x i)) (gaugeCoordinates y i))+
    (∑ i : Fin 3,inner ℝ (gaugeCoordinates x i) (show NativeLie from jointP286CoordinateLieBracket a (gaugeCoordinates y i)))=0
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  exact p286CoordinateLiePairing_adjoint_skew a (gaugeCoordinates x i) (gaugeCoordinates y i)

private theorem ambient_action_trace (a : NativeLie) : LinearMap.trace ℝ Ambient (ambientAction a)=0 := by
  rw [ambientAction,LinearMap.trace_prodMap',scalar_action_trace,gauge_action_trace,add_zero]

def inverseLie (z : SourceCoordinateSlice) : Ambient →ₗ[ℝ] NativeLie :=
  (LinearMap.fst ℝ NativeLie Slice).comp (inverseL z).toLinearMap

def inverseSlice (z : SourceCoordinateSlice) : Ambient →ₗ[ℝ] Slice :=
  (LinearMap.snd ℝ NativeLie Slice).comp (inverseL z).toLinearMap

def sliceResponse (v : Ambient) (z : SourceCoordinateSlice) : Slice →ₗ[ℝ] Slice :=
  (inverseSlice z).comp ((ambientAction (inverseL z v).1).comp sliceMap)

private theorem directional_trace_slice (v : Ambient) (z : physicalChart) :
    LinearMap.trace ℝ SourceCoordinateSlice (sourceDirectionalJacobian v z.val).toLinearMap=
      -LinearMap.trace ℝ Slice (sliceResponse v z.val) := by
  let E : Slice →ₗ[ℝ] SourceCoordinateSlice := LinearMap.inr ℝ Coframe Slice
  let P : SourceCoordinateSlice →ₗ[ℝ] Slice := LinearMap.snd ℝ Coframe Slice
  have he : (sourceDirectionalJacobian v z.val).toLinearMap=
      -((E.comp (sliceResponse v z.val)).comp P) := by
    apply LinearMap.ext
    intro h
    change -(0,(inverseL z.val (variationL h (inverseL z.val v))).2)=
      -(0,(inverseL z.val (ambientAction (inverseL z.val v).1 (sliceMap h.2))).2)
    rfl
  rw [he,map_neg]
  congr 1
  rw [LinearMap.trace_comp_comm' (R := ℝ) (M := SourceCoordinateSlice) (N := Slice) P (E.comp (sliceResponse v z.val))]
  congr 1

private theorem split_trace (T : Split →ₗ[ℝ] Split) :
    LinearMap.trace ℝ Split T=
      LinearMap.trace ℝ NativeLie ((LinearMap.fst ℝ NativeLie Slice).comp (T.comp (LinearMap.inl ℝ NativeLie Slice)))+
      LinearMap.trace ℝ Slice ((LinearMap.snd ℝ NativeLie Slice).comp (T.comp (LinearMap.inr ℝ NativeLie Slice))) := by
  have he : T=(T.comp (LinearMap.inl ℝ NativeLie Slice)).comp (LinearMap.fst ℝ NativeLie Slice)+
      (T.comp (LinearMap.inr ℝ NativeLie Slice)).comp (LinearMap.snd ℝ NativeLie Slice) := by
    apply LinearMap.ext
    intro x
    change T x=T (x.1,0)+T (0,x.2)
    rw [←map_add]
    congr 1
    exact Prod.ext (by simp) (by simp)
  calc
    _ = LinearMap.trace ℝ Split ((T.comp (LinearMap.inl ℝ NativeLie Slice)).comp (LinearMap.fst ℝ NativeLie Slice)+
        (T.comp (LinearMap.inr ℝ NativeLie Slice)).comp (LinearMap.snd ℝ NativeLie Slice)) := congrArg (LinearMap.trace ℝ Split) he
    _ = _ := by
      rw [map_add]
      exact congrArg₂ (fun x y : ℝ => x+y)
        (LinearMap.trace_comp_comm' (R := ℝ) (M := Split) (N := NativeLie) _ _) (LinearMap.trace_comp_comm' (R := ℝ) (M := Split) (N := Slice) _ _)

def orbitResponse (v : Ambient) (z : SourceCoordinateSlice) : NativeLie →ₗ[ℝ] NativeLie :=
  (inverseLie z).comp ((ambientAction (inverseL z v).1).comp (orbitMap z))

private theorem directional_trace_orbit (v : Ambient) (z : physicalChart) :
    LinearMap.trace ℝ SourceCoordinateSlice (sourceDirectionalJacobian v z.val).toLinearMap=
      LinearMap.trace ℝ NativeLie (orbitResponse v z.val) := by
  let T : Split →ₗ[ℝ] Split := (inverseL z.val).toLinearMap.comp ((ambientAction (inverseL z.val v).1).comp (splitMap z.val))
  have hz : LinearMap.trace ℝ Split T=0 := by
    change LinearMap.trace ℝ Split (((inverseL z.val).toLinearMap.comp (ambientAction (inverseL z.val v).1)).comp (splitMap z.val))=0
    rw [LinearMap.trace_comp_comm' (R := ℝ) (M := Split) (N := Ambient) (splitMap z.val) ((inverseL z.val).toLinearMap.comp (ambientAction (inverseL z.val v).1))]
    have he : (splitMap z.val).comp ((inverseL z.val).toLinearMap.comp (ambientAction (inverseL z.val v).1))=
        ambientAction (inverseL z.val v).1 := by
      apply LinearMap.ext
      intro x
      exact inverse_right z _
    rw [he,ambient_action_trace]
  have ht := split_trace T
  have ho : (LinearMap.fst ℝ NativeLie Slice).comp (T.comp (LinearMap.inl ℝ NativeLie Slice))=orbitResponse v z.val := by
    apply LinearMap.ext
    intro b
    have hb : splitMap z.val (b,0)=orbitMap z.val b := by simp [splitMap,sliceMap]
    change inverseLie z.val (ambientAction (inverseL z.val v).1 (splitMap z.val (b,0)))=
      inverseLie z.val (ambientAction (inverseL z.val v).1 (orbitMap z.val b))
    rw [hb]
  have hs : (LinearMap.snd ℝ NativeLie Slice).comp (T.comp (LinearMap.inr ℝ NativeLie Slice))=sliceResponse v z.val := by
    apply LinearMap.ext
    intro t
    have hb : splitMap z.val (0,t)=sliceMap t := by simp [splitMap,sliceMap]
    change inverseSlice z.val (ambientAction (inverseL z.val v).1 (splitMap z.val (0,t)))=
      inverseSlice z.val (ambientAction (inverseL z.val v).1 (sliceMap t))
    rw [hb]
  rw [ho,hs] at ht
  rw [directional_trace_slice]
  linarith

def nativeRead (v : Ambient) : NativeLie →ₗ[ℝ] Ambient :=
  (SourceQuantumScalarChart.action v.1).prod (nativeGauge.flip v.2)

def sourceLieResponse (v : Ambient) (z : SourceCoordinateSlice) : NativeLie →ₗ[ℝ] NativeLie :=
  (inverseLie z).comp (nativeRead v)

private theorem native_read_add (v w : Ambient) : nativeRead (v+w)=nativeRead v+nativeRead w := by
  apply LinearMap.ext
  intro a
  apply Prod.ext
  · exact map_add (scalarP286ActionBilinear a) v.1 w.1
  · exact map_add (nativeGauge a) v.2 w.2

private theorem inverse_lie_orbit (z : physicalChart) (a : NativeLie) : inverseLie z.val (orbitMap z.val a)=a := by
  have he : orbitMap z.val a=splitMap z.val (a,0) := by simp [splitMap,sliceMap]
  change (inverseL z.val (orbitMap z.val a)).1=a
  rw [he,inverse_left]

private theorem native_ad_trace (a : NativeLie) : LinearMap.trace ℝ NativeLie (SourceCartanCubic.nativeBracket a)=0 := by
  apply trace_skew
  intro b c
  exact p286CoordinateLiePairing_adjoint_skew a b c

private theorem orbit_response_split (v : Ambient) (z : physicalChart) :
    orbitResponse v z.val=SourceCartanCubic.nativeBracket (inverseL z.val v).1+
      sourceLieResponse (orbitMap z.val (inverseL z.val v).1) z.val := by
  apply LinearMap.ext
  intro b
  let a := (inverseL z.val v).1
  have he : ambientAction a (orbitMap z.val b)=
      orbitMap z.val (GaussInverseSecond.nativeBracket a b)+nativeRead (orbitMap z.val a) b := by
    change ambientAction a (orbitMap z.val b)=
      orbitMap z.val (GaussInverseSecond.nativeBracket a b)+ambientAction b (orbitMap z.val a)
    rw [orbit_is_action,orbit_is_action,orbit_is_action,ambient_bracket]
    module
  change inverseLie z.val (ambientAction a (orbitMap z.val b))=
    SourceCartanCubic.nativeBracket a b+inverseLie z.val (nativeRead (orbitMap z.val a) b)
  rw [he,map_add,inverse_lie_orbit]
  rfl

private theorem directional_trace_source (v : Ambient) (z : physicalChart) :
    LinearMap.trace ℝ SourceCoordinateSlice (sourceDirectionalJacobian v z.val).toLinearMap=
      LinearMap.trace ℝ NativeLie (sourceLieResponse (orbitMap z.val (inverseL z.val v).1) z.val) := by
  rw [directional_trace_orbit,orbit_response_split,map_add,native_ad_trace,zero_add]

private theorem source_response_decomposition (v : Ambient) (z : physicalChart) :
    sourceLieResponse v z.val=
      sourceLieResponse (orbitMap z.val (inverseL z.val v).1) z.val+
      sourceLieResponse (sliceMap (inverseL z.val v).2) z.val := by
  have hv : v=orbitMap z.val (inverseL z.val v).1+sliceMap (inverseL z.val v).2 := (inverse_right z v).symm
  have h := congrArg (fun x => sourceLieResponse x z.val) hv
  simpa only [sourceLieResponse,native_read_add,LinearMap.comp_add] using h

private theorem density_source_trace (N : ℕ) (v : Ambient) (z : physicalChart) :
    divergenceCoefficient N v z.val=
      ((LinearMap.trace ℝ NativeLie (sourceLieResponse v z.val)-
        LinearMap.trace ℝ NativeLie (sourceLieResponse (sliceMap (inverseL z.val v).2) z.val)+
          relativeGaugeTrace v z.val : ℝ) : ℂ) := by
  rw [original_density_two_traces,directional_trace_source]
  have h := congrArg (LinearMap.trace ℝ NativeLie) (source_response_decomposition v z)
  rw [map_add] at h
  congr 1
  linarith

open SourceNativeMixedCurvatureReduction SourceQuantumResidualFlow SourceBrokenGaussCurvatureCurrent

private theorem inverse_slice (z : physicalChart) (t : Slice) : inverseL z.val (sliceMap t)=(0,t) := by
  have hs : sliceMap t=splitMap z.val (0,t) := by simp [splitMap,sliceMap]
  rw [hs,inverse_left]

private theorem inverse_broken (z : physicalChart) (v : Ambient) :
    broken.orthogonalProjectionOnto (inverseLie z.val v)=normalLift z v.1 := by
  let a := inverseLie z.val v
  let h := stabilizer.orthogonalProjectionOnto a
  let b := broken.orthogonalProjectionOnto a
  have hab : (h : NativeLie)+(b : NativeLie)=a := stabilizer.starProjection_add_starProjection_orthogonal a
  have hs := congrArg Prod.fst (inverse_right z v)
  change SourceQuantumScalarChart.action (vacuum+(z.val.2.1 : Scalar)) a+((inverseL z.val v).2.1 : Scalar)=v.1 at hs
  have hn := congrArg sourceNormal hs
  rw [map_add,sourceNormal_slice,add_zero,←hab,map_add,map_add,sourceNormal_stabilizer,zero_add] at hn
  have ht := chartConsistency_right_inverse ⟨z.val.2.1,z.property.2.2.2.1⟩ (sourceNormal v.1)
  apply (chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩).injective
  change sourceNormal (SourceQuantumScalarChart.action (vacuum+(z.val.2.1 : Scalar)) b)=
    sourceNormal (SourceQuantumScalarChart.action (vacuum+(z.val.2.1 : Scalar)) (normalLift z v.1))
  exact hn.trans ht.symm

private theorem native_trace_split (T : NativeLie →ₗ[ℝ] NativeLie) :
    LinearMap.trace ℝ NativeLie T=
      LinearMap.trace ℝ stabilizer (stabilizer.orthogonalProjectionOnto.toLinearMap.comp (T.comp stabilizer.subtype))+
      LinearMap.trace ℝ broken (broken.orthogonalProjectionOnto.toLinearMap.comp (T.comp broken.subtype)) := by
  have he : T=(T.comp stabilizer.subtype).comp stabilizer.orthogonalProjectionOnto.toLinearMap+
      (T.comp broken.subtype).comp broken.orthogonalProjectionOnto.toLinearMap := by
    apply LinearMap.ext
    intro a
    change T a=T (stabilizer.orthogonalProjectionOnto a)+T (broken.orthogonalProjectionOnto a)
    rw [←map_add]
    exact congrArg T (stabilizer.starProjection_add_starProjection_orthogonal a).symm
  calc
    _ = LinearMap.trace ℝ NativeLie ((T.comp stabilizer.subtype).comp stabilizer.orthogonalProjectionOnto.toLinearMap+
        (T.comp broken.subtype).comp broken.orthogonalProjectionOnto.toLinearMap) := congrArg (LinearMap.trace ℝ NativeLie) he
    _ = _ := by
      rw [map_add]
      exact congrArg₂ (fun x y : ℝ => x+y)
        (LinearMap.trace_comp_comm' (R := ℝ) (M := NativeLie) (N := stabilizer) _ _)
        (LinearMap.trace_comp_comm' (R := ℝ) (M := NativeLie) (N := broken) _ _)

def residualSliceResponse (t : Slice) (z : SourceCoordinateSlice) : stabilizer →ₗ[ℝ] stabilizer :=
  (LinearMap.fst ℝ stabilizer coordinateSlice).comp
    ((residualInverse z).toLinearMap.comp (gaugeAction.flip (t.2 : Gauge)))

def brokenSliceResponse (t : Slice) (z : physicalChart) : broken →ₗ[ℝ] broken :=
  (chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩).symm.toLinearMap.comp
    (sourceNormal.comp ((SourceQuantumScalarChart.action (t.1 : Scalar)).comp broken.subtype))

private theorem residual_slice_block (t : Slice) (z : physicalChart) :
    stabilizer.orthogonalProjectionOnto.toLinearMap.comp ((sourceLieResponse (sliceMap t) z.val).comp stabilizer.subtype)=
      residualSliceResponse t z.val := by
  apply LinearMap.ext
  intro h
  have hv : nativeRead (sliceMap t) (h : NativeLie)=
      sliceMap (scalarAction h t.1,0)+(0,gaugeAction h (t.2 : Gauge)) := by
    apply Prod.ext
    · change scalarP286ActionBilinear (h : NativeLie) (t.1 : Scalar)=(scalarAction h t.1 : Scalar)+0
      rw [add_zero]
      rfl
    · change nativeGauge (h : NativeLie) (t.2 : Gauge)=(0 : Gauge)+gaugeAction h (t.2 : Gauge)
      rw [zero_add]
      rfl
  have hi : inverseLie z.val (nativeRead (sliceMap t) (h : NativeLie))=
      ((residualInverse z.val (gaugeAction h (t.2 : Gauge))).1 : NativeLie) := by
    change (inverseL z.val (nativeRead (sliceMap t) (h : NativeLie))).1=_
    rw [hv,map_add,inverse_slice,original_gauge_inverse]
    simp only [Prod.fst_add,zero_add]
  change stabilizer.orthogonalProjectionOnto (inverseLie z.val (nativeRead (sliceMap t) (h : NativeLie)))=
    (residualInverse z.val (gaugeAction h (t.2 : Gauge))).1
  rw [hi,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

private theorem broken_slice_block (t : Slice) (z : physicalChart) :
    broken.orthogonalProjectionOnto.toLinearMap.comp ((sourceLieResponse (sliceMap t) z.val).comp broken.subtype)=
      brokenSliceResponse t z := by
  apply LinearMap.ext
  intro b
  change broken.orthogonalProjectionOnto (inverseLie z.val (nativeRead (sliceMap t) (b : NativeLie)))=
    normalLift z (scalarP286ActionBilinear (b : NativeLie) (t.1 : Scalar))
  exact inverse_broken z (nativeRead (sliceMap t) (b : NativeLie))

private theorem slice_response_trace (t : Slice) (z : physicalChart) :
    LinearMap.trace ℝ NativeLie (sourceLieResponse (sliceMap t) z.val)=
      LinearMap.trace ℝ stabilizer (residualSliceResponse t z.val)+
      LinearMap.trace ℝ broken (brokenSliceResponse t z) := by
  rw [native_trace_split,residual_slice_block,broken_slice_block]

abbrev ResidualSpace := stabilizer × coordinateSlice

def relativeVariation : Gauge →ₗ[ℝ] Module.End ℝ ResidualSpace where
  toFun w := sourceSplitEquiv.symm.toLinearMap.comp ((gaugeAction.flip w).comp (LinearMap.fst ℝ stabilizer coordinateSlice))
  map_add' v w := by
    apply LinearMap.ext
    intro x
    change sourceSplitEquiv.symm (gaugeAction x.1 (v+w))=
      sourceSplitEquiv.symm (gaugeAction x.1 v)+sourceSplitEquiv.symm (gaugeAction x.1 w)
    rw [map_add,map_add]
  map_smul' c w := by
    apply LinearMap.ext
    intro x
    change sourceSplitEquiv.symm (gaugeAction x.1 (c • w))=c • sourceSplitEquiv.symm (gaugeAction x.1 w)
    rw [map_smul,map_smul]

def residualMatrixVariation : Gauge →ₗ[ℝ] Matrix GaugeMatrixIndex GaugeMatrixIndex ℝ :=
  (LinearMap.toMatrix coordinateBasis coordinateBasis).toLinearMap.comp relativeVariation

private theorem relative_field_affine (z : SourceCoordinateSlice) :
    relativeField z=relativeField 0+residualMatrixVariation (z.2.2 : Gauge) := by
  have hm : relative (z.2.2 : Gauge)=relative (0 : Gauge)+relativeVariation (z.2.2 : Gauge) := by
    apply LinearMap.ext
    intro x
    change sourceSplitEquiv.symm (gaugeAction x.1 (z.2.2 : Gauge)+(x.2 : Gauge))=
      sourceSplitEquiv.symm (gaugeAction x.1 (0 : Gauge)+(x.2 : Gauge))+
        sourceSplitEquiv.symm (gaugeAction x.1 (z.2.2 : Gauge))
    rw [map_zero,zero_add,map_add]
    abel
  have h := congrArg (LinearMap.toMatrix coordinateBasis coordinateBasis) hm
  simpa only [relativeField,relativeMatrix,residualMatrixVariation,LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap,map_add,Prod.snd_zero,Submodule.coe_zero] using h

private theorem relative_field_derivative (v : Ambient) (z : SourceCoordinateSlice) :
    fderiv ℝ relativeField z (direction v z)=residualMatrixVariation ((inverseL z v).2.2 : Gauge) := by
  let G : SourceCoordinateSlice →L[ℝ] Gauge := coordinateSlice.subtypeL.comp
    ((ContinuousLinearMap.snd ℝ scalarSlice coordinateSlice).comp (ContinuousLinearMap.snd ℝ Coframe Slice))
  let D : SourceCoordinateSlice →L[ℝ] Matrix GaugeMatrixIndex GaugeMatrixIndex ℝ := residualMatrixVariation.toContinuousLinearMap.comp G
  have hD : HasFDerivAt (fun x => D x) D z := D.hasFDerivAt
  have hf : HasFDerivAt (fun x => relativeField 0+D x) D z :=
    (hasFDerivAt_const_add_iff (𝕜 := ℝ) (E := SourceCoordinateSlice)
      (F := Matrix GaugeMatrixIndex GaugeMatrixIndex ℝ) (f := fun x => D x) (f' := D) (x := z) (relativeField 0)).mpr hD
  have he : relativeField=(fun x => relativeField 0+D x) := funext relative_field_affine
  rw [he,hf.fderiv]
  rfl

private theorem residual_inverse_equiv (z : physicalChart) :
    residualInverse z.val=(residualEquiv z).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  have hc : (combined (z.val.2.2 : Gauge)).toContinuousLinearMap=
      (residualEquiv z).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact (residualEquiv_apply z x).symm
  unfold residualInverse
  rw [hc]
  exact ContinuousLinearMap.inverse_equiv (residualEquiv z).toContinuousLinearEquiv

def relativeInverse (z : physicalChart) : Module.End ℝ ResidualSpace :=
  (residualInverse z.val).toLinearMap.comp sourceSplitEquiv.toLinearMap

private theorem relative_inverse_left (z : physicalChart) :
    relativeInverse z*(relative (z.val.2.2 : Gauge))=1 := by
  apply LinearMap.ext
  intro x
  change residualInverse z.val (sourceSplitEquiv (sourceSplitEquiv.symm (combined (z.val.2.2 : Gauge) x)))=x
  rw [sourceSplitEquiv.apply_symm_apply,residual_inverse_equiv]
  have hc : combined (z.val.2.2 : Gauge) x=residualEquiv z x := (residualEquiv_apply z x).symm
  rw [hc]
  exact (residualEquiv z).symm_apply_apply x

private theorem relative_matrix_inverse (z : physicalChart) :
    LinearMap.toMatrix coordinateBasis coordinateBasis (relativeInverse z)=(relativeField z.val)⁻¹ := by
  have hm : LinearMap.toMatrix coordinateBasis coordinateBasis (relativeInverse z)*relativeField z.val=1 := by
    change LinearMap.toMatrix coordinateBasis coordinateBasis (relativeInverse z)*
      LinearMap.toMatrix coordinateBasis coordinateBasis (relative (z.val.2.2 : Gauge))=1
    rw [←LinearMap.toMatrix_mul,relative_inverse_left,LinearMap.toMatrix_one]
  have hn : (relativeField z.val).det≠0 := by
    simpa only [relativeField,relativeMatrix,LinearMap.det_toMatrix] using residual_relative_det z
  have h := congrArg (fun A => A*(relativeField z.val)⁻¹) hm
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn),Matrix.mul_one,Matrix.one_mul] at h
  exact h

private theorem relative_gauge_trace_residual (v : Ambient) (z : physicalChart) :
    relativeGaugeTrace v z.val=LinearMap.trace ℝ stabilizer (residualSliceResponse (inverseL z.val v).2 z.val) := by
  rw [relativeGaugeTrace,relative_field_derivative,←relative_matrix_inverse]
  change Matrix.trace (LinearMap.toMatrix coordinateBasis coordinateBasis (relativeVariation ((inverseL z.val v).2.2 : Gauge))*
    LinearMap.toMatrix coordinateBasis coordinateBasis (relativeInverse z))=_
  rw [Matrix.trace_mul_comm,←LinearMap.toMatrix_mul,←LinearMap.trace_eq_matrix_trace ℝ coordinateBasis]
  have he : relativeInverse z*relativeVariation ((inverseL z.val v).2.2 : Gauge)=
      ((residualInverse z.val).toLinearMap.comp (gaugeAction.flip ((inverseL z.val v).2.2 : Gauge))).comp
        (LinearMap.fst ℝ stabilizer coordinateSlice) := by
    apply LinearMap.ext
    intro x
    change residualInverse z.val (sourceSplitEquiv (sourceSplitEquiv.symm
      (gaugeAction x.1 ((inverseL z.val v).2.2 : Gauge))))=
      residualInverse z.val (gaugeAction x.1 ((inverseL z.val v).2.2 : Gauge))
    rw [sourceSplitEquiv.apply_symm_apply]
  rw [he,LinearMap.trace_comp_comm']
  rfl

/-- The source residual Jacobian trace cancels its stabilizer block inside the complete density current. -/
theorem original_density_broken_return (N : ℕ) (v : Ambient) (z : physicalChart) :
    divergenceCoefficient N v z.val=
      ((LinearMap.trace ℝ NativeLie (sourceLieResponse v z.val)-
        LinearMap.trace ℝ broken (brokenSliceResponse (inverseL z.val v).2 z) : ℝ) : ℂ) := by
  rw [density_source_trace,slice_response_trace,relative_gauge_trace_residual]
  congr 1
  ring

open SourceQuantumResidualChartFlow

private theorem consistency_neg (phi : Scalar) : consistency (-phi)= -consistency phi := by
  apply LinearMap.ext
  intro b
  change sourceNormal (scalarP286ActionBilinear (b : NativeLie) (-phi))= -sourceNormal (scalarP286ActionBilinear (b : NativeLie) phi)
  rw [map_neg,map_neg]

private theorem broken_gauge_trace (w : Gauge) (z : physicalChart) :
    LinearMap.trace ℝ broken (brokenSliceResponse (inverseL z.val (0,w)).2 z)=0 := by
  let a := (residualInverse z.val w).1
  let E := chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩
  let B := brokenGenerator a
  have hphi : scalarP286ActionBilinear (a : NativeLie) (vacuum+(z.val.2.1 : Scalar))=(scalarAction a z.val.2.1 : Scalar) := by
    rw [map_add,show scalarP286ActionBilinear (a : NativeLie) vacuum=0 from a.property,zero_add]
    rfl
  have hC := consistency_commutator a (vacuum+(z.val.2.1 : Scalar))
  rw [hphi] at hC
  have hn : consistency (-(scalarAction a z.val.2.1 : Scalar))=E.toLinearMap*B-B*E.toLinearMap := by
    rw [consistency_neg,hC]
    change -(B*E.toLinearMap-E.toLinearMap*B)=_
    abel
  have he : brokenSliceResponse (inverseL z.val (0,w)).2 z=B-E.symm.toLinearMap*B*E.toLinearMap := by
    rw [original_gauge_inverse]
    change E.symm.toLinearMap*(consistency (-(scalarAction a z.val.2.1 : Scalar)))=_
    rw [hn,mul_sub]
    have hi : E.symm.toLinearMap*E.toLinearMap=1 := by
      apply LinearMap.ext
      intro b
      exact E.symm_apply_apply b
    rw [←mul_assoc,hi,one_mul]
    rfl
  rw [he,map_sub]
  have hi : E.toLinearMap*E.symm.toLinearMap=1 := by
    apply LinearMap.ext
    intro b
    exact E.apply_symm_apply b
  rw [LinearMap.trace_mul_comm ℝ (E.symm.toLinearMap*B) E.toLinearMap,←mul_assoc,hi,one_mul,sub_self]

/-- The actual gauge direction loses the complete broken-consistency trace through the source commutator. -/
theorem original_gauge_density_trace (N : ℕ) (w : Gauge) (z : physicalChart) :
    divergenceCoefficient N (0,w) z.val=(LinearMap.trace ℝ NativeLie (sourceLieResponse (0,w) z.val) : ℂ) := by
  rw [original_density_broken_return,broken_gauge_trace,sub_zero]

open SourceDoubleGramCurvatureForm GaussNativeForm

abbrev GammaIndex := Fin (Module.finrank ℝ broken)
local instance : NormedAddCommGroup (Matrix GammaIndex GammaIndex ℝ) :=
  inferInstanceAs (NormedAddCommGroup (GammaIndex → GammaIndex → ℝ))
local instance : NormedSpace ℝ (Matrix GammaIndex GammaIndex ℝ) :=
  inferInstanceAs (NormedSpace ℝ (GammaIndex → GammaIndex → ℝ))

def gammaBasis := (stdOrthonormalBasis ℝ broken).toBasis

def gammaVariation : Scalar →ₗ[ℝ] Module.End ℝ broken where
  toFun := consistency
  map_add' x y := by
    apply LinearMap.ext
    intro b
    change sourceNormal (scalarP286ActionBilinear (b : NativeLie) (x+y))=
      sourceNormal (scalarP286ActionBilinear (b : NativeLie) x)+sourceNormal (scalarP286ActionBilinear (b : NativeLie) y)
    rw [map_add,map_add]
  map_smul' c x := by
    apply LinearMap.ext
    intro b
    change sourceNormal (scalarP286ActionBilinear (b : NativeLie) (c • x))=
      c • sourceNormal (scalarP286ActionBilinear (b : NativeLie) x)
    rw [map_smul,map_smul]

def gammaMatrixVariation : Scalar →ₗ[ℝ] Matrix GammaIndex GammaIndex ℝ :=
  (LinearMap.toMatrix gammaBasis gammaBasis).toLinearMap.comp gammaVariation

def gammaField (z : SourceCoordinateSlice) : Matrix GammaIndex GammaIndex ℝ :=
  gammaMatrixVariation (vacuum+(z.2.1 : Scalar))

def gammaLog (z : SourceCoordinateSlice) : ℝ := Real.log (gammaField z).det

def gammaDensity (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  fderiv ℝ gammaLog z (direction v z)

private theorem gamma_field_smooth : ContDiff ℝ ∞ gammaField :=
  gammaMatrixVariation.toContinuousLinearMap.contDiff.comp GaussNativePotential.scalarField_smooth

private theorem gamma_field_derivative (v : Ambient) (z : SourceCoordinateSlice) :
    fderiv ℝ gammaField z (direction v z)=gammaMatrixVariation ((inverseL z v).2.1 : Scalar) := by
  let G : SourceCoordinateSlice →L[ℝ] Scalar := scalarSlice.subtypeL.comp
    ((ContinuousLinearMap.fst ℝ scalarSlice coordinateSlice).comp (ContinuousLinearMap.snd ℝ Coframe Slice))
  let D : SourceCoordinateSlice →L[ℝ] Matrix GammaIndex GammaIndex ℝ := gammaMatrixVariation.toContinuousLinearMap.comp G
  have hD : HasFDerivAt (fun x => D x) D z := D.hasFDerivAt
  have hf : HasFDerivAt (fun x => gammaMatrixVariation vacuum+D x) D z :=
    (hasFDerivAt_const_add_iff (𝕜 := ℝ) (E := SourceCoordinateSlice)
      (F := Matrix GammaIndex GammaIndex ℝ) (f := fun x => D x) (f' := D) (x := z) (gammaMatrixVariation vacuum)).mpr hD
  have he : gammaField=(fun x => gammaMatrixVariation vacuum+D x) := by
    funext x
    exact map_add gammaMatrixVariation vacuum (x.2.1 : Scalar)
  rw [he,hf.fderiv]
  rfl

private theorem gamma_det_ne (z : physicalChart) : (gammaField z.val).det≠0 := by
  change (LinearMap.toMatrix gammaBasis gammaBasis (consistency (vacuum+(z.val.2.1 : Scalar)))).det≠0
  rw [LinearMap.det_toMatrix]
  exact z.property.2.2.2.1

private theorem gamma_log_smooth (z : physicalChart) : ContDiffAt ℝ ∞ gammaLog z.val := by
  let D : ContinuousMultilinearMap ℝ (fun _ : GammaIndex => GammaIndex → ℝ) ℝ :=
    { toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
      cont := continuous_id.matrix_det }
  exact ((D.contDiff.comp gamma_field_smooth).contDiffAt).log (gamma_det_ne z)

private theorem gamma_matrix_inverse (z : physicalChart) :
    LinearMap.toMatrix gammaBasis gammaBasis (chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩).symm.toLinearMap=
      (gammaField z.val)⁻¹ := by
  let E := chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩
  have hm : LinearMap.toMatrix gammaBasis gammaBasis E.symm.toLinearMap*gammaField z.val=1 := by
    change LinearMap.toMatrix gammaBasis gammaBasis E.symm.toLinearMap*LinearMap.toMatrix gammaBasis gammaBasis E.toLinearMap=1
    rw [←LinearMap.toMatrix_mul]
    have hi : E.symm.toLinearMap*E.toLinearMap=1 := by
      apply LinearMap.ext
      intro b
      exact E.symm_apply_apply b
    rw [hi,LinearMap.toMatrix_one]
  have h := congrArg (fun A => A*(gammaField z.val)⁻¹) hm
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (gamma_det_ne z)),Matrix.mul_one,Matrix.one_mul] at h
  exact h

private theorem gamma_density_source (v : Ambient) (z : physicalChart) :
    gammaDensity v z.val=LinearMap.trace ℝ broken (brokenSliceResponse (inverseL z.val v).2 z) := by
  have hR := (gamma_field_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have hD := (determinant_differentiable (gammaField z.val)).hasFDerivAt.comp z.val hR
  have hL := hD.log (gamma_det_ne z)
  have he := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℝ => L (direction v z.val)) hL.fderiv
  change gammaDensity v z.val=(gammaField z.val).det⁻¹*
    fderiv ℝ (fun M : Matrix GammaIndex GammaIndex ℝ => M.det) (gammaField z.val)
      (fderiv ℝ gammaField z.val (direction v z.val)) at he
  rw [determinant_trace_derivative _ _ (gamma_det_ne z),←mul_assoc,inv_mul_cancel₀ (gamma_det_ne z),one_mul] at he
  rw [he,gamma_field_derivative,←gamma_matrix_inverse]
  change Matrix.trace (LinearMap.toMatrix gammaBasis gammaBasis (consistency ((inverseL z.val v).2.1 : Scalar))*
    LinearMap.toMatrix gammaBasis gammaBasis (chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩).symm.toLinearMap)=_
  rw [Matrix.trace_mul_comm,←LinearMap.toMatrix_mul,←LinearMap.trace_eq_matrix_trace ℝ gammaBasis]
  rfl

private theorem gamma_density_smooth (v : Ambient) (z : physicalChart) : ContDiffAt ℝ ∞ (gammaDensity v) z.val :=
  ((gamma_log_smooth z).fderiv_right (by simp)).clm_apply (direction_smooth v z)

private theorem gamma_gauge_zero (w : Gauge) (z : physicalChart) : gammaDensity (0,w) z.val=0 := by
  rw [gamma_density_source,broken_gauge_trace]

/-- The density remainder is the actual directional derivative of the broken log determinant. -/
theorem original_density_gamma_return (N : ℕ) (v : Ambient) (z : physicalChart) :
    divergenceCoefficient N v z.val=
      ((LinearMap.trace ℝ NativeLie (sourceLieResponse v z.val)-gammaDensity v z.val : ℝ) : ℂ) := by
  rw [original_density_broken_return,gamma_density_source]

private theorem source_direction_curvature (z : physicalChart) (u v : Ambient) :
    VectorField.lieBracket ℝ (direction u) (direction v) z.val=direction (nativeCurvature u v z.val) z.val := by
  rw [VectorField.lieBracket,direction_derivative,direction_derivative]
  have h := congrArg Prod.snd (original_inverse_curvature z u v)
  simp only [Prod.snd_sub,sub_zero] at h
  apply Prod.ext
  · exact sub_self _
  · exact h

def gammaRead (z : SourceCoordinateSlice) : Ambient →ₗ[ℝ] ℝ :=
  (fderiv ℝ gammaLog z).toLinearMap.comp ((LinearMap.inr ℝ Coframe Slice).comp
    ((LinearMap.snd ℝ NativeLie Slice).comp (inverseL z).toLinearMap))

private theorem gamma_scalar_rotation (u : Ambient) (s : ScalarIndex) (z : SourceCoordinateSlice) :
    gammaRead z (scalarP286ActionBilinear (inverseL z u).1 (scalarBasis s),0)=
      ∑ r : ScalarIndex,scalarRotation u r s z*gammaDensity (scalarDirection r) z := by
  have he : (scalarP286ActionBilinear (inverseL z u).1 (scalarBasis s),(0 : Gauge))=
      ∑ r : ScalarIndex,scalarRotation u r s z • scalarDirection r := by
    apply Prod.ext
    · simpa only [Prod.fst_sum,Prod.smul_fst,scalarDirection,scalarRotation] using
        (scalarBasis.sum_repr' (scalarP286ActionBilinear (inverseL z u).1 (scalarBasis s))).symm
    · simp only [Prod.snd_sum,Prod.smul_snd,scalarDirection,smul_zero,Finset.sum_const_zero]
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul,smul_eq_mul]
  rfl

private theorem scalar_rotation_skew (u : Ambient) (r s : ScalarIndex) (z : SourceCoordinateSlice) :
    scalarRotation u r s z= -scalarRotation u s r z := by
  have h := StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm (inverseL z u).1)) (scalarBasis s) (scalarBasis r)
  rw [original_scalar_pairing,original_scalar_pairing] at h
  change inner ℝ (scalarP286ActionBilinear (inverseL z u).1 (scalarBasis s)) (scalarBasis r)+
    inner ℝ (scalarBasis s) (scalarP286ActionBilinear (inverseL z u).1 (scalarBasis r))=0 at h
  rw [real_inner_comm (scalarBasis r) (scalarP286ActionBilinear (inverseL z u).1 (scalarBasis s))] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The broken log-determinant gradient transforms by the same actual scalar rotation. -/
theorem original_gamma_covariance (j : Fin 3) (a : LieIndex) (s : ScalarIndex) (z : physicalChart) :
    fderiv ℝ (gammaDensity (scalarDirection s)) z.val (direction (gaugeDirection j a) z.val)=
      -∑ r : ScalarIndex,scalarRotation (gaugeDirection j a) s r z.val*gammaDensity (scalarDirection r) z.val := by
  have hz : fderiv ℝ (gammaDensity (gaugeDirection j a)) z.val=0 := by
    have he : gammaDensity (gaugeDirection j a)=ᶠ[nhds z.val] (fun _ => (0 : ℝ)) := by
      filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
      exact gamma_gauge_zero (gaugeDirection j a).2 ⟨x,hx⟩
    rw [he.fderiv_eq,(hasFDerivAt_const (0 : ℝ) z.val).fderiv]
  have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := gammaLog)
    (V := direction (gaugeDirection j a)) (W := direction (scalarDirection s)) (x := z.val)
    (gamma_log_smooth z) (by simp only [minSmoothness_of_isRCLikeNormedField];exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    ((direction_smooth (scalarDirection s) z).differentiableAt (by simp))
    ((direction_smooth (gaugeDirection j a) z).differentiableAt (by simp))
  rw [source_direction_curvature] at h
  change gammaRead z.val (nativeCurvature (gaugeDirection j a) (scalarDirection s) z.val)=
    fderiv ℝ (gammaDensity (scalarDirection s)) z.val (direction (gaugeDirection j a) z.val)-
      fderiv ℝ (gammaDensity (gaugeDirection j a)) z.val (direction (scalarDirection s) z.val) at h
  rw [hz,zero_apply,sub_zero] at h
  have he : nativeCurvature (gaugeDirection j a) (scalarDirection s) z.val=
      (scalarP286ActionBilinear (inverseL z.val (gaugeDirection j a)).1 (scalarBasis s),0)-
        (0,nativeGauge (inverseL z.val (scalarDirection s)).1 (gaugeDirection j a).2) := by
    simp only [nativeCurvature,ambientAction,LinearMap.prodMap_apply,scalarDirection,gaugeDirection,map_zero]
  rw [←h,he,map_sub,gamma_scalar_rotation]
  have hg : gammaRead z.val (0,nativeGauge (inverseL z.val (scalarDirection s)).1 (gaugeDirection j a).2)=0 :=
    gamma_gauge_zero _ z
  rw [hg,sub_zero,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [scalar_rotation_skew,neg_mul]

def intrinsicDensity (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  LinearMap.trace ℝ NativeLie (sourceLieResponse v z)

private theorem density_coefficient_smooth (N : ℕ) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (divergenceCoefficient N v) z.val := by
  apply ContDiffAt.sum
  intro i _
  exact (inverseDensity_smooth N z).mul
    ((((complexDensity_smooth N z).mul (coefficient_smooth v i z)).fderiv_right (by simp)).clm_apply contDiffAt_const)

private theorem intrinsic_density_smooth (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (intrinsicDensity v) z.val := by
  have he : intrinsicDensity v=ᶠ[nhds z.val] (fun x => (divergenceCoefficient 0 v x).re+gammaDensity v x) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    have h := congrArg Complex.re (original_density_gamma_return 0 v ⟨x,hx⟩)
    simp only [Complex.ofReal_re] at h
    change (divergenceCoefficient 0 v x).re=intrinsicDensity v x-gammaDensity v x at h
    linarith
  have hr : ContDiffAt ℝ ∞ (fun x => (divergenceCoefficient 0 v x).re) z.val :=
    Complex.reCLM.contDiff.contDiffAt.comp z.val (density_coefficient_smooth 0 v z)
  exact (hr.add (gamma_density_smooth v z)).congr_of_eventuallyEq he

private theorem ofReal_derivative (f : SourceCoordinateSlice → ℝ) (z : SourceCoordinateSlice)
    (hf : DifferentiableAt ℝ f z) (h : SourceCoordinateSlice) :
    fderiv ℝ (fun x => (f x : ℂ)) z h=(fderiv ℝ f z h : ℂ) := by
  have hC : HasFDerivAt Complex.ofRealCLM Complex.ofRealCLM (f z) := Complex.ofRealCLM.hasFDerivAt
  exact congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L h) (hC.comp z hf.hasFDerivAt).fderiv

private theorem density_derivative_source (N : ℕ) (v : Ambient) (z : physicalChart) (h : SourceCoordinateSlice) :
    fderiv ℝ (divergenceCoefficient N v) z.val h=
      ((fderiv ℝ (intrinsicDensity v) z.val h-fderiv ℝ (gammaDensity v) z.val h : ℝ) : ℂ) := by
  have he : divergenceCoefficient N v=ᶠ[nhds z.val]
      (fun x => (intrinsicDensity v x : ℂ)-(gammaDensity v x : ℂ)) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    simpa only [intrinsicDensity,Complex.ofReal_sub] using original_density_gamma_return N v ⟨x,hx⟩
  have hi := ((intrinsic_density_smooth v z).differentiableAt (by simp))
  have hg := ((gamma_density_smooth v z).differentiableAt (by simp))
  have hiC : DifferentiableAt ℝ (fun x => (intrinsicDensity v x : ℂ)) z.val :=
    Complex.ofRealCLM.differentiableAt.comp z.val hi
  have hgC : DifferentiableAt ℝ (fun x => (gammaDensity v x : ℂ)) z.val :=
    Complex.ofRealCLM.differentiableAt.comp z.val hg
  rw [he.fderiv_eq,fderiv_fun_sub hiC hgC]
  simp only [sub_apply,ofReal_derivative _ _ hi,ofReal_derivative _ _ hg,Complex.ofReal_sub]


open SourceJointScalarGaugeCoefficientForm

/-- The remaining coefficient uses only the intrinsic inverse-source trace. -/
def intrinsicJointCoefficient (j : Fin 3) (a : LieIndex) (s : ScalarIndex) (z : SourceCoordinateSlice) : ℝ :=
  (∑ r : ScalarIndex,(
    fderiv ℝ (scalarRotation (gaugeDirection j a) s r) z (direction (scalarDirection r) z)+
      intrinsicDensity (scalarDirection r) z*scalarRotation (gaugeDirection j a) s r z-
      ∑ b : LieIndex,gaugeRotation r b a z*scalarRotation (gaugeDirection j b) s r z))+
  fderiv ℝ (intrinsicDensity (scalarDirection s)) z (direction (gaugeDirection j a) z)

/-- All Number, volume and broken-determinant density corrections cancel in the complete joint row. -/
theorem original_joint_density_cancellation (N : ℕ) (j : Fin 3) (a : LieIndex) (s : ScalarIndex) (z : physicalChart) :
    jointCoefficient N j a s z.val=(intrinsicJointCoefficient j a s z.val : ℂ) := by
  have hd (r : ScalarIndex) : divergenceCoefficient N (scalarDirection r) z.val=
      ((intrinsicDensity (scalarDirection r) z.val-gammaDensity (scalarDirection r) z.val : ℝ) : ℂ) :=
    original_density_gamma_return N (scalarDirection r) z
  have hc : (∑ r : ScalarIndex,(gammaDensity (scalarDirection r) z.val : ℂ)*
      (scalarRotation (gaugeDirection j a) s r z.val : ℂ))=
    ∑ r : ScalarIndex,(scalarRotation (gaugeDirection j a) s r z.val : ℂ)*
      (gammaDensity (scalarDirection r) z.val : ℂ) := by
    apply Finset.sum_congr rfl
    intro r _
    ring
  unfold jointCoefficient intrinsicJointCoefficient
  rw [density_derivative_source,original_gamma_covariance]
  simp_rw [hd]
  simp only [Complex.ofReal_sub,Complex.ofReal_neg,Complex.ofReal_add,Complex.ofReal_sum,Complex.ofReal_mul,
    sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [hc]
  ring

/-- The actual weighted Fock row consumes the density cancellation at every original Number sector. -/
theorem original_intrinsic_joint_row (j : Fin 3) (a : LieIndex) (f : QuantumTest) (z : physicalChart) :
    jointScalarGaugeRow j a f z.val=∑ s : ScalarIndex,
      (intrinsicJointCoefficient j a s z.val : ℂ) • covariantMomentum (scalarDirection s) f z.val := by
  rw [original_joint_scalar_gauge_row]
  apply Finset.sum_congr rfl
  intro s _
  simp only [original_joint_density_cancellation]
  apply PiLp.ext
  intro word
  simp only [GaussFockWeights.weight_apply,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul]

end LowEnergy.SourceNativeDensityTrace
