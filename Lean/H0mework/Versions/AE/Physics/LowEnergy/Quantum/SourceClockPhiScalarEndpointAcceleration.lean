import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusAcceleration
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiSecondPressure
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarAffineScaleTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiScalarEndpointAcceleration
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourcePhysicalKineticSquare SourceCoframeVolumeCurrent SourceScalarDoubleCurrent
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceScalarVirialBulk
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] resolventCore compressionCore defectAction diagonalAction
private abbrev U : End := inverseVolumeAction
private abbrev D : End := dilation
private abbrev E : End := phiEulerAction
private abbrev Phi : End := SourceScalarAffineScaleTransport.generator
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev n : ℝ := sourceTime 0
private abbrev Aρ : End := SourceClockPhiRadiusAcceleration.clockAcceleration

/-- The actual coframe source word retains both inverse-volume factors. -/
def endpointWord : End := U*U*((3:ℂ) • D+(4*Complex.I) • 1)

/-- The source affine generator includes the scalar61 half-density shift. -/
def sourceLq : End := Phi-(1/2:ℂ) • (1-S^2)

private abbrev C : End := endpointWord
private def T : End := ((n:ℂ)^2/8) • C

private theorem actual_D_U : D*U-U*D=(2*Complex.I) • U := by
  have h := congrArg (fun A : End => (-2*Complex.I/3) • A)
    SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (D*U-U*D))=
    (-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi : (-2*Complex.I/3)*(3*Complex.I/2)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring

private theorem actual_U_D_U : U*D*U=U*U*D+(2*Complex.I) • (U*U) := by
  have h := congrArg (fun A : End => U*A) actual_D_U
  linear_combination (norm := noncomm_ring) h

private theorem actual_D_U_U : D*(U*U)=U*U*D+(4*Complex.I) • (U*U) := by
  have h := congrArg (fun A : End => A*U) actual_D_U
  linear_combination (norm := (noncomm_ring;module)) h+actual_U_D_U

private theorem actual_acceleration_source :
    Aρ=(3*Complex.I*(n:ℂ)^2/8) • (U*U*D*Phi)-
      (3*(n:ℂ)^2/4) • (U*U*Phi) := by
  unfold Aρ SourceClockPhiRadiusAcceleration.clockAcceleration
  rw [actual_U_D_U]
  simp only [add_mul,smul_mul_assoc,smul_add,smul_smul]
  have hi : (3*Complex.I*(n:ℂ)^2/8)*(2*Complex.I)= -(3*(n:ℂ)^2/4) := by
    calc _=(3*(n:ℂ)^2/4)*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,neg_smul]
  module

private theorem actual_T_Phi :
    T*Phi=(-Complex.I) • (Aρ+((n:ℂ)^2/4) • (U*U*Phi)) := by
  rw [actual_acceleration_source]
  unfold T C endpointWord
  simp only [smul_mul_assoc,add_mul,mul_add,mul_smul_comm,smul_add,smul_sub,smul_smul]
  have hi : (-Complex.I)*(3*Complex.I*(n:ℂ)^2/8)=3*(n:ℂ)^2/8 := by
    calc _= -(3*(n:ℂ)^2/8)*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi]
  noncomm_ring
  module

private theorem actual_Phi_U : Commute Phi U := by
  have h := SourceScalarInverseBulk.inverse_phi
  change E*U-U*E=0 at h
  change Commute (E+(61/2:ℂ) • (1:End)) U
  have hEU : Commute E U := sub_eq_zero.mp h
  exact hEU.add_left ((Commute.one_left U).smul_left _)

private theorem actual_Phi_D : Commute Phi D := by
  have h := SourceScalarPositiveBulkWard.original_dilation_phi
  change E*D-D*E=0 at h
  change Commute (E+(61/2:ℂ) • (1:End)) D
  have hED : Commute E D := sub_eq_zero.mp h
  exact hED.add_left ((Commute.one_left D).smul_left _)

private theorem actual_Phi_T : Commute Phi T := by
  unfold T C endpointWord
  exact ((actual_Phi_U.mul_right actual_Phi_U).mul_right
    ((actual_Phi_D.smul_right (3:ℂ)).add_right
      ((Commute.one_right Phi).smul_right (4*Complex.I)))).smul_right _

private theorem actual_Phi_pair (f g : QuantumTest) :
    sourcePair f (Phi g)= -sourcePair (Phi f) g := by
  have hd (q : QuantumTest) : HasDerivAt
      (fun t : ℝ => embed (SourceScalarAffineScaleTransport.coreFlow t q))
      (embed (Phi q)) 0 := by
    simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0
  have h := (hd f).inner ℂ (hd g)
  simp only [SourceScalarAffineScaleTransport.coreFlow_zero] at h
  have he : (fun t : ℝ => inner ℂ
      (embed (SourceScalarAffineScaleTransport.coreFlow t f))
      (embed (SourceScalarAffineScaleTransport.coreFlow t g)))=
      fun _ => sourcePair f g :=
    funext (fun t => SourceScalarAffineScaleTransport.coreFlow_pair t f g)
  rw [he] at h
  have hz := h.unique (hasDerivAt_const (0:ℝ) (sourcePair f g))
  change sourcePair f (Phi g)+sourcePair (Phi f) g=0 at hz
  exact eq_neg_of_add_eq_zero_left hz

private theorem actual_Phi_endpoint (q p : QuantumTest) :
    (sourcePair (Phi q) (T p)).im=
      (sourcePair q ((Aρ+((n:ℂ)^2/4) • (U*U*Phi)) p)).re := by
  have hp := actual_Phi_pair q (T p)
  have hc := LinearMap.congr_fun actual_Phi_T.eq p
  change Phi (T p)=T (Phi p) at hc
  have ht := LinearMap.congr_fun actual_T_Phi p
  change T (Phi p)=(-Complex.I) • ((Aρ+((n:ℂ)^2/4) • (U*U*Phi)) p) at ht
  rw [hc,ht] at hp
  have h := congrArg Complex.im hp
  simp only [sourcePair,map_smul,inner_smul_right,Complex.mul_im,
    Complex.neg_im,Complex.neg_re,Complex.I_re,Complex.I_im] at h
  norm_num at h
  exact h.symm


private theorem actual_Lq_endpoint (q p : QuantumTest) :
    n^2/8*(sourcePair (sourceLq q) (C p)).im=
      (sourcePair q ((Aρ+((n:ℂ)^2/4) • (U*U*Phi)) p)).re-
        n^2/16*(sourcePair (((1:End)-S^2) q) (C p)).im := by
  have hT (f : QuantumTest) :
      (sourcePair f (T p)).im=n^2/8*(sourcePair f (C p)).im := by
    have hn : ((n:ℂ)^2/8)=((n^2/8:ℝ):ℂ) := by push_cast; ring
    simp only [T,LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right,hn]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero]
  rw [←hT]
  have hL : sourcePair (sourceLq q) (T p) =
      sourcePair (Phi q) (T p)-
        (1/2:ℂ)*sourcePair (((1:End)-S^2) q) (T p) := by
    simp only [sourceLq,LinearMap.sub_apply,LinearMap.smul_apply,
      sourcePair,map_sub,map_smul,inner_sub_left,inner_smul_left,
      map_div₀,map_one,map_ofNat]
  have hhalf (z : ℂ) : ((1/2:ℂ)*z).im=(1/2:ℝ)*z.im := by
    norm_num [Complex.mul_im,Complex.div_re,Complex.div_im]
  rw [hL,Complex.sub_im,actual_Phi_endpoint,hhalf,hT]
  ring

private theorem actual_Lq_compression (F : Index) (q p : QuantumTest) :
    n^2/8*(sourcePair (sourceLq q) (endpointWord p)).im=
      (sourcePair q ((SourceClockPhiRadiusAcceleration.scalarAcceleration+
        SourceClockPhiRadiusAcceleration.stableSpatialAcceleration+
        SourceClockPhiRadiusAcceleration.accelerationDefect F+
        bracket (compressionCore F) (bracket (compressionCore F)
          SourceClockPhiRadiusAcceleration.phiSquare)+
        ((n:ℂ)^2/4) • (U*U*Phi)) p)).re-
        n^2/16*(sourcePair (((1:End)-S^2) q) (endpointWord p)).im := by
  rw [actual_Lq_endpoint]
  have h := SourceClockPhiRadiusAcceleration.actual_phi_square_acceleration F
  have hA : Aρ=SourceClockPhiRadiusAcceleration.scalarAcceleration+
      SourceClockPhiRadiusAcceleration.stableSpatialAcceleration+
      SourceClockPhiRadiusAcceleration.accelerationDefect F+
      bracket (compressionCore F) (bracket (compressionCore F)
        SourceClockPhiRadiusAcceleration.phiSquare) := by
    linear_combination (norm := module) h
  rw [hA]

/-- The single scalar endpoint enters the actual radius-square acceleration on its retarded legs. -/
theorem actual_phi_endpoint_acceleration (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    let q : QuantumTest := resolventCore F z hz (coreEquiv.symm g)
    let h : QuantumTest := resolventCore F z hz (r (coreEquiv.symm g))
    let p : QuantumTest := (S*(phiThetaAction m ell)^2) (r q-h)
    n^2/8*(sourcePair (sourceLq q) (endpointWord p)).im=
      (sourcePair q ((Aρ+((n:ℂ)^2/4) • (U*U*Phi)) p)).re-
        n^2/16*(sourcePair (((1:End)-S^2) q) (endpointWord p)).im := by
  dsimp only
  exact actual_Lq_endpoint _ _

/-- The exact same compression supplies all three double defects and the full C_F double current. -/
theorem actual_phi_endpoint_compression (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    let q : QuantumTest := resolventCore F z hz (coreEquiv.symm g)
    let h : QuantumTest := resolventCore F z hz (r (coreEquiv.symm g))
    let p : QuantumTest := (S*(phiThetaAction m ell)^2) (r q-h)
    n^2/8*(sourcePair (sourceLq q) (endpointWord p)).im=
      (sourcePair q ((SourceClockPhiRadiusAcceleration.scalarAcceleration+
        SourceClockPhiRadiusAcceleration.stableSpatialAcceleration+
        SourceClockPhiRadiusAcceleration.accelerationDefect F+
        bracket (compressionCore F) (bracket (compressionCore F)
          SourceClockPhiRadiusAcceleration.phiSquare)+
        ((n:ℂ)^2/4) • (U*U*Phi)) p)).re-
        n^2/16*(sourcePair (((1:End)-S^2) q) (endpointWord p)).im := by
  dsimp only
  exact actual_Lq_compression F _ _

end LowEnergy.SourceClockPhiScalarEndpointAcceleration
