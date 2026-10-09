import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceBoundedClockAbel
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceHamiltonianVolume
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeCoframeCompatibility
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeDilation
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusClockSturm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockAbelNativeContact
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussNativeMatter GaussFockWeights
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceBoundedClockAbel
open SourcePhysicalKineticSquare SourceScalarPairedTransport
open scoped ContDiff Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev V : End := volumeAction
private abbrev U : End := inverseVolumeAction
private abbrev D : End := dilation
private abbrev H0 : End := diagonalAction
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
def nativeColumn (a : ScalarIndex) : End := U*P a
private abbrev B : End := clockCore
private def R : End := 1-B
def clockSquare : End := B*B
private abbrev n : ℝ := sourceTime 0

private theorem coframe_multiplier (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val)
    (hi : ∀ z s, c (z.1,s)=c z) (v : Ambient) :
    Commute (multiply c hc) (covariantMomentum v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have hd : fderiv ℝ c z (direction v z)=0 := by
      have hg : HasDerivAt (fun t : ℝ => z+t • direction v z) (direction v z) 0 := by
        simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const (direction v z)).const_add z
      have he (t : ℝ) : c (z+t • direction v z)=c z := by
        change c (z.1+t • (0 : Coframe),z.2+t • (inverseL z v).2)=c z
        rw [smul_zero,add_zero,hi]
      have dh := ((hc ⟨z,hz⟩).differentiableAt (by simp)).hasFDerivAt
        |>.comp_hasDerivAt_of_eq 0 hg (by simp)
      apply dh.unique
      change HasDerivAt (fun t : ℝ => c (z+t • direction v z)) 0 0
      rw [show (fun t : ℝ => c (z+t • direction v z))=(fun _ : ℝ => c z) from funext he]
      exact hasDerivAt_const (0 : ℝ) (c z)
    have hf : (multiply c hc f : SourceCoordinateSlice → FockFiber)=fun x => c x • f x := by
      funext x
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    have hD : directional v (multiply c hc f) z=(c z : ℂ) • directional v f z := by
      rw [directional_apply,hf,fderiv_fun_smul ((hc ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
      change c z • fderiv ℝ f z (direction v z)+fderiv ℝ c z (direction v z) • f z=_
      rw [hd,zero_smul,add_zero]
      apply PiLp.ext
      intro word
      exact Complex.real_smul
    change (c z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))=
      (-Complex.I) • (directional v (multiply c hc f) z+connection v z ((c z : ℂ) • f z))
    rw [hD,map_smul,←smul_add,smul_comm]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem native_euler (a : ScalarIndex) : Commute (P a) eulerAction := by
  unfold eulerAction
  apply Commute.sum_right
  intro i _
  have hc : Commute (P a) (coordinateAction i) :=
    (coframe_multiplier (fun z => z.1 i) (by intro z;fun_prop) (by intros;rfl) (scalarDirection a)).symm
  exact hc.mul_right (SourceNativeCoframeCompatibility.original_native_coframe_derivative (scalarDirection a) i).symm

private theorem number_fiber (f : QuantumTest) (z : SourceCoordinateSlice) :
    GaussCoframeForm.number f z=fiberNumber (f z) := by
  apply PiLp.ext
  intro word
  rw [GaussCoframeForm.number_apply,fiberNumber_apply]

private theorem native_number (a : ScalarIndex) : Commute (P a) GaussCoframeForm.number := by
  have hd : Commute GaussCoframeForm.number (directional (scalarDirection a)) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    let T := fiberNumber.restrictScalars ℝ
    have hf : (GaussCoframeForm.number f : SourceCoordinateSlice → FockFiber)=T ∘ f := funext (number_fiber f)
    have h := T.hasFDerivAt.comp z (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    change GaussCoframeForm.number (directional (scalarDirection a) f) z=directional (scalarDirection a) (GaussCoframeForm.number f) z
    rw [number_fiber]
    rw [directional_apply,directional_apply,hf,h.fderiv]
    rfl
  have hc : Commute GaussCoframeForm.number (localMultiplier (connection (scalarDirection a)) (connection_smooth (scalarDirection a))) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change GaussCoframeForm.number (localMultiplier (connection (scalarDirection a)) (connection_smooth (scalarDirection a)) f) z=
      (localMultiplier (connection (scalarDirection a)) (connection_smooth (scalarDirection a)) (GaussCoframeForm.number f)) z
    rw [number_fiber]
    change fiberNumber (connection (scalarDirection a) z (f z))=connection (scalarDirection a) z (GaussCoframeForm.number f z)
    rw [number_fiber]
    exact congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z))
      (native_number_commute (inverseL z (scalarDirection a)).1).eq
  exact ((hd.add_right hc).smul_right (-Complex.I)).symm

private theorem native_dilation (a : ScalarIndex) : Commute (P a) D := by
  rw [D,dilation_operator]
  exact (((native_euler a).smul_right (2/3:ℂ)).add_right (native_number a)).add_right
    ((Commute.one_right (P a)).smul_right (4:ℂ)) |>.smul_right (-Complex.I)

private theorem inverse_dilation : D*U-U*D=(2*Complex.I) • U := by
  have h := congrArg (fun A : End => (-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (D*U-U*D))=
    (-2*Complex.I/3) • ((-3 : ℂ) • U) at h
  simp only [smul_smul] at h
  have hi : (-2*Complex.I/3)*(3*Complex.I/2)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring

private theorem column_dilation (a : ScalarIndex) :
    nativeColumn a*D-D*nativeColumn a=(-2*Complex.I) • nativeColumn a := by
  have hp := (native_dilation a).eq
  have hu := inverse_dilation
  unfold nativeColumn
  linear_combination (norm := (noncomm_ring;module)) U*hp-hu*P a

private theorem column_volume (a : ScalarIndex) : Commute (nativeColumn a) V :=
  ((SourceHamiltonianVolume.real_volume _ _).mul_left (SourceHamiltonianVolume.native_momentum_volume (scalarDirection a)))

private theorem column_clock (a : ScalarIndex) : Commute (nativeColumn a) B := by
  have hp : Commute (P a) B := (coframe_multiplier _ _ (by intros;rfl) (scalarDirection a)).symm
  have hu : Commute U B := by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    change (reciprocalVolume z:ℂ) • ((clockProfile z:ℂ) • f z)=(clockProfile z:ℂ) • ((reciprocalVolume z:ℂ) • f z)
    exact smul_comm (reciprocalVolume z:ℂ) (clockProfile z:ℂ) (f z)
  exact hu.mul_left hp

private theorem reciprocal_volume : (1+V)*R=(1:End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have hd : 1+volume z≠0 := ne_of_gt (by have h:=volume_pos ⟨z,hz⟩;positivity)
    change (f z-(clockProfile z:ℂ) • f z)+(volume z:ℂ) • (f z-(clockProfile z:ℂ) • f z)=f z
    rw [smul_sub,smul_smul]
    have he : (1:ℂ)+(volume z:ℂ)-((clockProfile z:ℂ)+(volume z:ℂ)*(clockProfile z:ℂ))=1 := by
      unfold clockProfile
      push_cast
      have hdc : (1:ℂ)+(volume z:ℂ)≠0 := by exact_mod_cast hd
      field_simp [hdc]
      ring
    calc _=((1:ℂ)+(volume z:ℂ)-((clockProfile z:ℂ)+(volume z:ℂ)*(clockProfile z:ℂ))) • f z := by module
         _=f z := by rw [he,one_smul]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private def nativeCurvature (a : ScalarIndex) : End := nativeColumn a*H0-H0*nativeColumn a

private theorem curvature_volume (a : ScalarIndex) :
    nativeCurvature a*V-V*nativeCurvature a=(-3*(n:ℂ)/2) • nativeColumn a := by
  have hh := SourceHamiltonianVolume.full_source_volume_current
  have hl := (column_volume a).eq
  have hd := column_dilation a
  unfold nativeCurvature
  calc
    _ = nativeColumn a*(H0*V-V*H0)-(H0*V-V*H0)*nativeColumn a-
        H0*(nativeColumn a*V-V*nativeColumn a)+(nativeColumn a*V-V*nativeColumn a)*H0 := by noncomm_ring
    _ = (-3*Complex.I*(n:ℂ)/4) • (nativeColumn a*D-D*nativeColumn a) := by
      rw [hl,sub_self]
      simp only [mul_zero,zero_mul,sub_zero,add_zero]
      rw [hh]
      simp only [mul_smul_comm,smul_mul_assoc,←smul_sub]
    _ = (-3*(n:ℂ)/2) • nativeColumn a := by
      rw [hd,smul_smul]
      congr 1
      calc _=(3*(n:ℂ)/2)*(Complex.I*Complex.I) := by ring
           _=_ := by rw [Complex.I_mul_I];ring

private theorem reciprocal_volume_left : R*(1+V)=(1:End) := by
  have hr : Commute R V := (Commute.one_left V).sub_left (SourceHamiltonianVolume.real_volume _ _)
  exact ((Commute.one_right R).add_right hr).eq.trans reciprocal_volume

private theorem curvature_reciprocal (a : ScalarIndex) :
    nativeCurvature a*R-R*nativeCurvature a=(3*(n:ℂ)/2) • (R^2*nativeColumn a) := by
  let K := nativeCurvature a
  have h1 : R*K*(1+V)*R=R*K := by
    calc _=R*K*((1+V)*R) := by noncomm_ring
         _=_ := by rw [reciprocal_volume,mul_one]
  have h2 : R*(1+V)*K*R=K*R := by rw [reciprocal_volume_left,one_mul]
  have hK : K*(1+V)-(1+V)*K=(-3*(n:ℂ)/2) • nativeColumn a := by
    simpa only [mul_add,add_mul,mul_one,one_mul,add_sub_add_left_eq_sub] using curvature_volume a
  have hLR : nativeColumn a*R=R*nativeColumn a := ((Commute.one_right (nativeColumn a)).sub_right (column_clock a)).eq
  have hRLR : R*nativeColumn a*R=R^2*nativeColumn a := by
    rw [mul_assoc,hLR,←mul_assoc,←pow_two]
  calc
    _= -(R*K*(1+V)*R-R*(1+V)*K*R) := by rw [h1,h2];abel
    _= -(R*(K*(1+V)-(1+V)*K)*R) := by noncomm_ring
    _= (3*(n:ℂ)/2) • (R*nativeColumn a*R) := by
      rw [hK]
      simp only [mul_smul_comm,smul_mul_assoc]
      rw [←neg_smul]
      congr 1
      ring
    _= (3*(n:ℂ)/2) • (R^2*nativeColumn a) := by rw [hRLR]

private theorem curvature_clock (a : ScalarIndex) :
    nativeCurvature a*B-B*nativeCurvature a=(-3*(n:ℂ)/2) • (R^2*nativeColumn a) := by
  have hb : B=(1:End)-R := by unfold R;abel
  rw [hb]
  have he : nativeCurvature a*(1-R)-(1-R)*nativeCurvature a=
    -(nativeCurvature a*R-R*nativeCurvature a) := by noncomm_ring
  rw [he,curvature_reciprocal,←neg_smul]
  congr 1
  ring

/-- The original Hamiltonian/clock double contact returns the same native column. -/
theorem actual_native_clock_contact (a : ScalarIndex) :
    nativeCurvature a*clockSquare-clockSquare*nativeCurvature a=
      (-3*(n:ℂ)) • (B*(1-B)^2*nativeColumn a) := by
  have hB : Commute B R := (Commute.one_right B).sub_right (Commute.refl B)
  have hBR := (hB.pow_right 2).eq
  have hLB := (column_clock a).eq
  unfold clockSquare
  calc
    _=(nativeCurvature a*B-B*nativeCurvature a)*B+B*(nativeCurvature a*B-B*nativeCurvature a) := by noncomm_ring
    _=(-3*(n:ℂ)/2) • ((R^2*nativeColumn a)*B+B*(R^2*nativeColumn a)) := by
      rw [curvature_clock]
      simp only [smul_mul_assoc,mul_smul_comm,←smul_add]
    _=(-3*(n:ℂ)) • (B*R^2*nativeColumn a) := by
      have he : (R^2*nativeColumn a)*B+B*(R^2*nativeColumn a)=
        (2:ℂ) • (B*R^2*nativeColumn a) := by
        rw [mul_assoc,hLB,←mul_assoc,←hBR]
        module
      rw [he,smul_smul]
      congr 1
      ring
    _=_ := rfl

private theorem clock_smooth (z : physicalChart) : ContDiffAt ℝ ∞ clockProfile z.val :=
  volume_smooth.contDiffAt.div (contDiffAt_const.add volume_smooth.contDiffAt)
    (ne_of_gt (by have h:=volume_pos z;positivity))
private theorem clock_range (z : physicalChart) : 0 ≤ clockProfile z ∧ clockProfile z ≤ 1 := by
  have hv:=volume_pos z
  unfold clockProfile
  have hd : 0<1+volume z:=by positivity
  exact ⟨div_nonneg hv.le hd.le,(div_le_one hd).mpr (by linarith)⟩
private def contactProfile (z : SourceCoordinateSlice) : ℝ := clockProfile z*(1-clockProfile z)^2
private theorem profile_smooth (z : physicalChart) : ContDiffAt ℝ ∞ contactProfile z.val :=
  (clock_smooth z).mul ((contDiffAt_const.sub (clock_smooth z)).pow 2)
private theorem profile_range (z : physicalChart) : 0 ≤ contactProfile z ∧ contactProfile z ≤ 4/27 := by
  obtain ⟨h0,h1⟩:=clock_range z
  have hfactor:=mul_nonneg (sq_nonneg (clockProfile z-(1/3:ℝ)))
    (show 0 ≤ (4/3:ℝ)-clockProfile z by linarith)
  unfold contactProfile
  constructor
  · positivity
  · nlinarith only [hfactor]
private def profileFiber (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (contactProfile z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem fiber_smooth (z : physicalChart) : ContDiffAt ℝ ∞ profileFiber z.val :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (profile_smooth z)).smul contDiffAt_const
private theorem fiber_weight (z : physicalChart) (w : ℕ→ℂ) : Commute (weight w) (profileFiber z) :=
  (Commute.one_right _).smul_right _
private theorem fiber_bound (z : physicalChart) (f : FockFiber) : ‖profileFiber z f‖ ≤ (4/27:ℝ)*‖f‖ := by
  change ‖(contactProfile z:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (profile_range z).1]
  exact mul_le_mul_of_nonneg_right (profile_range z).2 (norm_nonneg _)
private def profileOperator : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension profileFiber fiber_smooth fiber_weight (4/27) (by norm_num) fiber_bound
private theorem profile_operator_norm : ‖profileOperator‖ ≤ (4/27:ℝ) :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem profile_operator_core (f : QuantumTest) :
    profileOperator (embed f)=embed ((B*R^2) f) := by
  have he:=GaussBoundedMultiplier.extension_core profileFiber fiber_smooth fiber_weight (4/27)
    (by norm_num) fiber_bound f
  unfold profileOperator
  rw [he]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change (contactProfile z:ℂ) • f z=(clockProfile z:ℂ) • ((1-B) ((1-B) f) z)
  change (contactProfile z:ℂ) • f z=(clockProfile z:ℂ) • (f z-(clockProfile z:ℂ) • f z-
    (clockProfile z:ℂ) • (f z-(clockProfile z:ℂ) • f z))
  unfold contactProfile
  push_cast
  module

private theorem contact_norm (a : ScalarIndex) (f : QuantumTest) :
    ‖embed ((nativeCurvature a*clockSquare-clockSquare*nativeCurvature a) f)‖ ≤
      (4*n/9)*‖embed (nativeColumn a f)‖ := by
  have hn : 0<n := by
    change 0<sourceTime 0
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  rw [actual_native_clock_contact,LinearMap.smul_apply,map_smul,norm_smul]
  have hc : ‖(-3*(n:ℂ))‖=3*n := by
    rw [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
  rw [hc]
  have he : embed (((B*(1-B)^2*nativeColumn a):End) f)=profileOperator (embed (nativeColumn a f)) :=
    (profile_operator_core (nativeColumn a f)).symm
  rw [he]
  have hb : ‖profileOperator (embed (nativeColumn a f))‖ ≤ (4/27:ℝ)*‖embed (nativeColumn a f)‖ :=
    (profileOperator.le_opNorm (embed (nativeColumn a f))).trans
      (mul_le_mul_of_nonneg_right profile_operator_norm (norm_nonneg (embed (nativeColumn a f))))
  calc _ ≤ (3*n)*((4/27:ℝ)*‖embed (nativeColumn a f)‖) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
       _= _ := by ring

/-- The complete original seventy-column contact has its source-generated joint price. -/
theorem actual_native_clock_joint_price (f : QuantumTest) :
    (∑a : ScalarIndex,‖embed ((nativeCurvature a*clockSquare-clockSquare*nativeCurvature a) f)‖^2) ≤
      (16*n^2/81)*(∑a : ScalarIndex,‖embed (nativeColumn a f)‖^2) := by
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun a (_:a∈(Finset.univ:Finset ScalarIndex))=>
    pow_le_pow_left₀ (norm_nonneg _) (contact_norm a f) 2)
  have hc : (4*n/9)^2=16*n^2/81 := by ring
  simp only [mul_pow,←Finset.mul_sum,hc] at h
  exact h

/-- The same compressed source retains its complete defect beside the generated native contact. -/
theorem actual_native_clock_full_defect (F : Index) (a : ScalarIndex) :
    ((nativeColumn a*SourceScalarPairedTransport.compressionCore F-
      SourceScalarPairedTransport.compressionCore F*nativeColumn a)*clockSquare-
      clockSquare*(nativeColumn a*SourceScalarPairedTransport.compressionCore F-
      SourceScalarPairedTransport.compressionCore F*nativeColumn a))=
    (-3*(n:ℂ)) • (B*(1-B)^2*nativeColumn a)-
      ((nativeColumn a*SourceScalarPairedTransport.defectAction F-
      SourceScalarPairedTransport.defectAction F*nativeColumn a)*clockSquare-
      clockSquare*(nativeColumn a*SourceScalarPairedTransport.defectAction F-
      SourceScalarPairedTransport.defectAction F*nativeColumn a)) := by
  have h:=actual_native_clock_contact a
  unfold nativeCurvature at h
  unfold SourceScalarPairedTransport.defectAction
  linear_combination (norm:=noncomm_ring) h

end LowEnergy.SourceClockAbelNativeContact
