import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCoframeScaleAction
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCoframeStrongJet
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceFourPoleEnergyClosed
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussRadialMomentum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceClosedCostNativeProbe
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussLiveMomentum
open GaussFockPair GaussCoframeForm GaussDiagonalHistory GaussNativeForm GaussNativeEnergy
open SourcePhysicalKineticSquare SourceDilationMultiplier
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceDilationRemainder
open SourceHamiltonianScaleJet SourceCoframeScaleAction SourceJointScaleBudget
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge GaussRadialMomentum
open scoped ContDiff RealInnerProductSpace

/-- The force is taken against the full signed source action. -/
def force (A T : CoreEnd) : CoreEnd := Complex.I • (A*T-T*A)

def projected (A : CoreEnd) : CoreEnd :=
  scaleDerivative (scaleDerivative (scaleDerivative A))+
    (3 : ℂ) • scaleDerivative (scaleDerivative A)-scaleDerivative A-(3 : ℂ) • A

private theorem derivative_commutator (A T : CoreEnd) (hT : Commute dilation T) :
    scaleDerivative (A*T-T*A)=scaleDerivative A*T-T*scaleDerivative A := by
  have he : dilation*(A*T-T*A)-(A*T-T*A)*dilation=
      (dilation*A-A*dilation)*T-T*(dilation*A-A*dilation) := by
    calc
      _ = (dilation*A-A*dilation)*T-T*(dilation*A-A*dilation)+
        (T*dilation-dilation*T)*A+A*(dilation*T-T*dilation) := by noncomm_ring
      _ = _ := by rw [hT.eq]; noncomm_ring
  change (3*Complex.I/2) • (dilation*(A*T-T*A)-(A*T-T*A)*dilation)=_
  change (3*Complex.I/2) • (dilation*(A*T-T*A)-(A*T-T*A)*dilation)=
    ((3*Complex.I/2) • (dilation*A-A*dilation))*T-
      T*((3*Complex.I/2) • (dilation*A-A*dilation))
  rw [he,smul_sub]
  simp only [sub_mul,mul_sub,smul_sub,smul_mul_assoc,mul_smul_comm]

private theorem derivative_force (A T : CoreEnd) (hT : Commute dilation T) :
    scaleDerivative (force A T)=force (scaleDerivative A) T := by
  simp only [force,map_smul,derivative_commutator A T hT]

/-- Projection commutes with the actual native force, without deleting any Hamiltonian term. -/
theorem projected_native_force (v : Ambient) :
    projected (force diagonalAction (covariantMomentum v))=
      (48 : ℂ) • force localAction (covariantMomentum v) := by
  have hT : Commute dilation (covariantMomentum v) :=
    sub_eq_zero.mp (SourceDilationMomentum.native_momentum_current v)
  unfold projected
  simp only [derivative_force _ _ hT]
  have he := source_local_from_scale_jet
  have hh := congrArg (fun A => force A (covariantMomentum v)) he
  simp only [force,add_mul,mul_add,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm] at hh ⊢
  convert! hh using 1 <;> module

/-- The mixed force is the derivative of the genuine coframe-conjugated source family. -/
theorem native_force_conjugation (t : ℝ) (v : Ambient) :
    conjugation t (force diagonalAction (covariantMomentum v))=
      force (sourceScale (SourceCoframeScaleTransport.rate t)) (covariantMomentum v) := by
  simp only [force,map_smul,map_sub,map_mul,original_hamiltonian_conjugation,
    native_momentum_conjugation]

def coordinate (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  inner ℝ (z.2.1 : Scalar) v.1

def coordinateAction (v : Ambient) : CoreEnd := multiply (coordinate v)
  (fun _ => (scalarCoordinate.contDiff.inner ℝ contDiff_const).contDiffAt)

private theorem local_as_norm : localPotential=(fun z =>
    sourceTime 0*volume z*(‖scalarCoordinate z‖^2+3)) := by
  funext z
  unfold localPotential volumePotential
  change sourceTime 0*volume z*inner ℝ (z.2.1 : Scalar) (z.2.1 : Scalar)+
    3*sourceTime 0*volume z=sourceTime 0*volume z*(‖(z.2.1 : Scalar)‖^2+3)
  rw [real_inner_self_eq_norm_sq]
  ring

private theorem local_global_smooth : ContDiff ℝ ∞ localPotential := by
  rw [local_as_norm]
  exact (contDiff_const.mul volume_smooth).mul
    ((scalarCoordinate.contDiff.norm_sq ℝ).add contDiff_const)

/-- Native differentiation reads the original scalar coordinate; all inverse-L orbit terms cancel. -/
theorem local_native_derivative (v : Ambient) (z : physicalChart) :
    fderiv ℝ localPotential z.val (direction v z.val)=
      2*sourceTime 0*volume z.val*coordinate v z.val := by
  have hd := ((volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt.const_mul
    (sourceTime 0)).mul (((scalarCoordinate.hasFDerivAt (x := z.val)).norm_sq).add_const 3)
  rw [local_as_norm]
  change fderiv ℝ ((fun y => sourceTime 0*volume y)*(fun x => ‖scalarCoordinate x‖^2+3))
    z.val (direction v z.val)=_
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,two_smul]
  have hv : fderiv ℝ volume z.val (direction v z.val)=0 := by
    rw [volume_derivative]
    simp [direction]
  change (sourceTime 0*volume z.val)*
    (inner ℝ (z.val.2.1 : Scalar) ((inverseL z.val v).2.1 : Scalar)+
      inner ℝ (z.val.2.1 : Scalar) ((inverseL z.val v).2.1 : Scalar))+
    (‖scalarCoordinate z.val‖^2+3)*(sourceTime 0*fderiv ℝ volume z.val (direction v z.val))=_
  rw [hv,inverse_radial]
  unfold coordinate
  ring

private theorem local_action_real (f : QuantumTest) :
    (localAction f : SourceCoordinateSlice → FockFiber)=fun z => localPotential z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem directional_local (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (localAction f) z=localPotential z • directional v f z+
      (2*sourceTime 0*volume z*coordinate v z) • f z := by
  rw [directional_apply,local_action_real,
    fderiv_fun_smul (local_global_smooth.differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change localPotential z • directional v f z+fderiv ℝ localPotential z (direction v z) • f z=_
  by_cases hz : z∈physicalChart
  · rw [local_native_derivative v ⟨z,hz⟩]
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    rw [hf,smul_zero,smul_zero]

theorem local_native_force (v : Ambient) :
    force localAction (covariantMomentum v)=
      (-2*(sourceTime 0 : ℂ)) • (volumeAction*coordinateAction v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change Complex.I • ((localPotential z : ℂ) •
    ((-Complex.I) • (directional v f z+connection v z (f z)))-
    (-Complex.I) • (directional v (localAction f) z+
      connection v z ((localPotential z : ℂ) • f z)))=_
  rw [directional_local,map_smul]
  apply PiLp.ext
  intro word
  simp only [PiLp.sub_apply,PiLp.smul_apply]
  change Complex.I*((localPotential z : ℂ)*
    (-Complex.I*(directional v f z word+connection v z (f z) word))-
    -Complex.I*((localPotential z : ℂ)*directional v f z word+
      ((2*sourceTime 0*volume z*coordinate v z : ℝ) : ℂ)*f z word+
      (localPotential z : ℂ)*connection v z (f z) word))=
    (-2*(sourceTime 0 : ℂ))*((volume z : ℂ)*((coordinate v z : ℂ)*f z word))
  push_cast
  calc
    _ = (Complex.I*Complex.I)*(2*(sourceTime 0 : ℂ)*(volume z : ℂ)*
      (coordinate v z : ℂ)*f z word) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

/-- A new mixed source identity produces the linear, rather than quadratic, scalar insertion. -/
theorem projected_force_coordinate (v : Ambient) :
    projected (force diagonalAction (covariantMomentum v))=
      (-96*(sourceTime 0 : ℂ)) • (volumeAction*coordinateAction v) := by
  rw [projected_native_force,local_native_force,smul_smul]
  congr 1
  ring

def weightedMomentum (v : Ambient) : CoreEnd :=
  multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*covariantMomentum v

private theorem derivative_mul (A T : CoreEnd) :
    scaleDerivative (A*T)=scaleDerivative A*T+A*scaleDerivative T := by
  change (3*Complex.I/2) • (dilation*(A*T)-(A*T)*dilation)=
    ((3*Complex.I/2) • (dilation*A-A*dilation))*T+
      A*((3*Complex.I/2) • (dilation*T-T*dilation))
  have he : dilation*(A*T)-(A*T)*dilation=
      (dilation*A-A*dilation)*T+A*(dilation*T-T*dilation) := by noncomm_ring
  rw [he,smul_add]
  simp only [sub_mul,mul_sub,smul_sub,smul_mul_assoc,mul_smul_comm]

/-- This weight is n/U from the original source coefficient, with no completed inverse-S. -/
theorem weighted_momentum_scale (v : Ambient) :
    scaleDerivative (weightedMomentum v)=(-3 : ℂ) • weightedMomentum v := by
  have hi : scaleDerivative (multiply GaussCoframeForm.inverseVolume
      GaussCoframeForm.inverseVolume_smooth)=
      (-3 : ℂ) • multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth := by
    change (3*Complex.I/2) • (dilation*_-_*dilation)=_
    rw [inverse_volume_commutator,smul_smul]
    have hc : (3*Complex.I/2)*(2*Complex.I)=(-3 : ℂ) := by
      calc _=3*(Complex.I*Complex.I) := by ring
           _=_ := by rw [Complex.I_mul_I]; ring
    rw [hc]
  have hp : scaleDerivative (covariantMomentum v)=0 := by
    change (3*Complex.I/2) • (dilation*_-_*dilation)=0
    rw [SourceDilationMomentum.native_momentum_current,smul_zero]
  rw [weightedMomentum,derivative_mul,hi,hp,mul_zero,add_zero,smul_mul_assoc]

def shiftedDerivative : CoreEnd →ₗ[ℂ] CoreEnd := scaleDerivative+(3 : ℂ) • LinearMap.id

def shiftedProjected (A : CoreEnd) : CoreEnd :=
  shiftedDerivative (shiftedDerivative (shiftedDerivative A))+
    (3 : ℂ) • shiftedDerivative (shiftedDerivative A)-shiftedDerivative A-(3 : ℂ) • A

private theorem shifted_force (A : CoreEnd) (v : Ambient) :
    shiftedDerivative (force A (weightedMomentum v))=
      force (scaleDerivative A) (weightedMomentum v) := by
  change scaleDerivative (force A (weightedMomentum v))+(3 : ℂ) • force A (weightedMomentum v)=_
  simp only [force,map_smul,map_sub,derivative_mul,weighted_momentum_scale,
    smul_mul_assoc,mul_smul_comm]
  module

private theorem local_weight_commute : Commute localAction
    (multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (localPotential z : ℂ) (GaussCoframeForm.inverseVolume z : ℂ) (f z)

private theorem weight_volume :
    multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*volumeAction=
      (sourceTime 0 : ℂ) • (1 : CoreEnd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (GaussCoframeForm.inverseVolume z : ℂ) • ((volume z : ℂ) • f z)=
    (sourceTime 0 : ℂ) • f z
  by_cases hz : z∈physicalChart
  · rw [smul_smul]
    congr 1
    unfold GaussCoframeForm.inverseVolume
    push_cast
    exact div_mul_cancel₀ _ (by exact_mod_cast (volume_pos ⟨z,hz⟩).ne')
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h)),smul_zero,smul_zero,smul_zero]

/-- Shifted scale projection gives a linear scalar insertion without an outside inverse volume. -/
theorem shifted_force_coordinate (v : Ambient) :
    shiftedProjected (force diagonalAction (weightedMomentum v))=
      (-96*(sourceTime 0 : ℂ)^2) • coordinateAction v := by
  have hj : shiftedProjected (force diagonalAction (weightedMomentum v))=
      (48 : ℂ) • force localAction (weightedMomentum v) := by
    unfold shiftedProjected
    simp only [shifted_force]
    have hh := congrArg (fun A => force A (weightedMomentum v)) source_local_from_scale_jet
    simp only [force,add_mul,mul_add,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm] at hh ⊢
    convert! hh using 1 <;> module
  rw [hj]
  have hf : force localAction (weightedMomentum v)=
      multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*
        force localAction (covariantMomentum v) := by
    unfold weightedMomentum force
    rw [mul_smul_comm]
    congr 1
    rw [←mul_assoc,local_weight_commute.eq]
    noncomm_ring
  rw [hf,local_native_force,mul_smul_comm,←mul_assoc,weight_volume,
    smul_mul_assoc,one_mul,smul_smul,smul_smul]
  congr 1
  ring

/-- Energy gaps lower the exact four-pole Gram to endpoint two-pole terms, including collisions. -/
theorem closed_kernel_gap_reduction (μ a b c d : ℝ) (hμ : 0<μ) :
    ((a : ℂ)-(b : ℂ))*((c : ℂ)-(d : ℂ))*
      SourceFourPoleEnergyClosed.closedKernel μ a b c d=
    2*(Real.pi : ℂ)*
      ((SourceFourPoleEnergyClosed.gap μ a c)⁻¹-(SourceFourPoleEnergyClosed.gap μ a d)⁻¹-
        (SourceFourPoleEnergyClosed.gap μ b c)⁻¹+(SourceFourPoleEnergyClosed.gap μ b d)⁻¹) := by
  unfold SourceFourPoleEnergyClosed.closedKernel
  field_simp [SourceFourPoleEnergyClosed.gap_ne μ a c hμ,
    SourceFourPoleEnergyClosed.gap_ne μ a d hμ,SourceFourPoleEnergyClosed.gap_ne μ b c hμ,
    SourceFourPoleEnergyClosed.gap_ne μ b d hμ]
  unfold SourceFourPoleEnergyClosed.gap
  ring_nf
  simp only [Complex.I_sq]
  have hi3 : Complex.I^3= -Complex.I := by rw [pow_succ,Complex.I_sq]; ring
  rw [hi3]
  ring

end LowEnergy.SourceClosedCostNativeProbe
