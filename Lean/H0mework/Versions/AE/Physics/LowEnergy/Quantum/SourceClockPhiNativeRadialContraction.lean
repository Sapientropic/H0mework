import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusClockSturm
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiEndpointNativePressure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiNativeRadialContraction
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open GaussNativeMatter GaussQuantumMultiplier GaussNativePotential SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceScalarFlatJoint SourceScalarVirialBulk
open SourceClockPhiRadiusSourceCurrent SourceScalarDoubleCurrent
open SourceClockPhiEndpointNativePressure
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U : End := inverseVolumeAction
private abbrev S : End := phiInverseAction
private abbrev rho : End := phiRadiusAction
private abbrev Ephi : End := SourceScalarVirialBulk.phiEulerAction
private abbrev Phi : End := SourceScalarAffineScaleTransport.generator
private abbrev n : ℝ := sourceTime 0
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev Dphi (a : ScalarIndex) : End := phiDirectionAction (scalarBasis a)
private abbrev L (a : ScalarIndex) : End := U*P a

private def phiColumn (a : ScalarIndex) : End :=
  multiply (fun z => inner ℝ (scalarField z) (scalarBasis a))
    (fun _ => (scalarField_smooth.inner ℝ contDiff_const).contDiffAt)
private def phiMomentum : End := ∑ a : ScalarIndex,phiColumn a*P a

private theorem scalar_frame_expansion (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,inner ℝ (scalarField z) (scalarBasis a) • scalarDirection a)=
      (scalarField z,0) := by
  apply Prod.ext
  · simp only [Prod.fst_sum,Prod.smul_fst]
    simpa only [scalarDirection,OrthonormalBasis.repr_apply_apply,real_inner_comm] using
      scalarBasis.sum_repr (scalarField z)
  · simp [scalarDirection,Prod.snd_sum]

private theorem phi_momentum_contraction : phiMomentum=(-Complex.I) • Ephi := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have he := congrArg (SourceElectricColumns.pointMomentum f z) (scalar_frame_expansion z)
    simp only [map_sum,map_smul] at he
    have hs : phiMomentum f z=∑ a : ScalarIndex,inner ℝ (scalarField z) (scalarBasis a) •
        SourceElectricColumns.pointMomentum f z (scalarDirection a) := by
      simp only [phiMomentum,LinearMap.sum_apply,sum_apply,Module.End.mul_apply]
      apply Finset.sum_congr rfl
      intro a _
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    rw [hs,he]
    let v : scalarSlice := vacuumSlice+z.2.1
    have hi := native_scalar_slice_inverse ⟨z,hz⟩ v
    have hd : direction (scalarField z,0) z=phiEuler z := by
      change (0,(inverseL z (v.val,0)).2)=_
      rw [hi]
      rfl
    have hc : connection (scalarField z,0) z=0 := by
      change GaussNativeMatter.nativeFock (inverseL z (v.val,0)).1=0
      rw [hi,map_zero]
    change (-Complex.I) • (fderiv ℝ f z (direction (scalarField z,0) z)+
      connection (scalarField z,0) z (f z))=(-Complex.I) • phiEulerAction f z
    rw [hd,hc,zero_apply,add_zero,phi_euler_apply]
  · exact (image_eq_zero_of_notMem_tsupport (fun h => hz ((phiMomentum f).tsupport_subset h))).trans
      (image_eq_zero_of_notMem_tsupport (fun h => hz (((-Complex.I) • Ephi f).tsupport_subset h))).symm

private theorem direction_column (a : ScalarIndex) :
    Dphi a=(-1/4:ℂ) • (S*phiColumn a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (phiDirectionWeight (scalarBasis a) z:ℂ) • f z=
    (-1/4:ℂ) • ((phiReciprocal z:ℂ) •
      ((inner ℝ (scalarField z) (scalarBasis a):ℂ) • f z))
  simp only [smul_smul]
  congr 1
  unfold phiDirectionWeight phiReciprocal
  push_cast
  ring

private theorem inverse_direction_commute (a : ScalarIndex) : Commute U (Dphi a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (reciprocalVolume z:ℂ)
    (phiDirectionWeight (scalarBasis a) z:ℂ) (f z)
private theorem inverse_phi_commute : Commute U S := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (reciprocalVolume z:ℂ) (phiReciprocal z:ℂ) (f z)

/-- True original 70-column scalar contraction, retaining the source connection
and its vanishing only along the generated scalar inverseL direction. -/
theorem original_native_radial_contraction :
    (∑ a : ScalarIndex, Dphi a*L a)=(Complex.I/4:ℂ) • (U*S*Ephi) := by
  have hrow (a : ScalarIndex) :
      Dphi a*L a=(-1/4:ℂ) • (U*S*phiColumn a*P a) := by
    unfold L
    rw [←mul_assoc,(inverse_direction_commute a).eq.symm,direction_column]
    simp only [mul_smul_comm,smul_mul_assoc]
    noncomm_ring
  simp_rw [hrow]
  rw [←Finset.smul_sum]
  have hsum : (∑ a : ScalarIndex,U*S*phiColumn a*P a)=U*S*phiMomentum := by
    simp only [phiMomentum,Finset.mul_sum,mul_assoc]
  rw [hsum,phi_momentum_contraction]
  simp only [mul_smul_comm,smul_smul]
  congr 1
  ring

private theorem inverse_radius : S*rho=(1:End) := by
  apply LinearMap.ext; intro f; apply DFunLike.ext; intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem inverse_radius_square : S*rho^2=rho := by
  rw [pow_two,←mul_assoc,inverse_radius,one_mul]
private theorem lapse_pos : 0<n := by
  rw [n,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

/-- The radial 70-column source reads directly into the original K_z tester;
the 61-density and causal imaginary part are explicit, with no new premise. -/
theorem original_native_radial_pressure_link (z : ℂ) :
    (∑ a : ScalarIndex,Dphi a*L a)=
      (Complex.I/(2*(n:ℂ))) •
        (S*(pressureTester z))-
      ((z.im:ℂ)/(n:ℂ)) • rho-
      ((61*Complex.I)/8:ℂ) • (U*S) := by
  rw [original_native_radial_contraction]
  unfold pressureTester
  change (Complex.I/4:ℂ) • (U*S*Ephi)=
    (Complex.I/(2*(n:ℂ))) •
      (S*((n/2:ℂ) • (U*Phi)-(2*Complex.I*(z.im:ℂ)) • rho^2))-
    ((z.im:ℂ)/(n:ℂ)) • rho-
    ((61*Complex.I)/8:ℂ) • (U*S)
  unfold Phi SourceScalarAffineScaleTransport.generator
  have hs := inverse_phi_commute.eq
  have hn : (n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  simp only [mul_sub,mul_add,mul_smul_comm,
    SourceScalarAffineScaleTransport.phiEulerAction]
  rw [inverse_radius_square]
  have hc₁ : (Complex.I/(2*(n:ℂ)))*((n:ℂ)/2)=Complex.I/4 := by
    field_simp [hn]
    ring
  have hc₂ : (Complex.I/(2*(n:ℂ)))*(2*Complex.I*(z.im:ℂ))=
      -((z.im:ℂ)/(n:ℂ)) := by
    field_simp [hn]
    simp only [Complex.I_sq]
    ring
  have hc₃ : (Complex.I/(2*(n:ℂ)))*((n:ℂ)/2*(61/2:ℂ))=
      61*Complex.I/8 := by
    field_simp [hn]
    ring
  simp only [smul_sub,smul_add,smul_smul]
  rw [hc₁,hc₂,hc₃]
  dsimp only [Ephi,SourceScalarAffineScaleTransport.phiEulerAction]
  noncomm_ring [hs]
  module

private theorem euler_pair_shift (f g : QuantumTest) :
    sourcePair f (Ephi g)=
      -sourcePair (Ephi f) g-(61:ℂ)*sourcePair f g := by
  have h := SourceClockPhiRadiusClockSturm.phi_profile_paired_derivative
    (1:End) f g
  simpa only [Ephi,Module.End.one_apply,SourceScalarDoubleCurrent.bracket,
    mul_one,one_mul,sub_self,
    zero_add,LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right] using h

private theorem inverse_phi_pair (f g : QuantumTest) :
    sourcePair f ((U*S) g)=sourcePair ((U*S) f) g := by
  have hU (p q : QuantumTest) : sourcePair p (U q)=sourcePair (U p) q :=
    multiply_pair _ _ _ _
  have hS (p q : QuantumTest) : sourcePair p (S q)=sourcePair (S p) q :=
    multiply_pair _ _ _ _
  change sourcePair f (U (S g))=sourcePair (U (S f)) g
  rw [hU,hS]
  exact congrArg (fun v : QuantumTest => sourcePair v g)
    (LinearMap.congr_fun inverse_phi_commute.eq f).symm

/-- The original radial column has the actual affine 61-density transpose.
No self-adjointness of Dphi or of the Abel observable is used. -/
theorem original_native_radial_pair (f g : QuantumTest) :
    sourcePair f ((∑ a : ScalarIndex,Dphi a*L a) g)=
      (Complex.I/4:ℂ)*
        (-sourcePair (Ephi ((U*S) f)) g-
          (61:ℂ)*sourcePair ((U*S) f) g) := by
  rw [original_native_radial_contraction]
  change sourcePair f ((Complex.I/4:ℂ) • ((U*S) (Ephi g)))=_
  have hs : sourcePair f ((Complex.I/4:ℂ) • ((U*S) (Ephi g)))=
      (Complex.I/4:ℂ)*sourcePair f ((U*S) (Ephi g)) := by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [hs,inverse_phi_pair,euler_pair_shift]

end LowEnergy.ClockPhiNativeRadialContraction
