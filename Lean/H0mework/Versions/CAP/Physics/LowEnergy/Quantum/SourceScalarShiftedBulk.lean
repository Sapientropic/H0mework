import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceBulkTimeBalance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarShiftedBulk
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussDiagonalHistory SourceScalarPairedTransport
open GaussNativeEnergy GaussNativeForm GaussNativePotential GaussRadialMomentum
open SourceScalarOscillatorAbsorption SourceScalarVirialBulk SourceScalarPositiveBulkWard
open SourceScalarInverseNativeEnergy SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume
open SourceInverseNoetherEnergy SourceDilationRemainder SourceScalarRadialContact SourceGammaNativeBudget
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore StageNineP286LinkedActiveScalarPairingSkew
open SourcePhysicalKineticSquare StageNineP286BracketCalculus StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariationDensity
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def offsetCoefficient (z : SourceCoordinateSlice) : ℝ :=
  sourceTime 0*(inner ℝ (z.2.1 : Scalar) vacuum+‖vacuum‖^2/4-3)

private theorem offset_smooth : ContDiff ℝ ∞ offsetCoefficient :=
  contDiff_const.mul ((scalarCoordinate.contDiff.inner ℝ contDiff_const).add contDiff_const |>.sub contDiff_const)

def offsetAction : End := multiply offsetCoefficient (fun _ => offset_smooth.contDiffAt)

def scalarBulkComplete : End := scalarBulk+(8 : ℂ) • offsetAction

def scalarCurrentComplete : End := scalarHamiltonian*scalarBulkComplete-scalarBulkComplete*scalarHamiltonian

attribute [local irreducible] sourcePair diagonalAction scalarKinetic scalarBulk scalarCurrent
  scalarHamiltonian inverseForm bulkAction

private theorem inverse_vacuum (z : physicalChart) (v : Ambient) :
    inner ℝ ((inverseL z.val v).2.1 : Scalar) vacuum=inner ℝ v.1 vacuum := by
  have h := congrArg Prod.fst (inverse_right z v)
  change action (vacuum+(z.val.2.1 : Scalar)) (inverseL z.val v).1+
    ((inverseL z.val v).2.1 : Scalar)=v.1 at h
  have hs := scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm (inverseL z.val v).1))
    vacuum (vacuum+(z.val.2.1 : Scalar))
  rw [original_scalar_pairing,original_scalar_pairing] at hs
  change inner ℝ (orbit (inverseL z.val v).1) (vacuum+(z.val.2.1 : Scalar))+
    inner ℝ vacuum (action (vacuum+(z.val.2.1 : Scalar)) (inverseL z.val v).1)=0 at hs
  rw [affine_slice_constraint,zero_add] at hs
  have he := congrArg (fun y : Scalar => inner ℝ y vacuum) h
  have hz : inner ℝ (action (vacuum+(z.val.2.1 : Scalar)) (inverseL z.val v).1) vacuum=0 :=
    (real_inner_comm _ _).trans hs
  rw [inner_add_left,hz,zero_add] at he
  exact he

private theorem offset_derivative (z : physicalChart) (v : Ambient) :
    fderiv ℝ offsetCoefficient z.val (direction v z.val)=sourceTime 0*inner ℝ v.1 vacuum := by
  have h := (((scalarCoordinate.hasFDerivAt (x := z.val)).inner ℝ (hasFDerivAt_const vacuum z.val)).add_const
    (‖vacuum‖^2/4)).sub_const 3 |>.const_mul (sourceTime 0)
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ => D (direction v z.val)) h.fderiv
  change fderiv ℝ offsetCoefficient z.val (direction v z.val)=_ at he
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,fderivInnerCLM_apply,smul_apply,zero_apply,
    smul_eq_mul,inner_zero_right,zero_add] at he
  change _=sourceTime 0*inner ℝ ((inverseL z.val v).2.1 : Scalar) vacuum at he
  rw [inverse_vacuum] at he
  exact he

private theorem real_fock_smul (r : ℝ) (f : FockFiber) : r • f=(r : ℂ) • f := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul

/-- The original vacuum shift has an exact constant native force, before any state estimate. -/
theorem original_offset_momentum (v : Ambient) :
    covariantMomentum v*offsetAction-offsetAction*covariantMomentum v=
      (-Complex.I*(sourceTime 0 : ℂ)*(inner ℝ v.1 vacuum : ℂ)) • (1 : End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have hv : (offsetAction f : SourceCoordinateSlice → FockFiber)=fun x => offsetCoefficient x • f x := by
      funext x
      exact (real_fock_smul _ _).symm
    have hd : directional v (offsetAction f) z=(offsetCoefficient z : ℂ) • directional v f z+
        ((sourceTime 0*inner ℝ v.1 vacuum : ℝ) : ℂ) • f z := by
      rw [directional_apply,hv,fderiv_fun_smul (offset_smooth.differentiable (by simp)).differentiableAt
        (f.contDiff.differentiable (by simp)).differentiableAt]
      change offsetCoefficient z • fderiv ℝ f z (direction v z)+
        fderiv ℝ offsetCoefficient z (direction v z) • f z=_
      rw [offset_derivative ⟨z,hz⟩,real_fock_smul,real_fock_smul]
      rfl
    change (-Complex.I) • (directional v (offsetAction f) z+connection v z ((offsetCoefficient z : ℂ) • f z))-
      (offsetCoefficient z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))=_
    rw [hd,map_smul,Complex.ofReal_mul]
    change _=(-Complex.I*(sourceTime 0 : ℂ)*(inner ℝ v.1 vacuum : ℂ)) • f z
    module
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem offset_volume : inverseVolumeAction*(shiftedAction-localAction)=offsetAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have hv : scalarField z-(1/2 : ℝ) • vacuum=(z.2.1 : Scalar)+(1/2 : ℝ) • vacuum := by
      unfold scalarField
      module
    have he : shiftedPotential z-localPotential z=volume z*offsetCoefficient z := by
      unfold shiftedPotential localPotential offsetCoefficient GaussCoframeForm.volumePotential
      rw [hv,norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,real_inner_self_eq_norm_sq]
      norm_num
      ring
    change (reciprocalVolume z : ℂ) • (((shiftedPotential z : ℂ) • f z)-((localPotential z : ℂ) • f z))=
      (offsetCoefficient z : ℂ) • f z
    rw [←sub_smul,←Complex.ofReal_sub,he,smul_smul,←Complex.ofReal_mul]
    have hc : reciprocalVolume z*(volume z*offsetCoefficient z)=offsetCoefficient z := by
      unfold reciprocalVolume
      field_simp [(volume_pos ⟨z,hz⟩).ne']
    rw [hc]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

/-- Completing the actual scalar bulk removes its entire vacuum-shift remainder; only the original electric bulk remains. -/
theorem original_bulk_complete_split :
    bulkAction=scalarBulkComplete+(36 : ℂ) • (inverseVolumeAction*gaugeKinetic) := by
  rw [bulkAction,original_positive_bulk,scalarBulkComplete,scalarBulk,←offset_volume]
  simp only [mul_add,mul_smul_comm,mul_sub]
  module

private theorem pair_add_left (f g h : QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_sub_right (f g h : QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_left (c : ℂ) (f g : QuantumTest) : sourcePair (c • f) g=star c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_right (c : ℂ) (f g : QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem offset_pair (f g : QuantumTest) : sourcePair f (offsetAction g)=sourcePair (offsetAction f) g :=
  multiply_pair _ _ _ _

private theorem adjoint_offset (v : Ambient) :
    GaussMomentumAdjoint.adjoint v*offsetAction-offsetAction*GaussMomentumAdjoint.adjoint v=
      (-Complex.I*(sourceTime 0 : ℂ)*(inner ℝ v.1 vacuum : ℂ)) • (1 : End) := by
  let c : ℂ := -Complex.I*(sourceTime 0 : ℂ)*(inner ℝ v.1 vacuum : ℂ)
  have hc : -star c=c := by simp [c]
  have hp (f : QuantumTest) : covariantMomentum v (offsetAction f)=offsetAction (covariantMomentum v f)+c • f :=
    sub_eq_iff_eq_add.mp (LinearMap.congr_fun (original_offset_momentum v) f) |>.trans (add_comm _ _)
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (GaussMomentumAdjoint.adjoint v (offsetAction g)-offsetAction (GaussMomentumAdjoint.adjoint v g))=
    sourcePair f (c • g)
  rw [pair_sub_right,adjoint_pair,offset_pair,offset_pair,adjoint_pair,hp,pair_add_left,pair_smul_left,pair_smul_right]
  calc
    _=(-star c)*sourcePair f g := by ring
    _=c*sourcePair f g := by rw [hc]

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0 : ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (scalarWeight z : ℂ) • f z=(-(sourceTime 0 : ℂ)) • ((reciprocalVolume z : ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem real_offset (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (multiply c hc) offsetAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (offsetCoefficient z : ℂ) (f z)

def vacuumSymmetric : End := ∑ a : ScalarIndex,(inner ℝ (scalarBasis a) vacuum : ℂ) •
  (GaussMomentumAdjoint.adjoint (scalarDirection a)*inverseVolumeAction+
    inverseVolumeAction*covariantMomentum (scalarDirection a))

private theorem sandwich_offset (a : ScalarIndex) :
    sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth*offsetAction-
      offsetAction*sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth=
      (Complex.I*(sourceTime 0 : ℂ)^2*(inner ℝ (scalarBasis a) vacuum : ℂ)) •
        (GaussMomentumAdjoint.adjoint (scalarDirection a)*inverseVolumeAction+
          inverseVolumeAction*covariantMomentum (scalarDirection a)) := by
  let A := GaussMomentumAdjoint.adjoint (scalarDirection a)
  let P := covariantMomentum (scalarDirection a)
  let W := multiply scalarWeight scalarWeight_smooth
  have he : (A*W*P)*offsetAction-offsetAction*(A*W*P)=
      A*W*(P*offsetAction-offsetAction*P)+(A*offsetAction-offsetAction*A)*W*P+
        A*(W*offsetAction-offsetAction*W)*P := by noncomm_ring
  change (A*W*P)*offsetAction-offsetAction*(A*W*P)=_
  rw [he,show W*offsetAction-offsetAction*W=0 from sub_eq_zero.mpr (real_offset _ _).eq]
  dsimp only [A,P,W]
  rw [original_offset_momentum,adjoint_offset,weight_inverse]
  simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul,mul_zero,zero_mul,add_zero,smul_smul,scalarDirection]
  module

private theorem scalar_offset : scalarKinetic*offsetAction-offsetAction*scalarKinetic=
    (Complex.I*(sourceTime 0 : ℂ)^2/2) • vacuumSymmetric := by
  simp only [scalarKinetic,smul_mul_assoc,mul_smul_comm,←smul_sub,Finset.sum_mul,Finset.mul_sum,
    ←Finset.sum_sub_distrib,sandwich_offset,vacuumSymmetric,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  ring

/-- The full shifted scalar current contains the original source current and its actual constant-force return. -/
theorem original_complete_scalar_current :
    scalarCurrentComplete=scalarCurrent+(4*Complex.I*(sourceTime 0 : ℂ)^2) • vacuumSymmetric := by
  have hh : scalarHamiltonian*offsetAction-offsetAction*scalarHamiltonian=
      scalarKinetic*offsetAction-offsetAction*scalarKinetic := by
    rw [scalarHamiltonian]
    have hl := (real_offset localPotential local_smooth).eq
    change localAction*offsetAction=offsetAction*localAction at hl
    simp only [add_mul,mul_add,hl]
    abel
  have he : scalarCurrentComplete=scalarCurrent+(8 : ℂ) •
      (scalarHamiltonian*offsetAction-offsetAction*scalarHamiltonian) := by
    unfold scalarCurrentComplete scalarBulkComplete scalarCurrent
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
    module
  rw [he,hh,scalar_offset,smul_smul]
  congr 2
  ring

private def radialPair (f : QuantumTest) : ℂ :=
  ∑ a : ScalarIndex,sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) f)) (scalarColumn a f)

private theorem inverse_pair (f g : QuantumTest) :
    sourcePair f (inverseVolumeAction g)=sourcePair (inverseVolumeAction f) g := by
  unfold inverseVolumeAction
  exact multiply_pair _ _ _ _
private theorem column_pair (a : ScalarIndex) (f g : QuantumTest) :
    sourcePair f (scalarColumn a g)=sourcePair (scalarColumn a f) g := by
  unfold scalarColumn SourceClosedCostNativeProbe.coordinateAction
  exact multiply_pair _ _ _ _
private theorem pair_sum_right {ι : Type*} [Fintype ι] (f : QuantumTest) (g : ι → QuantumTest) :
    sourcePair f (∑ i,g i)=∑ i,sourcePair f (g i) := by simp only [sourcePair,map_sum,inner_sum]

private theorem radial_pair (f : QuantumTest) :
    sourcePair f ((inverseVolumeAction*(radialAdjoint+radialMomentum)) f)=radialPair f+star (radialPair f) := by
  change sourcePair f (inverseVolumeAction (radialAdjoint f+radialMomentum f))=_
  rw [inverse_pair]
  have ha : sourcePair (inverseVolumeAction f) (radialAdjoint f)=radialPair f := by
    simp only [radialAdjoint,LinearMap.sum_apply,pair_sum_right,Module.End.mul_apply,radialPair]
    apply Finset.sum_congr rfl
    intro a _
    rw [adjoint_pair]
    exact congrArg (fun q => sourcePair q (scalarColumn a f))
      (LinearMap.congr_fun (original_native_inverse_commute (scalarDirection a)).eq f)
  have hb : sourcePair (inverseVolumeAction f) (radialMomentum f)=star (radialPair f) := by
    simp only [radialMomentum,LinearMap.sum_apply,pair_sum_right,Module.End.mul_apply,radialPair,star_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [column_pair]
    have hc : scalarColumn a (inverseVolumeAction f)=inverseVolumeAction (scalarColumn a f) := by
      unfold scalarColumn SourceClosedCostNativeProbe.coordinateAction inverseVolumeAction
      apply DFunLike.ext
      intro z
      change (SourceClosedCostNativeProbe.coordinate (scalarDirection a) z : ℂ) •
        ((reciprocalVolume z : ℂ) • f z)=(reciprocalVolume z : ℂ) •
          ((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z : ℂ) • f z)
      exact smul_comm _ _ _
    rw [hc,←inverse_pair]
    exact (pair_conjugate _ _).symm
  have hs : sourcePair (inverseVolumeAction f) (radialAdjoint f+radialMomentum f)=
      sourcePair (inverseVolumeAction f) (radialAdjoint f)+sourcePair (inverseVolumeAction f) (radialMomentum f) := by
    simp only [sourcePair,map_add,inner_add_right]
  exact hs.trans (congrArg₂ (fun a b : ℂ => a+b) ha hb)

private theorem scalar_current_pair (f : QuantumTest) :
    (sourcePair f (scalarCurrent f)).im/2=16*(sourceTime 0)^2*(radialPair f).re := by
  rw [original_scalar_current]
  change (sourcePair f ((16*Complex.I*(sourceTime 0 : ℂ)^2) •
    ((inverseVolumeAction*(radialAdjoint+radialMomentum)) f))).im/2=_
  have hs (c : ℂ) (q : QuantumTest) : sourcePair f (c • q)=c*sourcePair f q := by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [hs,radial_pair]
  have hc : (16*Complex.I*(sourceTime 0 : ℂ)^2)=((16*(sourceTime 0)^2 : ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  have hr : radialPair f+star (radialPair f)=((2*(radialPair f).re : ℝ):ℂ) := by
    apply Complex.ext <;> simp
    ring
  rw [hc,hr]
  simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

private def vacuumPair (f : QuantumTest) : ℂ := ∑ a : ScalarIndex,
  (inner ℝ (scalarBasis a) vacuum : ℂ)*sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) f)) f

def quarterColumn (a : ScalarIndex) : End := scalarColumn a+
  ((inner ℝ (scalarBasis a) vacuum/4 : ℝ) : ℂ) • (1 : End)

def quarterPair (f : QuantumTest) : ℂ := ∑ a : ScalarIndex,
  sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) f)) (quarterColumn a f)

def quarterMoment (f : QuantumTest) : ℝ := ∑ a : ScalarIndex,‖embed (quarterColumn a f)‖^2

private theorem vacuum_pair (f : QuantumTest) :
    sourcePair f (vacuumSymmetric f)=vacuumPair f+star (vacuumPair f) := by
  simp only [vacuumSymmetric,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.add_apply,
    Module.End.mul_apply,pair_sum_right,pair_smul_right,vacuumPair,star_sum,star_mul,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hp : sourcePair f (GaussMomentumAdjoint.adjoint (scalarDirection a) (inverseVolumeAction f))=
      sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) f)) f := by
    rw [adjoint_pair,inverse_pair]
  have hq : sourcePair f (inverseVolumeAction (covariantMomentum (scalarDirection a) f))=
      star (sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) f)) f) :=
    (pair_conjugate _ _).symm
  simp only [sourcePair,map_add,inner_add_right] at hp hq ⊢
  rw [hp,hq]
  simp only [Complex.star_def,Complex.conj_ofReal]
  ring

private theorem quarter_pair_split (f : QuantumTest) : quarterPair f=radialPair f+(1/4 : ℂ)*vacuumPair f := by
  unfold quarterPair radialPair vacuumPair quarterColumn
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_smul_right,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  push_cast
  ring

/-- The complete source scalar current is paired with the forced quarter-vacuum column. -/
theorem original_complete_scalar_form (f : QuantumTest) :
    (sourcePair f (scalarCurrentComplete f)).im/2=16*(sourceTime 0)^2*(quarterPair f).re := by
  rw [original_complete_scalar_current]
  have hadd : sourcePair f ((scalarCurrent+(4*Complex.I*(sourceTime 0 : ℂ)^2) • vacuumSymmetric) f)=
      sourcePair f (scalarCurrent f)+(4*Complex.I*(sourceTime 0 : ℂ)^2)*sourcePair f (vacuumSymmetric f) := by
    simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,inner_add_right,inner_smul_right]
  rw [hadd,Complex.add_im,add_div,scalar_current_pair,vacuum_pair,quarter_pair_split]
  have algebra (n : ℝ) (a b : ℂ) :
      16*n^2*a.re+((4*Complex.I*(n : ℂ)^2)*(b+star b)).im/2=
        16*n^2*(a+(1/4 : ℂ)*b).re := by
    rw [←Complex.ofReal_pow]
    simp only [Complex.mul_im,Complex.add_im,Complex.add_re,Complex.star_def,Complex.conj_re,Complex.conj_im,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
    norm_num
    ring
  exact algebra (sourceTime 0) (radialPair f) (vacuumPair f)

private theorem quarter_shifted (a : ScalarIndex) : quarterColumn a=shiftedColumn a-
    ((inner ℝ (scalarBasis a) vacuum/4 : ℝ) : ℂ) • (1 : End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (inner ℝ (z.2.1 : Scalar) (scalarBasis a) : ℂ) • f z+
    ((inner ℝ (scalarBasis a) vacuum/4 : ℝ) : ℂ) • f z=
      (shiftedCoordinate a z : ℂ) • f z-((inner ℝ (scalarBasis a) vacuum/4 : ℝ) : ℂ) • f z
  rw [←add_smul,←sub_smul,←Complex.ofReal_add,←Complex.ofReal_sub]
  congr 2
  unfold shiftedCoordinate scalarField
  rw [inner_sub_left,inner_add_left,real_inner_smul_left,real_inner_comm vacuum (scalarBasis a)]
  ring

private theorem norm_sub_square {V : Type*} [SeminormedAddCommGroup V] (x y : V) :
    ‖x-y‖^2 ≤ 2*(‖x‖^2+‖y‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

private theorem quarter_moment_bound (f : QuantumTest) :
    quarterMoment f ≤ 2*shiftedMoment f+(‖vacuum‖^2/8)*‖embed f‖^2 := by
  have h (a : ScalarIndex) : ‖embed (quarterColumn a f)‖^2 ≤
      2*(‖embed (shiftedColumn a f)‖^2+(inner ℝ (scalarBasis a) vacuum/4)^2*‖embed f‖^2) := by
    rw [quarter_shifted,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,map_sub,map_smul]
    simpa only [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs] using
      norm_sub_square (embed (shiftedColumn a f)) (((inner ℝ (scalarBasis a) vacuum/4 : ℝ) : ℂ) • embed f)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ScalarIndex)) (fun a _ => h a)
  have hc : (∑ a : ScalarIndex,(inner ℝ (scalarBasis a) vacuum/4)^2)=‖vacuum‖^2/16 := by
    have hh (a : ScalarIndex) : inner ℝ (scalarBasis a) vacuum=inner ℝ vacuum (scalarBasis a) := real_inner_comm _ _
    simp_rw [hh,div_pow]
    rw [←Finset.sum_div,scalarBasis.sum_sq_inner_left vacuum]
    norm_num
  change quarterMoment f ≤ _ at hs
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_mul,hc] at hs
  exact hs.trans_eq (by change 2*(shiftedMoment f+_)=_;ring)

private theorem quarter_pair_bound (f : QuantumTest) :
    |(quarterPair f).re| ≤ (inverseNativeEnergy f+quarterMoment f)/2 := by
  have h (a : ScalarIndex) :
      |(sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) f)) (quarterColumn a f)).re| ≤
        (‖embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))‖^2+‖embed (quarterColumn a f)‖^2)/2 := by
    have h1 := Complex.abs_re_le_norm (sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) f)) (quarterColumn a f))
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))) (embed (quarterColumn a f))
    change |(sourcePair _ _).re| ≤ _ at h1
    have hy : ‖embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))‖*‖embed (quarterColumn a f)‖ ≤
        (‖embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))‖^2+‖embed (quarterColumn a f)‖^2)/2 := by
      nlinarith [sq_nonneg (‖embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))‖-‖embed (quarterColumn a f)‖)]
    exact h1.trans (by simpa only [sourcePair] using h2.trans hy)
  unfold quarterPair
  rw [Complex.re_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun a _ => h a)).trans_eq (by
    rw [←Finset.sum_div,Finset.sum_add_distrib]
    rfl))

/-- The entire shifted scalar block is absorbed at the same source oscillator price, without a state premise. -/
theorem original_complete_scalar_bound (f : QuantumTest) :
    |(sourcePair f (scalarCurrentComplete f)).im/2| ≤
      2*sourceTime 0*inverseForm f+(sourceTime 0)^2*‖vacuum‖^2*‖embed f‖^2 := by
  rw [original_complete_scalar_form,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 16*(sourceTime 0)^2)]
  have hp := mul_le_mul_of_nonneg_left (quarter_pair_bound f) (by positivity : 0 ≤ 16*(sourceTime 0)^2)
  have hm := mul_le_mul_of_nonneg_left (quarter_moment_bound f) (by positivity : 0 ≤ 8*(sourceTime 0)^2)
  have hi := original_inverse_energy f
  have hg := original_gauge_kinetic_nonnegative (inverseRootAction f)
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  nlinarith [mul_nonneg hn.le hg]

private theorem offset_real (f : QuantumTest) :
    (offsetAction f : SourceCoordinateSlice → FockFiber)=
      fun z => offsetCoefficient z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem multiplier_commutes
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) :
    Commute (localMultiplier A smooth) (offsetAction) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (A z) (offsetCoefficient z : ℂ) (f z)

private theorem real_commutes (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (multiply c smooth) (offsetAction) := multiplier_commutes _ _

private theorem paired_commutes (A B : End)
    (pair : GaussCoframeForm.Paired B A) (hc : Commute A (offsetAction)) :
    Commute B (offsetAction) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (B (offsetAction g))=
    sourcePair f (offsetAction (B g))
  have he : A (offsetAction f)=offsetAction (A f) := LinearMap.congr_fun hc.eq f
  calc
    _=sourcePair (A f) (offsetAction g) := pair _ _
    _=sourcePair (offsetAction (A f)) g := offset_pair _ _
    _=sourcePair (A (offsetAction f)) g := congrArg (fun q => sourcePair q g) he.symm
    _=sourcePair (offsetAction f) (B g) := (pair _ _).symm
    _=_ := (offset_pair _ _).symm

private theorem offset_coframe_derivative (z : SourceCoordinateSlice) (i : Fin 6) :
    fderiv ℝ (offsetCoefficient) z (GaussCoframeCore.coframeDirection i)=0 := by
  have hd := ((offset_smooth).differentiable (by simp)).differentiableAt (x := z) |>.hasFDerivAt
  have hc : HasDerivAt (fun r : ℝ => z+r • GaussCoframeCore.coframeDirection i)
      (GaussCoframeCore.coframeDirection i) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (GaussCoframeCore.coframeDirection i) |>.const_add z
  have hh := hd.comp_hasDerivAt_of_eq 0 hc (by simp)
  have he : (fun r : ℝ => offsetCoefficient (z+r • GaussCoframeCore.coframeDirection i))=
      (fun _ => offsetCoefficient z) := by
    funext r
    simp [offsetCoefficient,GaussCoframeCore.coframeDirection]
  change HasDerivAt (fun r : ℝ => offsetCoefficient (z+r • GaussCoframeCore.coframeDirection i))
    (fderiv ℝ (offsetCoefficient) z (GaussCoframeCore.coframeDirection i)) 0 at hh
  rw [he] at hh
  exact hh.unique (hasDerivAt_const 0 _)

private theorem coframe_derivative (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (offsetAction) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoframeCore.derivative _ (offsetAction f) z=
    offsetAction (GaussCoframeCore.derivative _ f) z
  rw [GaussCoframeCore.derivative_apply,offset_real,
    fderiv_fun_smul ((offset_smooth).differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change offsetCoefficient z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
    fderiv ℝ (offsetCoefficient) z (GaussCoframeCore.coframeDirection i) • f z=_
  rw [offset_coframe_derivative,zero_smul,add_zero]
  change _=(offsetCoefficient z : ℂ) • GaussCoframeCore.derivative _ f z
  rw [GaussCoframeCore.derivative_apply]
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem coframe_momentum (i : Fin 6) :
    Commute (GaussCoframeCore.momentum i) (offsetAction) :=
  (coframe_derivative i).smul_left (-Complex.I)

private theorem coframe_adjoint (i : Fin 6) :
    Commute (GaussCoframeCore.adjoint i) (offsetAction) :=
  paired_commutes _ _ (GaussCoframeKinetic.adjoint_pair i) (coframe_momentum i)

private theorem quantum_commutes (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val) :
    Commute (GaussQuantumMultiplier.action A smooth) (offsetAction) := multiplier_commutes _ _

private theorem end_sum_commute {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (A : ι → R) (B : R)
    (h : ∀ i, Commute (A i) B) : Commute (∑ i, A i) B := by
  change (∑ i, A i)*B=B*(∑ i, A i)
  rw [Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => (h i).eq)

private theorem end_smul_commute {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (c : ℂ) (A B : R) (h : Commute A B) : Commute (c • A) B := by
  change (c • A)*B=B*(c • A)
  rw [smul_mul_assoc,mul_smul_comm,h.eq]

private theorem end_mul_commute {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A*B) C := hA.mul_left hB

private theorem end_add_commute {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A+B) C := hA.add_left hB

private theorem coframe_kinetic :
    Commute GaussCoframeKinetic.kinetic (offsetAction) := by
  change Commute (∑ i : Fin 6, ∑ j : Fin 6, GaussCoframeKinetic.term i j) (offsetAction)
  apply end_sum_commute (R := End)
  intro i
  apply end_sum_commute (R := End)
  intro j
  change Commute (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j)) (offsetAction)
  apply end_mul_commute (R := End)
  · exact coframe_adjoint i
  · apply end_mul_commute (R := End)
    · exact real_commutes _ _
    · exact coframe_momentum j

private theorem coframe_current (a : Fin 7) :
    Commute (GaussCoframeSpin.current a) (offsetAction) := quantum_commutes _ _

private theorem coframe_mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussCoframeForm.mixed i a c smooth) (offsetAction) := by
  change Commute ((1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply c smooth*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply c smooth*GaussCoframeSpin.current a))) (offsetAction)
  apply end_smul_commute (R := End)
  apply end_add_commute (R := End)
  · apply end_mul_commute (R := End)
    · exact coframe_current a
    · apply end_mul_commute (R := End)
      · exact real_commutes c smooth
      · exact coframe_momentum i
  · apply end_mul_commute (R := End)
    · exact coframe_adjoint i
    · apply end_mul_commute (R := End)
      · exact real_commutes c smooth
      · exact coframe_current a

private theorem coframe_commutes :
    Commute GaussCoframeForm.coframeAction (offsetAction) := by
  unfold GaussCoframeForm.coframeAction GaussCoframeForm.currentAction
    GaussCoframeForm.spinSquare GaussCoframeForm.numberShift
  apply end_add_commute (R := End)
  · apply end_add_commute (R := End)
    · apply end_add_commute (R := End)
      · apply end_add_commute (R := End)
        · exact coframe_kinetic
        · apply end_add_commute (R := End)
          · apply end_add_commute (R := End)
            · apply end_add_commute (R := End)
              · exact coframe_mixed _ _ _ _
              · exact coframe_mixed _ _ _ _
            · exact coframe_mixed _ _ _ _
          · exact coframe_mixed _ _ _ _
      · apply end_sum_commute (R := End)
        intro a
        apply end_smul_commute (R := End)
        change Commute (GaussCoframeSpin.current a*(multiply GaussCoframeForm.inverseVolume
          GaussCoframeForm.inverseVolume_smooth*GaussCoframeSpin.current a)) (offsetAction)
        apply end_mul_commute (R := End)
        · exact coframe_current a
        · apply end_mul_commute (R := End)
          · exact real_commutes _ _
          · exact coframe_current a
    · apply end_smul_commute (R := End)
      change Commute (GaussCoframeForm.number*multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth+
        multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth*GaussCoframeForm.number) (offsetAction)
      apply end_add_commute (R := End)
      · apply end_mul_commute (R := End)
        · exact quantum_commutes _ _
        · exact real_commutes _ _
      · apply end_mul_commute (R := End)
        · exact real_commutes _ _
        · exact quantum_commutes _ _
  · exact real_commutes _ _

private theorem matter_commutes :
    Commute GaussMatterCore.matterAction (offsetAction) := by
  unfold GaussMatterCore.matterAction
  apply end_sum_commute (R := End)
  intro i
  apply end_sum_commute (R := End)
  intro a
  exact quantum_commutes _ _

private theorem gauge_offset : Commute gaugeKinetic offsetAction := by
  have hp (i : Fin 3) (a : LieIndex) : Commute (covariantMomentum (gaugeDirection i a)) offsetAction := by
    change _*offsetAction=offsetAction*_
    apply sub_eq_zero.mp
    simpa only [gaugeDirection,inner_zero_left,Complex.ofReal_zero,mul_zero,zero_smul] using original_offset_momentum (gaugeDirection i a)
  have ha (i : Fin 3) (a : LieIndex) : Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)) offsetAction := by
    change _*offsetAction=offsetAction*_
    apply sub_eq_zero.mp
    simpa only [gaugeDirection,inner_zero_left,Complex.ofReal_zero,mul_zero,zero_smul] using adjoint_offset (gaugeDirection i a)
  unfold gaugeKinetic
  apply end_smul_commute (R := End)
  apply end_sum_commute (R := End)
  intro a
  apply end_sum_commute (R := End)
  intro i
  apply end_sum_commute (R := End)
  intro j
  change Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
    (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a))) offsetAction
  apply end_mul_commute (R := End)
  · exact ha i a
  · apply end_mul_commute (R := End)
    · exact real_offset _ _
    · exact hp j a

/-- All genuine non-scalar sectors commute with this original vacuum shift, so it is removed rather than relocated. -/
theorem original_remaining_offset : Commute remainingHamiltonian offsetAction := by
  have he : remainingHamiltonian=gaugeKinetic+multiply GaussNativePotential.potential GaussNativePotential.potential_smooth+
      GaussCoframeForm.coframeAction+GaussMatterCore.matterAction-localAction := by
    unfold remainingHamiltonian scalarHamiltonian diagonalAction GaussNativeForm.nativeAction
    abel
  rw [he]
  have hpot : Commute (multiply GaussNativePotential.potential GaussNativePotential.potential_smooth) offsetAction := real_offset _ _
  have hA := end_add_commute (R := End) _ _ _ gauge_offset hpot
  have hB := end_add_commute (R := End) _ _ _ hA coframe_commutes
  have hC := end_add_commute (R := End) _ _ _ hB matter_commutes
  have hL : Commute localAction offsetAction := by
    unfold localAction
    exact real_offset _ _
  have subc {R : Type} [Ring R] (A B C : R) (hA : Commute A C) (hB : Commute B C) :
      Commute (A-B) C := by
    change (A-B)*C=C*(A-B)
    rw [sub_mul,mul_sub,hA.eq,hB.eq]
  exact subc (R := End) _ _ _ hC hL

def remainingCurrentComplete : End :=
  remainingHamiltonian*scalarBulk-scalarBulk*remainingHamiltonian+
    (diagonalAction*((36 : ℂ) • (inverseVolumeAction*gaugeKinetic))-
      ((36 : ℂ) • (inverseVolumeAction*gaugeKinetic))*diagonalAction)

/-- The original full current now has no vacuum-offset term in its remaining sectors. -/
theorem original_complete_current_split : bulkCurrent=scalarCurrentComplete+remainingCurrentComplete := by
  have ho := original_remaining_offset.eq
  change (diagonalAction-scalarHamiltonian)*offsetAction=offsetAction*(diagonalAction-scalarHamiltonian) at ho
  rw [bulkCurrent,original_bulk_complete_split,scalarCurrentComplete,remainingCurrentComplete,scalarBulkComplete,
    remainingHamiltonian]
  simp only [mul_add,add_mul,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc] at ho ⊢
  linear_combination (norm := module) (8 : ℂ) • ho

end LowEnergy.SourceScalarShiftedBulk
