import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPhaseBulkSquare
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardPositivePrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualSecondPressurePositiveStorage
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeEnergy GaussNativeForm GaussLiveMomentum SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalHamiltonianSquare SourceScalarPairedTransport SourceScalarVirialBulk SourceScalarGaugeScale
open SourceClockPhiSecondBulk SourceClockPhiSecondPressure SourcePhysicalKineticSquare SourceScalarInverseBulk
open SourceScalarInverseNativeEnergy SourceClockReflectedForm ActualScalarPhaseJet ActualPhaseBulkSquare
open ActualMixedWardPositivePrice SourceScalarPositiveBulkWard SourceQuantumScalarChart
open Lean Meta Elab Term
open scoped InnerProductSpace ContDiff
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction inverseVolumeAction phaseForce phaseHamiltonianSquare
  sourcePair pressure secondBulk phaseCoefficient sourceTime vacuumConstantAction

elab "paid_second_storage%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPhaseBulkSquare 0) "LowEnergy") "ActualPhaseBulkSquare"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem second_inverse_right(A:End):
    secondJet (A*inverseVolumeAction)=secondJet A*inverseVolumeAction := by
  unfold secondJet
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    (paid_second_storage% phi_product),(paid_second_storage% gauge_product),
    inverse_phi,inverse_gauge,mul_zero,add_zero,map_sub,sub_mul]
private theorem second_inverse_left(A:End):
    secondJet (inverseVolumeAction*A)=inverseVolumeAction*secondJet A := by
  unfold secondJet
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    (paid_second_storage% phi_product),(paid_second_storage% gauge_product),
    inverse_phi,inverse_gauge,zero_mul,zero_add,map_sub,mul_sub]
private theorem force_second:
    secondJet (phaseForce*phaseForce)=(-2:ℂ) • (phaseForce*phaseForce) := by
  obtain ⟨hp,hg,_⟩:=actual_source_phase_force_weights
  unfold secondJet
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    (paid_second_storage% phi_product),(paid_second_storage% gauge_product),hp,hg,
    zero_mul,mul_zero,add_zero,sub_zero,neg_mul,mul_neg,map_add,map_neg]
  module

private theorem second_square_source:
    secondJet phaseHamiltonianSquare=
      (-(phaseCoefficient:ℂ)) • (secondJet diagonalAction*inverseVolumeAction+
        inverseVolumeAction*secondJet diagonalAction)-(4:ℂ) • (phaseForce*phaseForce) := by
  rw [actual_source_phase_square]
  simp only [map_add,map_smul,second_inverse_right,second_inverse_left,force_second,smul_smul]
  module

elab "paid_second_kinetic%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourcePhysicalKineticSquare 0) "LowEnergy") "SourcePhysicalKineticSquare"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem root_scalar:Commute inverseRootAction scalarKinetic := by
  have hp(v:GaussLiveMomentum.Ambient):Commute (covariantMomentum v) inverseRootAction :=
    (paid_second_kinetic% native_multiplier) inverseRootVolume inverse_root_volume_smooth inverse_root_native_derivative v
  have ha(v:GaussLiveMomentum.Ambient):Commute (GaussMomentumAdjoint.adjoint v) inverseRootAction :=
    (paid_second_kinetic% adjoint_multiplier) inverseRootVolume inverse_root_volume_smooth v (hp v)
  have hterm(i:ScalarIndex):Commute inverseRootAction
      (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth) := by
    change Commute inverseRootAction (GaussMomentumAdjoint.adjoint (scalarDirection i)*
      (multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection i)))
    have hw:Commute inverseRootAction (multiply scalarWeight scalarWeight_smooth) := by
      apply LinearMap.ext
      intro f
      apply DFunLike.ext
      intro z
      exact smul_comm (inverseRootVolume z:ℂ) (scalarWeight z:ℂ) (f z)
    apply sub_eq_zero.mp
    have hA:= (ha (scalarDirection i)).eq
    have hP:= (hp (scalarDirection i)).eq
    have hW:=hw.eq
    change inverseRootAction*(GaussMomentumAdjoint.adjoint (scalarDirection i)*
      (multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection i)))-
      (GaussMomentumAdjoint.adjoint (scalarDirection i)*
        (multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection i)))*inverseRootAction=0
    have hl:=congrArg (fun A:End=>A*(multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection i))) hA
    have hm:=congrArg (fun A:End=>GaussMomentumAdjoint.adjoint (scalarDirection i)*A*covariantMomentum (scalarDirection i)) hW
    have hr:=congrArg (fun A:End=>GaussMomentumAdjoint.adjoint (scalarDirection i)*multiply scalarWeight scalarWeight_smooth*A) hP
    linear_combination (norm:=noncomm_ring) -hl+hm-hr
  change Commute inverseRootAction ((1/2:ℂ) • ∑i:ScalarIndex,
    sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth)
  apply sub_eq_zero.mp
  simp only [mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul]
  have he:∑i:ScalarIndex,inverseRootAction*sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth=
      ∑i:ScalarIndex,sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth*inverseRootAction :=
    Finset.sum_congr rfl (fun i _=>(hterm i).eq)
  rw [he,sub_self]

private theorem pressure_operator_pair(f h:QuantumTest):
    sourcePair f (inverseVolumeAction (secondBulk h))=
      sourcePair (inverseRootAction f) (secondBulk (inverseRootAction h)) := by
  have hr:Commute inverseRootAction secondBulk := by
    rw [original_second_bulk_source]
    have hs:Commute inverseRootAction shiftedAction := by
      unfold shiftedAction
      exact inverse_root_real _ _
    have hb:Commute inverseRootAction magneticAction := by
      unfold magneticAction
      exact inverse_root_real _ _
    exact (((root_scalar.smul_right (-2:ℂ)).add_right
      (inverse_root_electric.smul_right (6:ℂ))).add_right
        (hs.smul_right (2:ℂ))).add_right (hb.smul_right (12:ℂ))
  rw [←inverse_root_square]
  have hp:sourcePair f (inverseRootAction (inverseRootAction (secondBulk h)))=
      sourcePair (inverseRootAction f) (inverseRootAction (secondBulk h)) := by
    unfold inverseRootAction
    exact multiply_pair _ _ _ _
  rw [hp]
  exact congrArg (sourcePair (inverseRootAction f)) (LinearMap.congr_fun hr.eq h)

private theorem real_commute(c d:SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice → ℝ)
    (hc:∀ z : GaussHistoryHilbert.physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd:∀ z : GaussHistoryHilbert.physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)

private theorem vacuum_inverse:
    inverseVolumeAction*vacuumConstantAction=
      ((sourceTime 0:ℂ)*(‖vacuum‖^2:ℂ)) • (1:End) := by
  have hc:vacuumConstantAction=((sourceTime 0:ℂ)*(‖vacuum‖^2:ℂ)) • volumeAction := by
    unfold vacuumConstantAction volumeAction
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    simp only [LinearMap.smul_apply,multiply_apply,smul_apply,smul_smul]
    change ((sourceTime 0*volume z*‖vacuum‖^2:ℝ):ℂ) • f z=
      ((sourceTime 0:ℂ)*(‖vacuum‖^2:ℂ)*(volume z:ℂ)) • f z
    push_cast
    congr 1
    ring
  have hi:inverseVolumeAction*volumeAction=(1:End) := by
    have hcomm:Commute inverseVolumeAction volumeAction := by
      unfold inverseVolumeAction volumeAction
      apply LinearMap.ext
      intro f
      apply DFunLike.ext
      intro z
      exact smul_comm (reciprocalVolume z:ℂ) (volume z:ℂ) (f z)
    rw [hcomm.eq]
    apply LinearMap.ext
    exact volume_inverse
  rw [hc,mul_smul_comm,hi]

/-- A source-owned storage keeps every positive second-pressure sector and
the phase-force square. Its norm compensation is the original vacuum. -/
def secondStorage(f:QuantumTest):ℝ := pressure f+(2/phaseCoefficient)*‖embed (phaseForce f)‖^2

theorem actual_second_storage_nonnegative(f:QuantumTest):0 ≤ secondStorage f := by
  have hc:=actual_phase_coefficient_positive
  have hs:=original_second_pressure_payment f
  have hn:0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hscalar:0 ≤ scalarForm (inverseVolumeAction f):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hshift:0 ≤ shiftedMoment f:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hp:0 ≤ pressure f:=by nlinarith only [hs,hn,hscalar,hshift]
  unfold secondStorage
  exact add_nonneg hp (mul_nonneg (by positivity) (sq_nonneg _))

private theorem second_bulk_pair(f h:QuantumTest):
    sourcePair f (secondBulk h)=sourcePair (secondBulk f) h := by
  rw [original_second_bulk_source]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,
    inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,map_ofNat,map_neg]
  have hs:=scalarKinetic_pair f h
  have hg:=gaugeKinetic_pair f h
  have ht:sourcePair f (shiftedAction h)=sourcePair (shiftedAction f) h := by
    unfold shiftedAction
    exact multiply_pair _ _ _ _
  have hm:sourcePair f (magneticAction h)=sourcePair (magneticAction f) h := by
    unfold magneticAction
    exact multiply_pair _ _ _ _
  simp only [sourcePair] at hs hg ht hm
  rw [hs,hg,ht,hm]

private theorem second_current_pair(f:QuantumTest):
    (sourcePair f ((secondJet diagonalAction*inverseVolumeAction+
      inverseVolumeAction*secondJet diagonalAction) f)).re=
      2*pressure f-sourceTime 0*‖vacuum‖^2*‖embed f‖^2 := by
  have hS:secondJet diagonalAction=secondBulk-(1/2:ℂ) • vacuumConstantAction := by
    unfold secondBulk
    module
  have hp:sourcePair f ((secondBulk*inverseVolumeAction) f)=
      star (sourcePair f ((inverseVolumeAction*secondBulk) f)) := by
    change sourcePair f (secondBulk (inverseVolumeAction f))=_
    rw [second_bulk_pair]
    have hu:sourcePair (secondBulk f) (inverseVolumeAction f)=
        sourcePair (inverseVolumeAction (secondBulk f)) f := by
      unfold inverseVolumeAction
      exact multiply_pair _ _ _ _
    rw [hu]
    exact (pair_conjugate _ _).symm
  have hV:vacuumConstantAction*inverseVolumeAction=
      ((sourceTime 0:ℂ)*(‖vacuum‖^2:ℂ)) • (1:End) := by
    have hc:Commute vacuumConstantAction inverseVolumeAction := by
      unfold vacuumConstantAction inverseVolumeAction
      exact real_commute _ _ _ _
    exact hc.eq.trans vacuum_inverse
  rw [hS]
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,vacuum_inverse,hV,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    sourcePair,map_add,map_sub,map_smul,inner_add_right,inner_sub_right,inner_smul_right,Complex.add_re,Complex.sub_re]
  simp only [←mul_assoc]
  have hpr:=congrArg Complex.re hp
  simp only [sourcePair,Complex.star_def,Complex.conj_re] at hpr
  rw [hpr]
  have he:(sourcePair f ((inverseVolumeAction*secondBulk) f)).re=pressure f := by
    unfold pressure
    exact congrArg Complex.re (pressure_operator_pair f f)
  simp only [sourcePair] at he
  rw [he]
  have hn:sourcePair f f=(‖embed f‖^2:ℂ):=by
    unfold sourcePair
    exact inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (embed f)
  simp only [sourcePair] at hn
  rw [hn]
  simp only [pow_two,←Complex.ofReal_mul]
  norm_num [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

/-- The lower source Ward field generates the actual positive storage,
with its original vacuum norm compensation retained exactly. -/
theorem actual_second_storage_source(f:QuantumTest):
    secondStorage f=(-(1/(2*phaseCoefficient)))*(sourcePair f (secondJet phaseHamiltonianSquare f)).re+
      (sourceTime 0*‖vacuum‖^2/2)*‖embed f‖^2 := by
  have h:=congrArg (fun A:End=>(sourcePair f (A f)).re) second_square_source
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,
    inner_sub_right,inner_smul_right,Complex.sub_re] at h
  have hs:=actual_phase_force_square_energy f
  change (sourcePair f ((phaseForce*phaseForce) f)).re=‖embed (phaseForce f)‖^2 at hs
  have hn:-(phaseCoefficient:ℂ)=((-phaseCoefficient:ℝ):ℂ):=by push_cast;rfl
  rw [hn] at h
  norm_num only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,
    Complex.im_ofNat,mul_zero,zero_mul,sub_zero] at h
  simp only [sourcePair] at hs
  have hp:=second_current_pair f
  simp only [sourcePair] at hp
  rw [hp,hs] at h
  unfold secondStorage
  have hc:phaseCoefficient≠0:=actual_phase_coefficient_positive.ne'
  simp only [sourcePair]
  field_simp [hc]
  nlinarith only [h]

/-- The actual lower Ward field and its original fixed vacuum create one
form operator; no positive storage certificate is supplied by a caller. -/
def secondStorageAction:End :=
  ((-(1/(2*phaseCoefficient)):ℝ):ℂ) • secondJet phaseHamiltonianSquare+
    (((sourceTime 0*‖vacuum‖^2/2:ℝ):ℂ)) • (1:End)

theorem actual_second_storage_action(f:QuantumTest):
    (sourcePair f (secondStorageAction f)).re=secondStorage f := by
  rw [actual_second_storage_source]
  unfold secondStorageAction
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    sourcePair,map_add,map_smul,inner_add_right,inner_smul_right,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hn:(inner ℂ (embed f) (embed f)).re=‖embed f‖^2:=by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
  rw [hn]

theorem actual_second_storage_native_price(f:QuantumTest):
    sourceTime 0*scalarForm (inverseVolumeAction f)+2*sourceTime 0*shiftedMoment f ≤ secondStorage f := by
  have hp:=original_second_pressure_payment f
  have hc:=actual_phase_coefficient_positive
  unfold secondStorage
  exact hp.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _)))

theorem actual_second_storage_magnetic_price(f:QuantumTest):
    12*(sourcePair (inverseRootAction f) (magneticAction (inverseRootAction f))).re ≤ secondStorage f := by
  have hn:0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hc:=actual_phase_coefficient_positive
  have hs:0 ≤ scalarForm (inverseVolumeAction f):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hv:0 ≤ shiftedMoment f:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hg:=original_gauge_kinetic_nonnegative (inverseRootAction f)
  unfold secondStorage
  rw [original_second_pressure_energy]
  have hforce:0 ≤ (2/phaseCoefficient)*‖embed (phaseForce f)‖^2:=by positivity
  nlinarith only [hn,hs,hv,hg,hforce]

theorem actual_second_source_pair(g u:QuantumTest):
    sourcePair g (secondJet phaseHamiltonianSquare u)=sourcePair (secondJet phaseHamiltonianSquare g) u := by
  have h0:=actual_phase_force_pair g (phaseForce u)
  have h1:=actual_phase_force_pair (phaseForce g) u
  have hs:=second_bulk_pair g u
  have hU:∀x y:QuantumTest,sourcePair x (inverseVolumeAction y)=sourcePair (inverseVolumeAction x) y := by
    intro x y
    unfold inverseVolumeAction
    exact multiply_pair _ _ _ _
  have h2:∀x y:QuantumTest,sourcePair x (secondJet diagonalAction y)=
      sourcePair (secondJet diagonalAction x) y := by
    intro x y
    have hV:sourcePair x (vacuumConstantAction y)=sourcePair (vacuumConstantAction x) y := by
      unfold vacuumConstantAction
      exact multiply_pair _ _ _ _
    have he:secondJet diagonalAction=secondBulk-(1/2:ℂ) • vacuumConstantAction := by
      unfold secondBulk
      module
    rw [he]
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,
      inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right]
    have hr:star (1/2:ℂ)=(1/2:ℂ):=by norm_num
    simp only [starRingEnd_apply,hr]
    have hb:=second_bulk_pair x y
    simp only [sourcePair] at hb hV
    exact congrArg₂ (fun a b:ℂ=>a-(1/2:ℂ)*b) hb hV
  rw [second_square_source]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_add,map_sub,map_smul,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right]
  have hn:star (-(phaseCoefficient:ℂ))=-(phaseCoefficient:ℂ):=by
    rw [star_neg]
    congr 1
    rw [Complex.star_def,Complex.conj_ofReal]
  simp only [starRingEnd_apply,hn,star_ofNat]
  simp only [sourcePair] at hU h2 h0 h1
  rw [hU,h2,h2,hU,h0,h1]
  ring

private theorem storage_action_pair(f h:QuantumTest):
    sourcePair f (secondStorageAction h)=sourcePair (secondStorageAction f) h := by
  have hS:=actual_second_source_pair
  unfold secondStorageAction
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,sourcePair,map_add,map_smul,
    inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  simp only [sourcePair] at hS
  rw [hS]

private theorem storage_real_young(f h:QuantumTest):
    |(sourcePair f (secondStorageAction h)).re| ≤ (secondStorage f+secondStorage h)/2 := by
  have hp:=actual_second_storage_nonnegative (f+h)
  have hm:=actual_second_storage_nonnegative (f-h)
  rw [←actual_second_storage_action] at hp
  rw [←actual_second_storage_action] at hm
  have hs:=storage_action_pair f h
  have hc:=congrArg Complex.re (pair_conjugate f (secondStorageAction h))
  rw [←storage_action_pair h f] at hc
  simp only [Complex.conj_re] at hc
  simp only [sourcePair,map_add,map_sub,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    Complex.add_re,Complex.sub_re] at hp hm
  have hf:=actual_second_storage_action f
  have hh:=actual_second_storage_action h
  simp only [sourcePair] at hf hh hc
  rw [hf,hh,←hc] at hp hm
  simp only [sourcePair]
  rw [abs_le]
  constructor <;> linarith only [hp,hm]

/-- The whole complex lower-Ward cross receives a real source Young price,
including its independent imaginary interference. -/
theorem actual_second_storage_complex_price(f h:QuantumTest):
    ‖sourcePair f (secondStorageAction h)‖ ≤ secondStorage f+secondStorage h := by
  have hr:=storage_real_young f h
  have hi:=storage_real_young f (Complex.I • h)
  have hscale:secondStorage (Complex.I • h)=secondStorage h := by
    rw [←actual_second_storage_action,←actual_second_storage_action]
    simp only [sourcePair,map_smul,inner_smul_left,inner_smul_right,Complex.conj_I]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have he:sourcePair f (secondStorageAction (Complex.I • h))=Complex.I*sourcePair f (secondStorageAction h) := by
    simp only [map_smul,sourcePair,inner_smul_right]
  rw [hscale,he] at hi
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,abs_neg] at hi
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith only [hr,hi])

/-- The actual lower Ward pressure cross is paid by its two source storages
and the original vacuum norm cross, with the source coefficient unchanged. -/
theorem actual_second_source_cross_price(f h:QuantumTest):
    ‖sourcePair f (secondJet phaseHamiltonianSquare h)‖ ≤
      2*phaseCoefficient*(secondStorage f+secondStorage h)+
        phaseCoefficient*sourceTime 0*‖vacuum‖^2*‖embed f‖*‖embed h‖ := by
  have he:secondJet phaseHamiltonianSquare=
      (-2*(phaseCoefficient:ℂ)) • secondStorageAction+
        ((phaseCoefficient*sourceTime 0*‖vacuum‖^2:ℝ):ℂ) • (1:End) := by
    unfold secondStorageAction
    simp only [smul_add,smul_smul]
    have hc:phaseCoefficient≠0:=actual_phase_coefficient_positive.ne'
    have h1:(-2*(phaseCoefficient:ℂ))*((-(1/(2*phaseCoefficient)):ℝ):ℂ)=1 := by
      push_cast
      field_simp [hc]
    have h2:(-2*(phaseCoefficient:ℂ))*((sourceTime 0*‖vacuum‖^2/2:ℝ):ℂ)+
        ((phaseCoefficient*sourceTime 0*‖vacuum‖^2:ℝ):ℂ)=0 := by
      push_cast
      ring
    rw [h1,one_smul]
    have hsum:((-2*(phaseCoefficient:ℂ))*((sourceTime 0*‖vacuum‖^2/2:ℝ):ℂ)) • (1:End)+
        ((phaseCoefficient*sourceTime 0*‖vacuum‖^2:ℝ):ℂ) • (1:End)=0 := by
      rw [←add_smul,h2,zero_smul]
    linear_combination (norm:=module) -hsum
  rw [he]
  have hp:sourcePair f (((-2*(phaseCoefficient:ℂ)) • secondStorageAction+
      ((phaseCoefficient*sourceTime 0*‖vacuum‖^2:ℝ):ℂ) • (1:End)) h)=
      (-2*(phaseCoefficient:ℂ))*sourcePair f (secondStorageAction h)+
        ((phaseCoefficient*sourceTime 0*‖vacuum‖^2:ℝ):ℂ)*sourcePair f h := by
    simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
      sourcePair,map_add,map_smul,inner_add_right,inner_smul_right]
  rw [hp]
  have hn:0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hc:=actual_phase_coefficient_positive
  have hy:=actual_second_storage_complex_price f h
  have hi:‖sourcePair f h‖≤‖embed f‖*‖embed h‖ := by
    unfold sourcePair
    exact norm_inner_le_norm (𝕜:=ℂ) _ _
  have hb:=norm_add_le ((-2*(phaseCoefficient:ℂ))*sourcePair f (secondStorageAction h))
    (((phaseCoefficient*sourceTime 0*‖vacuum‖^2:ℝ):ℂ)*sourcePair f h)
  simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hc,abs_of_pos hn,abs_of_nonneg (sq_nonneg ‖vacuum‖)] at hb
  apply hb.trans
  exact add_le_add (mul_le_mul_of_nonneg_left hy (by positivity))
    ((mul_le_mul_of_nonneg_left hi (by positivity:0 ≤ phaseCoefficient*sourceTime 0*‖vacuum‖^2)).trans_eq (by ring))

end LowEnergy.ActualSecondPressurePositiveStorage
