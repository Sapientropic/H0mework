import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeNoetherEnergy
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeNoetherChannelGap
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarDoubleCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarOscillatorAbsorption
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume
open SourceScalarVirialBulk SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy
open SourceInverseNoetherEnergy SourceScalarInverseRetardedBudget SourceScalarDoubleCurrent
open SourceScalarRadialContact SourceGammaNativeBudget SourceDilationRemainder
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def scalarHamiltonian : End := scalarKinetic+localAction
def scalarBulk : End := (-8 : ℂ) • (inverseVolumeAction*scalarKinetic)+(8 : ℂ) • (inverseVolumeAction*localAction)
def scalarCurrent : End := scalarHamiltonian*scalarBulk-scalarBulk*scalarHamiltonian

def remainingHamiltonian : End := diagonalAction-scalarHamiltonian
def remainingBulk : End := bulkAction-scalarBulk

def remainingCurrent : End :=
  remainingHamiltonian*scalarBulk-scalarBulk*remainingHamiltonian+
    (diagonalAction*remainingBulk-remainingBulk*diagonalAction)

attribute [local irreducible] scalarKinetic localAction inverseVolumeAction volumeAction
  scalarHamiltonian scalarBulk scalarCurrent bulkAction bulkCurrent diagonalAction
  inverseForm sourcePair state raisedDefect raisedNoetherCurrent

private theorem inverse_commute (A : End) (h : Commute A volumeAction) : Commute A inverseVolumeAction := by
  have hVU : Commute inverseVolumeAction volumeAction := by
    unfold inverseVolumeAction
    exact real_volume _ _
  apply LinearMap.ext
  intro f
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  have hi (q : QuantumTest) : inverseVolumeAction (volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem scalar_inverse : Commute scalarKinetic inverseVolumeAction :=
  inverse_commute scalarKinetic scalar_kinetic_volume
private theorem local_inverse : Commute localAction inverseVolumeAction := by
  apply inverse_commute
  unfold localAction
  exact real_volume _ _

/-- The native scalar oscillator current has only its genuine first-order radial rows. -/
theorem original_scalar_current :
    scalarCurrent=(16*Complex.I*(sourceTime 0 : ℂ)^2) •
      (inverseVolumeAction*(radialAdjoint+radialMomentum)) := by
  have he : scalarCurrent=(16 : ℂ) • (inverseVolumeAction*bracket scalarKinetic localAction) := by
    unfold scalarCurrent scalarHamiltonian scalarBulk bracket
    simp only [mul_add,add_mul,mul_sub,mul_smul_comm,smul_mul_assoc,←mul_assoc,scalar_inverse.eq,local_inverse.eq]
    module
  have hr : radialAdjoint+radialMomentum=(-Complex.I) •
      ((2 : ℂ) • scalarEulerAction+(61 : ℂ) • (1 : End)) := by
    rw [scalar_adjoint_contraction,scalar_native_contraction]
    module
  rw [he,original_scalar_local_current,hr]
  simp only [mul_smul_comm,smul_smul]
  congr 1
  calc 16*(sourceTime 0 : ℂ)^2 = -16*(Complex.I*Complex.I)*(sourceTime 0 : ℂ)^2 := by rw [Complex.I_mul_I];ring
       _ = _ := by ring

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

private theorem radial_pair_bound (f : QuantumTest) :
    |(radialPair f).re| ≤ (inverseNativeEnergy f+scalarMoment f)/2 := by
  have h (a : ScalarIndex) : |(sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) f)) (scalarColumn a f)).re| ≤
      (‖embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))‖^2+‖embed (scalarColumn a f)‖^2)/2 := by
    have hr := Complex.abs_re_le_norm (sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) f)) (scalarColumn a f))
    have hn := norm_inner_le_norm (𝕜 := ℂ)
      (embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))) (embed (scalarColumn a f))
    unfold sourcePair at hr
    have hy : ‖embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))‖*‖embed (scalarColumn a f)‖ ≤
        (‖embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))‖^2+‖embed (scalarColumn a f)‖^2)/2 := by
      nlinarith [sq_nonneg (‖embed (inverseVolumeAction (covariantMomentum (scalarDirection a) f))‖-‖embed (scalarColumn a f)‖)]
    unfold sourcePair
    exact (hr.trans hn).trans hy
  unfold radialPair
  rw [Complex.re_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun a _ => h a)).trans_eq (by
    rw [←Finset.sum_div,Finset.sum_add_distrib]
    rfl))

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

/-- The leading scalar current is paid by the original inverse form and a vacuum norm price. -/
theorem original_scalar_current_bound (f : QuantumTest) :
    |(sourcePair f (scalarCurrent f)).im/2| ≤
      2*sourceTime 0*inverseForm f+4*(sourceTime 0)^2*‖vacuum‖^2*‖embed f‖^2 := by
  rw [scalar_current_pair,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 16*(sourceTime 0)^2)]
  have hr := mul_le_mul_of_nonneg_left (radial_pair_bound f) (by positivity : 0 ≤ 16*(sourceTime 0)^2)
  have hm := original_scalar_moment_bound f
  have he := original_inverse_energy f
  have hg := original_gauge_kinetic_nonnegative (inverseRootAction f)
  have hn := lapse_pos
  nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 8*(sourceTime 0)^2)]

/-- All other source sectors stay in one signed word, including the mixed native curvature. -/
theorem original_current_split : bulkCurrent=scalarCurrent+remainingCurrent := by
  unfold bulkCurrent scalarCurrent remainingCurrent remainingHamiltonian remainingBulk
  noncomm_ring

def remainingRaisedCurrent (F : Index) (A : End) (q : QuantumTest) : ℝ :=
  (sourcePair (raisedDefect F A q) (bulkAction (A q))).im-
    (sourcePair (A q) (remainingCurrent (A q))).im/2

private theorem raised_current_split (F : Index) (A : End) (q : QuantumTest) :
    raisedNoetherCurrent F A q=remainingRaisedCurrent F A q-(sourcePair (A q) (scalarCurrent (A q))).im/2 := by
  rw [raisedNoetherCurrent,original_current_split]
  have hs : sourcePair (A q) ((scalarCurrent+remainingCurrent) (A q))=
      sourcePair (A q) (scalarCurrent (A q))+sourcePair (A q) (remainingCurrent (A q)) := by
    simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right]
  rw [hs,Complex.add_im,remainingRaisedCurrent]
  ring

/-- The actual nonreal source equation absorbs the scalar oscillator at μ−2n.
The full raised defect remains paired with the unchanged bulk. -/
theorem actual_raised_absorption (F : Index) (z : ℂ) (hz : z.im≠0) (hgap : 2*sourceTime 0<z.im)
    (g : diagonal.domain) (A : End) :
    (z.im-2*sourceTime 0)^2*inverseForm (A (state F z hz g)) ≤
      inverseForm (A (coreEquiv.symm g))+2*(z.im-2*sourceTime 0)*
        (remainingRaisedCurrent F A (state F z hz g)+
          4*(sourceTime 0)^2*‖vacuum‖^2*‖embed (A (state F z hz g))‖^2) := by
  let q := state F z hz g
  have hb := actual_raised_noether_balance F z hz g A
  rw [raised_current_split] at hb
  have hc := original_scalar_current_bound (A q)
  have hlo := neg_abs_le ((sourcePair (A q) (scalarCurrent (A q))).im/2)
  have hy := original_imaginary_young (A (coreEquiv.symm g)) (A q) (z.im-2*sourceTime 0)
  have h0 : 0 ≤ z.im-2*sourceTime 0 := sub_nonneg.mpr hgap.le
  have he : (z.im-2*sourceTime 0)*inverseForm (A q) ≤
      (sourcePair (A (coreEquiv.symm g)) (bulkAction (A q))).im+
      remainingRaisedCurrent F A q+4*(sourceTime 0)^2*‖vacuum‖^2*‖embed (A q)‖^2 := by
    dsimp only [q] at hc hlo ⊢
    linarith
  have hp := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0:ℝ)≤2) h0)
  nlinarith only [hp,hy]

end LowEnergy.SourceScalarOscillatorAbsorption
