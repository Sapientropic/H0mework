import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarInverseBulk
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare
open SourceScalarVirialBulk SourceScalarPositiveBulkWard SourceGammaNativeBudget
open SourceScalarInverseNativeEnergy SourceHamiltonianVolume SourceMixedNativeReturn
open SourceClosedCostNativeProbe
open SourceMovingJetFlux FullYSourceResolventGraphSplice SourceRelativePowerTail
open SourceQuantumScalarChart

attribute [local irreducible] GaussDiagonalHistory.diagonalAction
  SourceScalarVirialBulk.deltaPhi SourceScalarGaugeScale.deltaGauge
  SourceHamiltonianScaleJet.scaleDerivative SourceScalarVirialBulk.positiveBulk
  inverseWeightedBulkJet inverseSymmetricScale

private theorem inverse_commutes (A : SourceScalarGaugeScale.End) (h : Commute A volumeAction) :
    Commute A inverseVolumeAction := by
  have huv : volumeAction*inverseVolumeAction=(1 : SourceScalarGaugeScale.End) := LinearMap.ext volume_inverse
  have hVU : Commute inverseVolumeAction volumeAction := real_volume _ _
  have hvu : inverseVolumeAction*volumeAction=(1 : SourceScalarGaugeScale.End) := hVU.eq.trans huv
  have hc := InverseVolumeWardAlgebra.inverse_commutator A volumeAction inverseVolumeAction huv hvu
  rw [h.eq,sub_self,mul_zero,zero_mul,neg_zero] at hc
  exact sub_eq_zero.mp hc

private theorem bulk_volume : Commute positiveBulk volumeAction := by
  rw [original_positive_bulk]
  exact ((scalar_kinetic_volume.smul_left (-8 : ℂ)).add_left
    (gauge_kinetic_volume.smul_left (36 : ℂ))).add_left
      ((real_volume _ _).smul_left (8 : ℂ))

/-- The polarized return keeps each original leg and the entire bulk. -/
theorem inverse_bulk_pair_return (f g : QuantumTest) :
    sourcePair f (inverseWeightedBulkJet inverseSymmetricScale g)=
      sourcePair (inverseVolumeAction f) (volumeAction (positiveBulk (inverseVolumeAction g))) := by
  have hc := LinearMap.congr_fun (inverse_commutes positiveBulk bulk_volume).eq g
  change positiveBulk (inverseVolumeAction g)=inverseVolumeAction (positiveBulk g) at hc
  rw [original_inverse_bulk_symmetric_jet]
  change sourcePair f (inverseVolumeAction (positiveBulk g))=
    sourcePair (inverseVolumeAction f) (volumeAction (positiveBulk (inverseVolumeAction g)))
  have hp := multiply_pair GaussNativeEnergy.volume (fun _ => volume_smooth.contDiffAt)
    (inverseVolumeAction f) (positiveBulk (inverseVolumeAction g))
  change sourcePair (inverseVolumeAction f) (volumeAction (positiveBulk (inverseVolumeAction g)))=
    sourcePair (volumeAction (inverseVolumeAction f)) (positiveBulk (inverseVolumeAction g)) at hp
  rw [volume_inverse,hc] at hp
  rw [hc]
  exact hp.symm

/-- Both original retarded legs enter the same resolved polynomial; raised defects are unchanged. -/
theorem actual_inverse_bulk_ward (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) (A B : SourceScalarGaugeScale.End) :
    sourcePair (A (state F zl hl k))
      (inverseWeightedBulkJet inverseSymmetricScale (B (state F zr hr g)))=
        resolvedBulk F zl zr hl hr g k (inverseVolumeAction*A) (inverseVolumeAction*B) := by
  have h := actual_positive_bulk_ward F zl zr hl hr g k
    (inverseVolumeAction*A) (inverseVolumeAction*B)
  have hc := inverse_bulk_pair_return (A (state F zl hl k)) (B (state F zr hr g))
  exact hc.trans h

private theorem inverse_pair_return (f g : QuantumTest) :
    sourcePair (inverseVolumeAction f) (volumeAction (inverseVolumeAction g))=
      sourcePair f (inverseVolumeAction g) := by
  rw [volume_inverse]
  exact (multiply_pair _ _ _ _).symm

/-- The signed normal form retains both raised defects and the complete complex-frequency term. -/
theorem actual_inverse_bulk_normal (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) (A B : SourceScalarGaugeScale.End) :
    resolvedBulk F zl zr hl hr g k (inverseVolumeAction*A) (inverseVolumeAction*B)=
      fixedBulk F zl zr hl hr g k (inverseVolumeAction*A) (inverseVolumeAction*B)+
      defectBulk F zl zr hl hr g k (inverseVolumeAction*A) (inverseVolumeAction*B)-
        (3*(vacuumJetCoefficient : ℂ)*(star zl+zr))*
          sourcePair (A (state F zl hl k)) (inverseVolumeAction (B (state F zr hr g))) := by
  have h := actual_positive_bulk_normal F zl zr hl hr g k
    (inverseVolumeAction*A) (inverseVolumeAction*B)
  rw [actual_positive_bulk_ward] at h
  simpa only [Module.End.mul_apply,inverse_pair_return] using! h

/-- The original coordinate moment is bounded by the whole two-leg source word, not a supplied energy budget. -/
theorem actual_inverse_ward_moment_bound (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (A : SourceScalarGaugeScale.End) :
    4*sourceTime 0*scalarMoment (A (state F z hz g)) ≤
      (resolvedBulk F z z hz hz g g (inverseVolumeAction*A) (inverseVolumeAction*A)).re+
        2*sourceTime 0*‖vacuum‖^2*‖embed (A (state F z hz g))‖^2 := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hc := mul_le_mul_of_nonneg_left (original_scalar_moment_bound (A (state F z hz g)))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hn.le)
  have hb := original_inverse_shifted_bound (A (state F z hz g))
  rw [inverseForm,actual_inverse_bulk_ward] at hb
  nlinarith only [hc,hb]

/-- The original primitive and scalar insertion consume a single resolved two-leg Ward word. -/
theorem actual_resolved_coupled_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    4*sourceTime 0*(‖embed (primitive sharp m ell (state F z hz g))‖^2+
      (sourceTime 0)^2*‖embed (scalarAction sharp (thetaAction m ell (state F z hz g)))‖^2) ≤
      2*(sourceTime 0)^2*coefficientCost sharp*
        ((resolvedBulk F z z hz hz g g (inverseVolumeAction*thetaAction m ell)
          (inverseVolumeAction*thetaAction m ell)).re+
        sourceTime 0*‖vacuum‖^2*‖embed (thetaAction m ell (state F z hz g))‖^2) := by
  have h := original_coupled_inverse_bound sharp m ell (state F z hz g)
  rw [inverseForm,actual_inverse_bulk_ward] at h
  exact h

/-- The complete Gamma plus its moving current is controlled by the same source Ward word.
Gamma here is the existing Ward response, not a decay width. -/
theorem actual_resolved_gamma_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    4*sourceTime 0*‖sourceGamma sharp m ell F g k z+Complex.I*inner ℂ (k : H)
      ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
        orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))‖^2 ≤
      ‖-96*(sourceTime 0 : ℂ)^2‖^2*‖(k : H)‖^2*‖finiteResolvent F z‖^2*coefficientCost sharp*
        ((resolvedBulk F z z hz hz g g (inverseVolumeAction*thetaAction m ell)
          (inverseVolumeAction*thetaAction m ell)).re+
        2*sourceTime 0*‖vacuum‖^2*‖embed (thetaAction m ell (state F z hz g))‖^2) := by
  let C := ‖-96*(sourceTime 0 : ℂ)^2‖^2*‖(k : H)‖^2*‖finiteResolvent F z‖^2*coefficientCost sharp
  have hC : 0 ≤ C := by
    dsimp [C,coefficientCost]
    positivity
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have h := gamma_scalar_estimate sharp m ell F g k z hz
  have hm := actual_inverse_ward_moment_bound F z hz g (thetaAction m ell)
  have hs := mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hn.le)
  have hw := mul_le_mul_of_nonneg_left hm hC
  dsimp only [C,coefficientCost] at hw
  dsimp only [state] at hm hw
  dsimp only [state,coefficientCost] at ⊢
  nlinarith only [hs,hw]

end LowEnergy.SourceScalarInverseBulk
