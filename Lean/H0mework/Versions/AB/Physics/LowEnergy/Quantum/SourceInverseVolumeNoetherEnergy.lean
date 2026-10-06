import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeRetarded
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarInverseRetardedBudget
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarInverseEnergyExchange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseNoetherEnergy
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume
open SourceScalarVirialBulk SourceScalarPositiveBulkWard SourceScalarInverseBulk
open SourceScalarInverseNativeEnergy SourceScalarInverseRetardedBudget
open SourcePhysicalKineticSquare SourcePhysicalHamiltonianSquare SourceHamiltonianScaleJet
open SourceScalarPairedTransport
open SourceScalarInverseEnergyExchange SourceGammaNativeBudget SourceMovingJetFlux
open SourceMixedNativeReturn SourceClosedCostNativeProbe SourceQuantumScalarChart
open FullYSourceResolventGraphSplice

abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def bulkAction : End := inverseVolumeAction*positiveBulk

def bulkCurrent : End := diagonalAction*bulkAction-bulkAction*diagonalAction

attribute [local irreducible] diagonalAction positiveBulk inverseVolumeAction
  inverseWeightedBulkJet inverseSymmetricScale state bulkAction bulkCurrent inverseForm
  sourcePair scalarKinetic gaugeKinetic shiftedAction defectAction compressionCore

private theorem pair_add_right (f g h : QuantumTest) :
    sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_add_left (f g h : QuantumTest) :
    sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_sub_right (f g h : QuantumTest) :
    sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_right (c : ℂ) (f g : QuantumTest) :
    sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_smul_left (c : ℂ) (f g : QuantumTest) :
    sourcePair (c • f) g=star c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left,Complex.star_def]

private theorem positive_bulk_pair (f g : QuantumTest) :
    sourcePair f (positiveBulk g)=sourcePair (positiveBulk f) g := by
  rw [original_positive_bulk]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,pair_add_right,pair_add_left,
    pair_smul_right,pair_smul_left,star_neg,star_ofNat]
  rw [scalarKinetic_pair,gaugeKinetic_pair]
  have h : sourcePair f (shiftedAction g)=sourcePair (shiftedAction f) g := by
    unfold shiftedAction
    exact multiply_pair _ _ _ _
  rw [h]

private theorem bulk_inverse : Commute positiveBulk inverseVolumeAction := by
  have hU : Commute positiveBulk volumeAction := by
    rw [original_positive_bulk]
    exact ((scalar_kinetic_volume.smul_left (-8 : ℂ)).add_left
      (gauge_kinetic_volume.smul_left (36 : ℂ))).add_left
        (by unfold shiftedAction; exact (real_volume _ _).smul_left (8 : ℂ))
  have huv : volumeAction*inverseVolumeAction=(1 : End) := LinearMap.ext volume_inverse
  have hVU : Commute inverseVolumeAction volumeAction := by
    unfold inverseVolumeAction
    exact real_volume _ _
  have hvu : inverseVolumeAction*volumeAction=(1 : End) := hVU.eq.trans huv
  have hc := InverseVolumeWardAlgebra.inverse_commutator positiveBulk volumeAction inverseVolumeAction huv hvu
  rw [hU.eq,sub_self,mul_zero,zero_mul,neg_zero] at hc
  exact sub_eq_zero.mp hc

/-- The exact inverse Ward output is formally symmetric on the original source core. -/
theorem original_bulk_pair (f g : QuantumTest) :
    sourcePair f (bulkAction g)=sourcePair (bulkAction f) g := by
  rw [bulkAction]
  change sourcePair f (inverseVolumeAction (positiveBulk g))=
    sourcePair (inverseVolumeAction (positiveBulk f)) g
  have hV : sourcePair f (inverseVolumeAction (positiveBulk g))=
      sourcePair (inverseVolumeAction f) (positiveBulk g) := by
    unfold inverseVolumeAction
    exact multiply_pair _ _ _ _
  rw [hV,positive_bulk_pair]
  exact congrArg (fun q => sourcePair q g) (LinearMap.congr_fun bulk_inverse.eq f)

theorem original_bulk_energy (f : QuantumTest) :
    (sourcePair f (bulkAction f)).re=inverseForm f := by
  rw [inverseForm,original_inverse_bulk_symmetric_jet,bulkAction]

theorem original_bulk_real (f : QuantumTest) : (sourcePair f (bulkAction f)).im=0 := by
  have h := congrArg Complex.im ((pair_conjugate f (bulkAction f)).trans (original_bulk_pair f f).symm)
  simp only [Complex.conj_im] at h
  linarith

/-- The full uncompressed action has twice the symplectic current; no real-frequency term survives. -/
theorem original_current_pair (f : QuantumTest) :
    (sourcePair f (bulkCurrent f)).im=2*(sourcePair (diagonalAction f) (bulkAction f)).im := by
  rw [bulkCurrent]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,pair_sub_right,Complex.sub_im]
  rw [diagonalAction_pair f (bulkAction f),original_bulk_pair f (diagonalAction f)]
  have h := congrArg Complex.im (pair_conjugate (diagonalAction f) (bulkAction f))
  simp only [Complex.conj_im] at h
  linarith

/-- Compression defect and the full Hamiltonian current remain one signed Noether current. -/
def noetherCurrent (F : Index) (q : QuantumTest) : ℝ :=
  (sourcePair (defectAction F q) (bulkAction q)).im-
    (1/2 : ℝ)*(sourcePair q (bulkCurrent q)).im

private theorem actual_equation (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    diagonalAction (state F z hz g)=coreEquiv.symm g+z • state F z hz g+
      defectAction F (state F z hz g) := by
  simpa only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,
    LinearMap.zero_apply,zero_add] using! actual_raised_source F z hz g (1 : End)

/-- Same F, z and g: the source equation generates the positive inverse-energy balance. -/
theorem actual_noether_balance (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    z.im*inverseForm (state F z hz g)=
      (sourcePair (coreEquiv.symm g) (bulkAction (state F z hz g))).im+
        noetherCurrent F (state F z hz g) := by
  have hc := original_current_pair (state F z hz g)
  rw [actual_equation,pair_add_left,pair_add_left,pair_smul_left] at hc
  simp only [Complex.add_im,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    original_bulk_real,mul_zero,zero_add,original_bulk_energy] at hc
  unfold noetherCurrent
  linarith

/-- The requested upper-half-plane line keeps the original source state and full signed current. -/
theorem actual_line_noether_balance (F : Index) (w μ : ℝ) (hμ : μ ≠ 0) (g : diagonal.domain) :
    μ*inverseForm (state F (SourceResolventBandLimit.line μ w)
      (by simpa only [SourceResolventBandLimit.line_im] using hμ) g)=
      (sourcePair (coreEquiv.symm g) (bulkAction (state F (SourceResolventBandLimit.line μ w)
        (by simpa only [SourceResolventBandLimit.line_im] using hμ) g))).im+
      noetherCurrent F (state F (SourceResolventBandLimit.line μ w)
        (by simpa only [SourceResolventBandLimit.line_im] using hμ) g) := by
  simpa only [SourceResolventBandLimit.line_im] using!
    actual_noether_balance F (SourceResolventBandLimit.line μ w)
      (by simpa only [SourceResolventBandLimit.line_im] using hμ) g

/-- Positivity of the original form gives the source Young square without any supplied budget. -/
theorem original_imaginary_young (u q : QuantumTest) (μ : ℝ) :
    2*μ*(sourcePair u (bulkAction q)).im ≤ inverseForm u+μ^2*inverseForm q := by
  have hn := original_inverse_nonnegative (u+((μ : ℂ)*Complex.I) • q)
  rw [←original_bulk_energy] at hn
  simp only [map_add,map_smul,pair_add_left,pair_add_right,pair_smul_left,pair_smul_right] at hn
  have hs : sourcePair q (bulkAction u)=star (sourcePair u (bulkAction q)) := by
    rw [original_bulk_pair]
    exact (pair_conjugate u (bulkAction q)).symm
  rw [hs] at hn
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    original_bulk_real,original_bulk_energy] at hn
  nlinarith

/-- The first actual energy upper: fixed input energy and one intact signed Noether current. -/
theorem actual_noether_energy_upper (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    z.im^2*inverseForm (state F z hz g) ≤ inverseForm (coreEquiv.symm g)+
      2*z.im*noetherCurrent F (state F z hz g) := by
  have hb := actual_noether_balance F z hz g
  have hy := original_imaginary_young (coreEquiv.symm g) (state F z hz g) z.im
  nlinarith only [hy,congrArg (fun a : ℝ => 2*z.im*a) hb]

/-- Localizing the state transports its full raised defect into the same current. -/
def raisedNoetherCurrent (F : Index) (A : End) (q : QuantumTest) : ℝ :=
  (sourcePair (raisedDefect F A q) (bulkAction (A q))).im-
    (1/2 : ℝ)*(sourcePair (A q) (bulkCurrent (A q))).im

theorem actual_raised_noether_balance (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g : diagonal.domain) (A : End) :
    z.im*inverseForm (A (state F z hz g))=
      (sourcePair (A (coreEquiv.symm g)) (bulkAction (A (state F z hz g)))).im+
        raisedNoetherCurrent F A (state F z hz g) := by
  have hc := original_current_pair (A (state F z hz g))
  rw [actual_raised_source,pair_add_left,pair_add_left,pair_smul_left] at hc
  simp only [Complex.add_im,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    original_bulk_real,mul_zero,zero_add,original_bulk_energy] at hc
  unfold raisedNoetherCurrent
  linarith

/-- The original cutoff input pays the localized source energy; neither defect nor current is discarded. -/
theorem actual_raised_energy_upper (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g : diagonal.domain) (A : End) :
    z.im^2*inverseForm (A (state F z hz g)) ≤ inverseForm (A (coreEquiv.symm g))+
      2*z.im*raisedNoetherCurrent F A (state F z hz g) := by
  have hb := actual_raised_noether_balance F z hz g A
  have hy := original_imaginary_young (A (coreEquiv.symm g)) (A (state F z hz g)) z.im
  nlinarith only [hy,congrArg (fun a : ℝ => 2*z.im*a) hb]

/-- The coframe flux has both inverse factors; the remaining term differentiates the actual bulk. -/
theorem original_current_source :
    bulkCurrent=(3*Complex.I*(sourceTime 0 : ℂ)/4) •
      (inverseVolumeAction*dilation*inverseVolumeAction*positiveBulk)+
      inverseVolumeAction*(diagonalAction*positiveBulk-positiveBulk*diagonalAction) := by
  calc
    bulkCurrent=(diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction)*positiveBulk+
      inverseVolumeAction*(diagonalAction*positiveBulk-positiveBulk*diagonalAction) := by
        rw [bulkCurrent,bulkAction]
        noncomm_ring
    _=_ := by rw [original_inverse_current,smul_mul_assoc]

/-- The scalar and electric kinetic sectors have different coefficients; their mixed current is 44. -/
theorem original_current_kinetic_source :
    bulkCurrent=(3*Complex.I*(sourceTime 0 : ℂ)/4) •
      (inverseVolumeAction*dilation*inverseVolumeAction*positiveBulk)+
      inverseVolumeAction*((44 : ℂ) • (scalarKinetic*gaugeKinetic-gaugeKinetic*scalarKinetic)-
        (8 : ℂ) • ((diagonalAction-scalarKinetic-gaugeKinetic)*scalarKinetic-
          scalarKinetic*(diagonalAction-scalarKinetic-gaugeKinetic))+
        (36 : ℂ) • ((diagonalAction-scalarKinetic-gaugeKinetic)*gaugeKinetic-
          gaugeKinetic*(diagonalAction-scalarKinetic-gaugeKinetic))+
        (8 : ℂ) • (diagonalAction*shiftedAction-shiftedAction*diagonalAction)) := by
  rw [original_current_source]
  congr 2
  rw [original_positive_bulk]
  simp only [mul_add,add_mul,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  module

/-- Keeping the defect and full current joined cancels H0 exactly and exposes the actual graded compression. -/
theorem original_noether_compression (F : Index) (q : QuantumTest) :
    noetherCurrent F q= -(sourcePair (compressionCore F q) (bulkAction q)).im := by
  rw [noetherCurrent,original_current_pair,defectAction,LinearMap.sub_apply]
  have hs : sourcePair (diagonalAction q-compressionCore F q) (bulkAction q)=
      sourcePair (diagonalAction q) (bulkAction q)-sourcePair (compressionCore F q) (bulkAction q) := by
    simp only [sourcePair,map_sub,inner_sub_left]
  rw [hs,Complex.sub_im]
  ring

/-- The raised defect cancels against the current before any estimate; the literal A C_F term remains. -/
theorem original_raised_noether_compression (F : Index) (A : End) (q : QuantumTest) :
    raisedNoetherCurrent F A q= -(sourcePair (A (compressionCore F q)) (bulkAction (A q))).im := by
  have hd : raisedDefect F A q=diagonalAction (A q)-A (compressionCore F q) := by
    simp only [raisedDefect,defectAction,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
    abel
  rw [raisedNoetherCurrent,original_current_pair,hd]
  have hs : sourcePair (diagonalAction (A q)-A (compressionCore F q)) (bulkAction (A q))=
      sourcePair (diagonalAction (A q)) (bulkAction (A q))-
        sourcePair (A (compressionCore F q)) (bulkAction (A q)) := by
    simp only [sourcePair,map_sub,inner_sub_left]
  rw [hs,Complex.sub_im]
  ring

/-- The original Gamma and moving current directly consume the source Noether upper at the same frequency. -/
theorem actual_gamma_noether_upper (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im ≠ 0) (g k : diagonal.domain) :
    z.im^2*(4*sourceTime 0*‖sourceGamma sharp m ell F g k z+Complex.I*inner ℂ (k : H)
      ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
        orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))‖^2) ≤
      ‖-96*(sourceTime 0 : ℂ)^2‖^2*‖(k : H)‖^2*‖finiteResolvent F z‖^2*coefficientCost sharp*
        (inverseForm (theta m ell (coreEquiv.symm g))+
          2*z.im*raisedNoetherCurrent F (theta m ell) (state F z hz g)+
          z.im^2*(2*sourceTime 0*‖vacuum‖^2*‖embed (theta m ell (state F z hz g))‖^2)) := by
  have hg := actual_gamma_energy_exchange sharp m ell F z hz g k
  rw [original_diagonal_energy_exchange] at hg
  have hn := actual_raised_energy_upper F z hz g (theta m ell)
  have hc : 0 ≤ coefficientCost sharp := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : 0 ≤ ‖-96*(sourceTime 0 : ℂ)^2‖^2*‖(k : H)‖^2*
      ‖finiteResolvent F z‖^2*coefficientCost sharp := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hg (sq_nonneg z.im)
  have hpaid := mul_le_mul_of_nonneg_left hn hp
  nlinarith only [hscaled,hpaid]

end LowEnergy.SourceInverseNoetherEnergy
