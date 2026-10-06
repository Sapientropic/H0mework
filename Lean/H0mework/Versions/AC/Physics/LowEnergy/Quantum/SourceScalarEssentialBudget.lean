import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceGeometricBulkTimeBudget
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarSignedInverseReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarEssentialBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussMatterCore GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumScalarChart
open SourcePhysicalKineticSquare SourceScalarInverseNativeEnergy SourceInverseNoetherEnergy
open SourceScalarShiftedBulk SourceScalarOscillatorAbsorption SourceScalarVirialBulk
open SourceMixedNativeReturn SourceGammaNativeBudget SourceScalarSignedInverseReturn SourceScalarInverseEnergyBudget
open GaussYukawaCoefficient GaussYukawaOperator SourceScalarPositiveBulkWard SourceScalarForceBudget
open SourceInverseNeutralSpinTail SourceDilationRemainder SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceNativeMatterCovarianceCancellation SourceUnmixedPotentialCancellation SourceMixedCurrentCancellation
open SourceHamiltonianVolume SourceScalarDoubleCurrent FullYSourceResolventGraphSplice
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] scalarBulkComplete scalarCurrentComplete bulkAction bulkCurrent inverseForm
  diagonalAction scalarKinetic gaugeKinetic matterAction inverseVolumeAction inverseRootAction state

/-- Exactly the scalar derivative and shifted-coordinate price needed by the complete signed reader. -/
def scalarEnergy (f : QuantumTest) : ℝ :=
  4*sourceTime 0*inverseNativeEnergy f+8*sourceTime 0*shiftedMoment f

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem inverse_electric_pair (f g : QuantumTest) :
    sourcePair f ((inverseVolumeAction*gaugeKinetic) g)=
      sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction g)) := by
  change sourcePair f (inverseVolumeAction (gaugeKinetic g))=_
  rw [←inverse_root_square]
  have hs (p q : QuantumTest) : sourcePair p (inverseRootAction q)=sourcePair (inverseRootAction p) q := by
    unfold inverseRootAction
    exact multiply_pair _ _ _ _
  rw [hs]
  exact congrArg (sourcePair (inverseRootAction f)) (LinearMap.congr_fun inverse_root_electric.eq g)

/-- The source scalar part is a positive core form by its actual native and shifted-column squares. -/
theorem original_scalar_energy (f : QuantumTest) :
    (sourcePair f (scalarBulkComplete f)).re=scalarEnergy f := by
  have h := congrArg (fun A : End => (sourcePair f (A f)).re) original_bulk_complete_split
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,inner_add_right,
    inner_smul_right,Complex.add_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] at h
  change (sourcePair f (bulkAction f)).re=(sourcePair f (scalarBulkComplete f)).re+
    36*(sourcePair f ((inverseVolumeAction*gaugeKinetic) f)).re at h
  rw [original_bulk_energy,inverse_electric_pair,original_inverse_energy] at h
  unfold scalarEnergy
  linarith

/-- Original formal symmetry of the smaller positive scalar form. -/
theorem original_scalar_pair (f g : QuantumTest) :
    sourcePair f (scalarBulkComplete g)=sourcePair (scalarBulkComplete f) g := by
  have h := original_bulk_pair f g
  have he (p q : QuantumTest) : sourcePair p ((inverseVolumeAction*gaugeKinetic) q)=
      sourcePair ((inverseVolumeAction*gaugeKinetic) p) q := by
    rw [inverse_electric_pair,gaugeKinetic_pair]
    have hc := congrArg (starRingEnd ℂ) (inverse_electric_pair q p)
    rw [pair_conjugate,pair_conjugate] at hc
    exact hc.symm
  rw [original_bulk_complete_split] at h
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,inner_add_right,
    inner_add_left,inner_smul_right,inner_smul_left,map_ofNat] at h
  change sourcePair f (scalarBulkComplete g)+36*sourcePair f ((inverseVolumeAction*gaugeKinetic) g)=
    sourcePair (scalarBulkComplete f) g+36*sourcePair ((inverseVolumeAction*gaugeKinetic) f) g at h
  rw [he] at h
  exact add_right_cancel h

private theorem scalar_energy_shifted (f : QuantumTest) :
    8*sourceTime 0*shiftedMoment f ≤ scalarEnergy f := by
  have hn : 0 ≤ inverseNativeEnergy f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold scalarEnergy
  nlinarith only [mul_nonneg lapse_pos.le hn]

private theorem constant_bound (sharp : Bool) (v : Scalar) (f : QuantumTest) :
    ‖embed (constantAction sharp v f)‖^2 ≤ ‖constantBounded sharp v‖^2*‖embed f‖^2 := by
  rw [←constant_bounded_core]
  exact (pow_le_pow_left₀ (norm_nonneg _) ((constantBounded sharp v).le_opNorm (embed f)) 2).trans_eq (mul_pow _ _ _)

/-- The complete independent Y/Y† branch needs only the original shifted scalar moment and an ordinary norm. -/
theorem original_full_shifted_price (sharp : Bool) (f : QuantumTest) :
    ‖embed (fullAction sharp f)‖^2 ≤ 4*coefficientCost sharp*shiftedMoment f+
      vacuumPrice sharp*‖embed f‖^2 := by
  rw [full_scalar_split,LinearMap.add_apply,map_add]
  have h0 := norm_add_le (embed (constantAction sharp vacuum f)) (embed (scalarAction sharp f))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have hc := constant_bound sharp vacuum f
  have hs := scalar_insertion_estimate sharp f
  change ‖embed (scalarAction sharp f)‖^2 ≤ coefficientCost sharp*scalarMoment f at hs
  have hm := mul_le_mul_of_nonneg_left (original_scalar_moment_bound f)
    (show 0 ≤ coefficientCost sharp from Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hy := hs.trans hm
  unfold vacuumPrice
  nlinarith only [hsq,hc,hy,sq_nonneg (‖embed (constantAction sharp vacuum f)‖-‖embed (scalarAction sharp f)‖)]

/-- The scalar energy is used for its closed oscillator evolution, without adding the unrelated electric/contact form. -/
theorem original_full_scalar_price (sharp : Bool) (f : QuantumTest) :
    ‖embed (fullAction sharp f)‖^2 ≤ coefficientCost sharp/(2*sourceTime 0)*scalarEnergy f+
      vacuumPrice sharp*‖embed f‖^2 := by
  have h := mul_le_mul_of_nonneg_left (scalar_energy_shifted f)
    (show 0 ≤ coefficientCost sharp from Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hs : 4*coefficientCost sharp*shiftedMoment f ≤
      coefficientCost sharp/(2*sourceTime 0)*scalarEnergy f := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (show 0<2*sourceTime 0 by have hn:=lapse_pos;positivity)).mpr
    nlinarith only [h]
  exact (original_full_shifted_price sharp f).trans (add_le_add hs (le_refl _))

private theorem three_square (a b c : ℂ) : ‖a+b-c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have h := (norm_sub_le (a+b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

/-- Direct complete signed reader: both source branches, actual advanced leg, fixed compression and Hardy endpoints, with only the smaller scalar energy. -/
theorem actual_complete_scalar_bound (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) :
    let p := state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k
    let q := state F z hz g
    let tq := SourceMixedNativeReturn.thetaAction m ell q
    ‖(oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (scalarOnlyRemainder sharp m ell F g z (g : H))‖^2 ≤
      3*(‖compressionProfile sharp m ell F g k z‖^2+
        (coefficientCost sharp/(2*sourceTime 0))*‖embed p‖^2*scalarEnergy tq+
        vacuumPrice sharp*‖embed p‖^2*‖embed tq‖^2+
        ‖(k : H)‖^2*‖hardyVector sharp m ell F z (g : H)‖^2) := by
  dsimp only
  rw [actual_complete_scalar_pair]
  have hy : ‖sourcePair
      (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
      (fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))‖^2 ≤
      ‖embed (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)‖^2*
      ‖embed (fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))‖^2 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) _ _) 2).trans_eq (mul_pow _ _ _)
  have hf := mul_le_mul_of_nonneg_left (original_full_scalar_price sharp
    (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))
    (sq_nonneg ‖embed (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)‖)
  have hh := (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (k : H)
    (hardyVector sharp m ell F z (g : H))) 2).trans_eq (mul_pow _ _ _)
  have h3 := three_square (compressionProfile sharp m ell F g k z)
    (sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
      (fullAction sharp (SourceMixedNativeReturn.thetaAction m ell (state F z hz g))))
    (inner ℂ (k : H) (hardyVector sharp m ell F z (g : H)))
  have hs := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (le_refl (‖compressionProfile sharp m ell F g k z‖^2)) (hy.trans hf)) hh) (by norm_num : (0:ℝ) ≤ 3)
  exact h3.trans (hs.trans_eq (by ring))

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



/-- The complete shifted scalar oscillator is paid by the scalar form itself; no electric energy is introduced. -/
theorem original_scalar_oscillator_bound (f : QuantumTest) :
    |(sourcePair f (scalarCurrentComplete f)).im/2| ≤
      2*sourceTime 0*scalarEnergy f+(sourceTime 0)^2*‖vacuum‖^2*‖embed f‖^2 := by
  rw [original_complete_scalar_form,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 16*(sourceTime 0)^2)]
  have hp := mul_le_mul_of_nonneg_left (quarter_pair_bound f) (by positivity : 0 ≤ 16*(sourceTime 0)^2)
  have hm := mul_le_mul_of_nonneg_left (quarter_moment_bound f) (by positivity : 0 ≤ 8*(sourceTime 0)^2)
  unfold scalarEnergy
  nlinarith only [hp,hm]

private theorem real_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)

private theorem matter_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute matterAction (multiply c hc) := by
  unfold matterAction
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro b _
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (GaussQuantumMultiplier.quantized (localMatrix i b z)) (c z : ℂ) (f z)

private theorem inverse_commute (A : End) (h : Commute A volumeAction) : Commute A inverseVolumeAction := by
  have hVU : Commute inverseVolumeAction volumeAction := by
    unfold inverseVolumeAction
    exact real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem scalar_bulk_commute (A : End) (hV : Commute A inverseVolumeAction)
    (hK : Commute A scalarKinetic) (hL : Commute A localAction) : Commute A scalarBulk := by
  unfold scalarBulk
  exact ((hV.mul_right hK).smul_right _).add_right ((hV.mul_right hL).smul_right _)

private theorem gauge_scalar_bulk : Commute gaugeKinetic scalarBulk :=
  scalar_bulk_commute _ (inverse_commute _ gauge_kinetic_volume)
    original_scalar_gauge_commute.symm original_gauge_local_commute

private theorem magnetic_scalar_bulk : Commute magneticAction scalarBulk := by
  apply scalar_bulk_commute
  · unfold magneticAction inverseVolumeAction
    exact real_commute _ _ _ _
  · exact original_scalar_magnetic_commute.symm
  · unfold magneticAction localAction
    exact real_commute _ _ _ _

private theorem matter_scalar_bulk : Commute matterAction scalarBulk := by
  apply scalar_bulk_commute
  · unfold inverseVolumeAction
    exact matter_real _ _
  · exact original_scalar_matter_commute.symm
  · unfold localAction
    exact matter_real _ _

private theorem source_split : diagonalAction=scalarHamiltonian+gaugeKinetic+
    magneticAction+matterAction+geometricAction := by
  have h := original_interaction_decomposition
  simp only [interactionAction,geometricAction,scalarHamiltonian] at h ⊢
  linear_combination (norm := module) h


/-- The remaining scalar source flow contains the actual whole coframe and signed spatial potential, with no electric/matter/contact current. -/
def geometricScalarCurrent : End := geometricAction*scalarBulk-scalarBulk*geometricAction

/-- The positive scalar form's full-H current deletes the complete electric, magnetic and matter sectors by their original source commutations. -/
theorem original_scalar_current_geometric :
    diagonalAction*scalarBulkComplete-scalarBulkComplete*diagonalAction=
      scalarCurrentComplete+geometricScalarCurrent := by
  have h := original_complete_current_split
  unfold bulkCurrent at h
  rw [original_bulk_complete_split] at h
  unfold remainingCurrentComplete at h
  have he : diagonalAction*scalarBulkComplete-scalarBulkComplete*diagonalAction=
      scalarCurrentComplete+(remainingHamiltonian*scalarBulk-scalarBulk*remainingHamiltonian) := by
    simp only [mul_add,add_mul] at h
    linear_combination (norm := module) h
  rw [he]
  unfold remainingHamiltonian
  rw [source_split]
  unfold geometricScalarCurrent
  simp only [add_mul,mul_add,sub_mul,mul_sub,gauge_scalar_bulk.eq,magnetic_scalar_bulk.eq,matter_scalar_bulk.eq]
  module

/-- Full original compression defect paired with the necessary scalar source form. -/
def scalarNoether (F : Index) (T : End) (q : QuantumTest) : ℝ :=
  (sourcePair (raisedDefect F T q) (scalarBulkComplete (T q))).im-
    (sourcePair (T q) ((diagonalAction*scalarBulkComplete-scalarBulkComplete*diagonalAction) (T q))).im/2

/-- This residual is the actual scalar-only geometric current, not a free energy-family premise. -/
def scalarRaised (F : Index) (T : End) (q : QuantumTest) : ℝ :=
  (sourcePair (raisedDefect F T q) (scalarBulkComplete (T q))).im-
    (sourcePair (T q) (geometricScalarCurrent (T q))).im/2

/-- Same F, actual state and complete defect: the necessary scalar price has a direct μ−2n upper bound with only its geometric current and the already paid vacuum norm. -/
theorem actual_scalar_absorption (μ : ℝ) (F : Index) (T : End) (q : QuantumTest) :
    (μ-2*sourceTime 0)*scalarEnergy (T q) ≤
      μ*scalarEnergy (T q)-scalarNoether F T q+scalarRaised F T q+
        (sourceTime 0)^2*‖vacuum‖^2*‖embed (T q)‖^2 := by
  have he : scalarNoether F T q=scalarRaised F T q-
      (sourcePair (T q) (scalarCurrentComplete (T q))).im/2 := by
    unfold scalarNoether scalarRaised
    rw [original_scalar_current_geometric]
    simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,Complex.add_im]
    ring
  rw [he]
  have hs := original_scalar_oscillator_bound (T q)
  have ha := neg_le_abs ((sourcePair (T q) (scalarCurrentComplete (T q))).im/2)
  nlinarith only [hs,ha]

end LowEnergy.SourceScalarEssentialBudget
