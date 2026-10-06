import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarCoefficientDecay
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeEnergy
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarJointEnergyBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarInverseEnergyBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussYukawaCoefficient GaussYukawaOperator
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory SourceMixedNativeReturn
open SourceGammaNativeBudget SourceScalarInverseNativeEnergy PositiveScalarWeakBudget PositiveScalarCoefficientDecay
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open FullYSourceResolventGraphSplice
open scoped InnerProductSpace ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem constant_bound (sharp : Bool) (v : Scalar) (f : QuantumTest) :
    ‖embed (constantAction sharp v f)‖^2≤‖constantBounded sharp v‖^2*‖embed f‖^2 := by
  rw [←constant_bounded_core]
  exact (pow_le_pow_left₀ (norm_nonneg _) ((constantBounded sharp v).le_opNorm (embed f)) 2).trans_eq (mul_pow _ _ _)

private theorem norm_add_square {V : Type*} [SeminormedAddCommGroup V] (x y : V) :
    ‖x+y‖^2≤2*(‖x‖^2+‖y‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

private theorem coordinate_square (f : QuantumTest) (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,scalarColumn a (scalarColumn a f)) z=
      ((‖(z.2.1 : Scalar)‖^2 : ℝ) : ℂ) • f z := by
  simp only [sum_apply]
  change (∑ a : ScalarIndex,(inner ℝ (z.2.1 : Scalar) (scalarBasis a) : ℂ) •
    ((inner ℝ (z.2.1 : Scalar) (scalarBasis a) : ℂ) • f z))=_
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  rw [scalarBasis.sum_sq_inner_left]

private theorem radius_square (f : QuantumTest) :
    radiusAction (radiusAction f)=f+(1/4 : ℂ) • ∑ a : ScalarIndex,scalarColumn a (scalarColumn a f) := by
  apply DFunLike.ext
  intro z
  change (radius z : ℂ) • ((radius z : ℂ) • f z)=f z+
    (1/4 : ℂ) • (∑ a : ScalarIndex,scalarColumn a (scalarColumn a f)) z
  rw [coordinate_square,smul_smul,smul_smul]
  conv_rhs => lhs; rw [←one_smul ℂ (f z)]
  rw [←add_smul]
  congr 1
  have hr : radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 := Real.sq_sqrt (by positivity)
  have h := congrArg (fun r : ℝ => (r : ℂ)) hr
  push_cast at h
  push_cast
  linear_combination h

/-- The original q-radius uses the full native seventy-column scalar square. -/
theorem original_radius_energy (f : QuantumTest) :
    ‖embed (radiusAction f)‖^2=‖embed f‖^2+(1/4 : ℝ)*scalarMoment f := by
  have hr : sourcePair f (radiusAction (radiusAction f))=sourcePair (radiusAction f) (radiusAction f) :=
    multiply_pair radius (fun _ => radius_smooth.contDiffAt) _ _
  have hs (a : ScalarIndex) : sourcePair f (scalarColumn a (scalarColumn a f))=
      sourcePair (scalarColumn a f) (scalarColumn a f) := by
    unfold scalarColumn SourceClosedCostNativeProbe.coordinateAction
    exact multiply_pair _ _ _ _
  rw [radius_square] at hr
  have he := congrArg Complex.re hr
  simp only [sourcePair,map_add,map_smul,map_sum,inner_add_right,inner_smul_right,inner_sum] at he
  change (sourcePair f f+(1/4 : ℂ)*∑ a : ScalarIndex,sourcePair f (scalarColumn a (scalarColumn a f))).re=_ at he
  simp_rw [hs] at he
  have hquarter (x : ℂ) : ((1/4 : ℂ)*x).re=(1/4 : ℝ)*x.re := by norm_num [Complex.mul_re]
  rw [Complex.add_re,hquarter,Complex.re_sum] at he
  change ‖embed (radiusAction f)‖^2=‖embed f‖^2+(1/4 : ℝ)*∑ a : ScalarIndex,‖embed (scalarColumn a f)‖^2
  have hdiag (q : QuantumTest) : (inner ℂ (embed q) (embed q)).re=‖embed q‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (embed q)
  simpa only [sourcePair,hdiag] using he.symm

def radiusPrice (f : QuantumTest) : ℝ :=
  inverseForm f/(16*sourceTime 0)+(1+‖vacuum‖^2/8)*‖embed f‖^2

/-- The source radius is paid by the already-generated inverse Ward form and
an ordinary Hilbert norm; no new moving radius reader remains. -/
theorem original_radius_inverse (f : QuantumTest) : ‖embed (radiusAction f)‖^2≤radiusPrice f := by
  rw [original_radius_energy]
  have hm := original_scalar_moment_bound f
  have hi := original_inverse_shifted_bound f
  unfold radiusPrice
  have hn := lapse_pos
  apply (mul_le_mul_iff_right₀ (show 0<16*sourceTime 0 by positivity)).mp
  field_simp
  nlinarith

private theorem radius_constant (sharp : Bool) (a : ScalarIndex) (f : QuantumTest) :
    radiusAction (constantAction sharp (scalarDirection a).1 f)=
      constantAction sharp (scalarDirection a).1 (radiusAction f) := by
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (sourceMap (scalarDirection a).1) (radius z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarDirection a).1) (radius z : ℂ) (f z)).symm

private theorem radius_columns (sharp : Bool) (f : QuantumTest) :
    (∑ a : ScalarIndex,‖embed (radiusAction (constantAction sharp (scalarDirection a).1 f))‖^2)≤
      coefficientCost sharp*radiusPrice f := by
  have h1 : (∑ a : ScalarIndex,‖embed (radiusAction (constantAction sharp (scalarDirection a).1 f))‖^2)≤
      coefficientCost sharp*‖embed (radiusAction f)‖^2 := by
    rw [coefficientCost,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    rw [radius_constant]
    exact constant_bound sharp (scalarBasis a) _
  apply h1.trans
  exact mul_le_mul_of_nonneg_left (original_radius_inverse f) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

def fullPrice (sharp : Bool) (f : QuantumTest) : ℝ :=
  2*(‖constantBounded sharp vacuum‖^2*‖embed f‖^2+
    coefficientCost sharp*(inverseForm f+2*sourceTime 0*‖vacuum‖^2*‖embed f‖^2)/(4*sourceTime 0))

/-- The full vacuum-plus-scalar Y on either independent branch is paid by
its genuine bounded constant part and the original inverse scalar form. -/
theorem original_full_inverse (sharp : Bool) (f : QuantumTest) :
    ‖embed (fullAction sharp f)‖^2≤fullPrice sharp f := by
  rw [full_scalar_split,LinearMap.add_apply,map_add]
  have hs : ‖embed (scalarAction sharp f)‖^2≤
      coefficientCost sharp*(inverseForm f+2*sourceTime 0*‖vacuum‖^2*‖embed f‖^2)/(4*sourceTime 0) := by
    apply (le_div_iff₀ (show 0<4*sourceTime 0 by have h := lapse_pos;positivity)).mpr
    simpa only [mul_comm] using original_scalar_inverse_bound sharp f
  exact (norm_add_square _ _).trans (mul_le_mul_of_nonneg_left
    (add_le_add (constant_bound sharp vacuum f) hs) (by norm_num))

def localPrice (sharp : Bool) (f : QuantumTest) : ℝ :=
  coefficientCost sharp*radiusPrice f+4*(Fintype.card ScalarIndex : ℝ)*fullPrice sharp f

attribute [local irreducible] coefficient fullAction scalarAction constantAction radiusAction
  inverseForm coefficientCost radiusPrice fullPrice scalarMoment

/-- The cutoff coefficient's entire seventy-row energy is now paid by the
existing inverse form and Hilbert norm, not by an additional radius/Y moment. -/
theorem original_coefficient_inverse (sharp : Bool) (m ell : ℕ) (hle : m≤ell) (f : QuantumTest) :
    (∑ a : ScalarIndex,‖embed (coefficient sharp a m ell f)‖^2)≤
      (2/(m+2 : ℝ)^2)*localPrice sharp f := by
  have hz : (∑ a : ScalarIndex,‖embed (coefficient sharp a m ell f)‖^2)≤
      ∑ a : ScalarIndex,(2/(m+2 : ℝ)^2)*
        (‖embed (radiusAction (constantAction sharp (scalarDirection a).1 f))‖^2+
          4*‖embed (fullAction sharp f)‖^2) :=
    Finset.sum_le_sum (fun a _ => original_coefficient_energy sharp a m ell hle f)
  have he : (∑ a : ScalarIndex,(2/(m+2 : ℝ)^2)*
        (‖embed (radiusAction (constantAction sharp (scalarDirection a).1 f))‖^2+
          4*‖embed (fullAction sharp f)‖^2))=
      (2/(m+2 : ℝ)^2)*((∑ a : ScalarIndex,
        ‖embed (radiusAction (constantAction sharp (scalarDirection a).1 f))‖^2)+
          4*(Fintype.card ScalarIndex : ℝ)*‖embed (fullAction sharp f)‖^2) := by
    rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const]
    simp only [Finset.card_univ,nsmul_eq_mul]
    ring
  apply (hz.trans_eq he).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hy := mul_le_mul_of_nonneg_left (original_full_inverse sharp f)
    (show 0≤4*(Fintype.card ScalarIndex : ℝ) by positivity)
  exact add_le_add (radius_columns sharp f) hy

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=
    (-(sourceTime 0 : ℂ)) • SourcePhysicalKineticSquare.inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (scalarWeight z : ℂ) • f z=
    (-(sourceTime 0 : ℂ)) • ((SourcePhysicalKineticSquare.reciprocalVolume z : ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

/-- The negative source weight moves exactly to V P. The sign becomes +i n/2,
while the two genuine coefficient branches stay independent. -/
theorem original_inverse_scalar_pair (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (SourceInverseNeutralSpinTail.scalarOnlyCurrent sharp m ell q)=
      (Complex.I*(sourceTime 0 : ℂ)/2)*
        ((∑ a : ScalarIndex,sourcePair
          (SourcePhysicalKineticSquare.inverseVolumeAction (covariantMomentum (scalarDirection a) p))
          (coefficient sharp a m ell q))+
        ∑ a : ScalarIndex,sourcePair (coefficient (!sharp) a m ell p)
          (SourcePhysicalKineticSquare.inverseVolumeAction (covariantMomentum (scalarDirection a) q))) := by
  have h1 (a : ScalarIndex) : sourcePair (covariantMomentum (scalarDirection a) p)
      (SourceScalarJointEnergyBudget.weightedCoefficient sharp a m ell q)=
      (-(sourceTime 0 : ℂ))*sourcePair
        (SourcePhysicalKineticSquare.inverseVolumeAction (covariantMomentum (scalarDirection a) p))
        (coefficient sharp a m ell q) := by
    rw [SourceScalarJointEnergyBudget.weightedCoefficient,Module.End.mul_apply,weight_inverse,LinearMap.smul_apply]
    simp only [sourcePair,map_smul,inner_smul_right]
    congr 1
    exact multiply_pair _ _ _ _
  have h2 (a : ScalarIndex) : sourcePair
      (SourceScalarJointEnergyBudget.weightedCoefficient (!sharp) a m ell p)
      (covariantMomentum (scalarDirection a) q)=
      (-(sourceTime 0 : ℂ))*sourcePair (coefficient (!sharp) a m ell p)
        (SourcePhysicalKineticSquare.inverseVolumeAction (covariantMomentum (scalarDirection a) q)) := by
    rw [SourceScalarJointEnergyBudget.weightedCoefficient,Module.End.mul_apply,weight_inverse,LinearMap.smul_apply]
    simp only [sourcePair,map_smul,inner_smul_left,map_neg,Complex.conj_ofReal]
    congr 1
    exact (multiply_pair _ _ _ _).symm
  rw [SourceScalarJointEnergyBudget.original_scalar_pair]
  simp_rw [h1,h2]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  ring

private theorem gram_bound (p q : ScalarIndex → QuantumTest) :
    ‖∑ a,sourcePair (p a) (q a)‖^2≤
      (∑ a,‖embed (p a)‖^2)*(∑ a,‖embed (q a)‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ScalarIndex)
      (fun a => sourcePair (p a) (q a))).trans
    (Finset.sum_le_sum (fun a _ => norm_inner_le_norm (embed (p a)) (embed (q a))))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖embed (p a)‖) (fun a => ‖embed (q a)‖))

private theorem n_half_add_bound (a b : ℂ) :
    ‖(Complex.I*(sourceTime 0 : ℂ)/2)*(a+b)‖^2≤
      ((sourceTime 0)^2/2)*(‖a‖^2+‖b‖^2) := by
  have hh : ‖(-Complex.I/2 : ℂ)*(a+b)‖^2≤(1/2 : ℝ)*(‖a‖^2+‖b‖^2) := by
    have h := norm_add_le a b
    rw [norm_mul,mul_pow]
    norm_num
    nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]
  have he : (Complex.I*(sourceTime 0 : ℂ)/2)*(a+b)=
      (-(sourceTime 0 : ℂ))*((-Complex.I/2 : ℂ)*(a+b)) := by ring
  rw [he,norm_mul,mul_pow,norm_neg,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans_eq (by ring)

private theorem local_price_nonnegative (sharp : Bool) (f : QuantumTest) : 0≤localPrice sharp f := by
  unfold localPrice radiusPrice fullPrice coefficientCost
  have hi := original_inverse_nonnegative f
  have hn := lapse_pos
  positivity

private theorem inverse_native_div (f : QuantumTest) :
    inverseNativeEnergy f≤ inverseForm f/(4*sourceTime 0) := by
  apply (le_div_iff₀ (show 0<4*sourceTime 0 by have hn := lapse_pos;positivity)).mpr
  simpa only [mul_comm] using original_inverse_native_bound f

/-- Both factors are existing source inverse forms plus ordinary Hilbert norms.
No additional scalar moment or higher moving derivative is required. -/
theorem original_scalar_inverse_energy (sharp : Bool) (m ell : ℕ) (hle : m≤ell) (p q : QuantumTest) :
    ‖sourcePair p (SourceInverseNeutralSpinTail.scalarOnlyCurrent sharp m ell q)‖^2≤
      (sourceTime 0/(4*(m+2 : ℝ)^2))*
        (inverseForm p*localPrice sharp q+localPrice (!sharp) p*inverseForm q) := by
  rw [original_inverse_scalar_pair]
  have h0 := (n_half_add_bound _ _).trans (mul_le_mul_of_nonneg_left
    (add_le_add (gram_bound
      (fun a => SourcePhysicalKineticSquare.inverseVolumeAction (covariantMomentum (scalarDirection a) p))
      (fun a => coefficient sharp a m ell q))
      (gram_bound (fun a => coefficient (!sharp) a m ell p)
        (fun a => SourcePhysicalKineticSquare.inverseVolumeAction (covariantMomentum (scalarDirection a) q))))
    (by positivity : (0:ℝ)≤(sourceTime 0)^2/2))
  have h1 := mul_le_mul (inverse_native_div p) (original_coefficient_inverse sharp m ell hle q)
    (by positivity : (0:ℝ)≤∑ a : ScalarIndex,‖embed (coefficient sharp a m ell q)‖^2)
    (by have hi := original_inverse_nonnegative p; have hn := lapse_pos; positivity : 0≤ inverseForm p/(4*sourceTime 0))
  have h2 := mul_le_mul (original_coefficient_inverse (!sharp) m ell hle p) (inverse_native_div q)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (by positivity) (local_price_nonnegative (!sharp) p))
  have he := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (by positivity : (0:ℝ)≤(sourceTime 0)^2/2)
  apply h0.trans (he.trans_eq _)
  field_simp [lapse_pos.ne']

/-- The same original advanced/retarded pair now consumes only its two actual
inverse Ward forms and its ordinary norm, keeping the entire source reader. -/
private theorem actual_scalar_inverse_response (sharp : Bool) (m ell : ℕ) (hle : m≤ell) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    let p := SourceScalarPositiveBulkWard.state F (star z)
      (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k
    let q := SourceScalarPositiveBulkWard.state F z hz g
    ‖inner ℂ (k : H) ((finiteResolvent F z*sourceRead F g
      (SourceInverseNeutralSpinTail.scalarOnlyCurrent sharp m ell)*finiteResolvent F z) (g : H))‖^2≤
      (sourceTime 0/(4*(m+2 : ℝ)^2))*(inverseForm p*localPrice sharp q+localPrice (!sharp) p*inverseForm q) := by
  rw [SourceInverseDefectCurrentResponse.actual_read_pair F z hz]
  exact original_scalar_inverse_energy sharp m ell hle _ _


def localPriceWithNorm (sharp : Bool) (f : QuantumTest) (N : ℝ) : ℝ :=
  coefficientCost sharp*(inverseForm f/(16*sourceTime 0)+(1+‖vacuum‖^2/8)*N)+
    4*(Fintype.card ScalarIndex : ℝ)*
      (2*(‖constantBounded sharp vacuum‖^2*N+
        coefficientCost sharp*(inverseForm f+2*sourceTime 0*‖vacuum‖^2*N)/(4*sourceTime 0)))

private theorem local_norm_mono (sharp : Bool) (f : QuantumTest) (N : ℝ) (hN : ‖embed f‖^2≤N) :
    localPrice sharp f≤localPriceWithNorm sharp f N := by
  have hn := lapse_pos
  have hC : 0≤coefficientCost sharp := by unfold coefficientCost;positivity
  have hr := add_le_add_left (mul_le_mul_of_nonneg_left hN
    (by positivity : (0:ℝ)≤1+‖vacuum‖^2/8)) (inverseForm f/(16*sourceTime 0))
  have hv := mul_le_mul_of_nonneg_left hN (sq_nonneg ‖constantBounded sharp vacuum‖)
  have hs := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (add_le_add_left (mul_le_mul_of_nonneg_left hN
      (by positivity : (0:ℝ)≤2*sourceTime 0*‖vacuum‖^2)) (inverseForm f)) hC)
    (by positivity : (0:ℝ)≤4*sourceTime 0)
  unfold localPrice radiusPrice fullPrice localPriceWithNorm
  have hr' : inverseForm f/(16*sourceTime 0)+(1+‖vacuum‖^2/8)*‖embed f‖^2≤
      inverseForm f/(16*sourceTime 0)+(1+‖vacuum‖^2/8)*N := by
    simpa only [add_comm] using hr
  have hs' : coefficientCost sharp*(inverseForm f+2*sourceTime 0*‖vacuum‖^2*‖embed f‖^2)/(4*sourceTime 0)≤
      coefficientCost sharp*(inverseForm f+2*sourceTime 0*‖vacuum‖^2*N)/(4*sourceTime 0) := by
    simpa only [add_comm] using hs
  exact add_le_add (mul_le_mul_of_nonneg_left hr' hC)
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hv hs') (by norm_num : (0:ℝ)≤2))
      (by positivity : (0:ℝ)≤4*(Fintype.card ScalarIndex : ℝ)))

private theorem state_norm_bound (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    ‖embed (SourceScalarPositiveBulkWard.state F z hz g)‖^2≤(1/|z.im|)^2*‖(g : H)‖^2 := by
  have he : embed (SourceScalarPositiveBulkWard.state F z hz g)=finiteResolvent F z (g : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [he]
  have h := ((finiteResolvent F z).le_opNorm (g : H)).trans
    (mul_le_mul_of_nonneg_right (finite_resolvent_norm F z hz) (norm_nonneg _))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (mul_pow _ _ _)

def sourcePrice (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  localPriceWithNorm sharp (SourceScalarPositiveBulkWard.state F z hz g) ((1/|z.im|)^2*‖(g : H)‖^2)

/-- Ordinary state norms are paid by the actual source resolvent. The only
remaining moving quantities are the existing inverse forms at both genuine legs. -/
theorem actual_scalar_source_inverse_response (sharp : Bool) (m ell : ℕ) (hle : m≤ell) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
    let p := SourceScalarPositiveBulkWard.state F (star z) hs k
    let q := SourceScalarPositiveBulkWard.state F z hz g
    ‖inner ℂ (k : H) ((finiteResolvent F z*sourceRead F g
      (SourceInverseNeutralSpinTail.scalarOnlyCurrent sharp m ell)*finiteResolvent F z) (g : H))‖^2≤
      (sourceTime 0/(4*(m+2 : ℝ)^2))*
        (inverseForm p*sourcePrice sharp F z hz g+sourcePrice (!sharp) F (star z) hs k*inverseForm q) := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hp := local_norm_mono (!sharp) _ _ (state_norm_bound F (star z) hs k)
  have hq := local_norm_mono sharp _ _ (state_norm_bound F z hz g)
  apply (actual_scalar_inverse_response sharp m ell hle F z hz g k).trans
  apply mul_le_mul_of_nonneg_left _ (by have hn := lapse_pos;positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left hq (original_inverse_nonnegative _))
    (mul_le_mul_of_nonneg_right hp (original_inverse_nonnegative _))

end LowEnergy.SourceScalarInverseEnergyBudget
