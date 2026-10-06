import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCovariantGramFlux
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCoframeVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceCovariantGramRadial
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceCoframeSpinConnection SourceCoframeCovariantAction SourceCoframeCovariantCurrent
open SourceMatterContactNative SourceMatterContactCoframe SourceCoframeVolume GaussCoframeCore
open scoped ContDiff Matrix Topology

private theorem triad_scale (z : physicalChart) (r : ℝ) (hr : r≠0) (i j : Fin 3) :
    triadInverse (r • z.val.1) i j=r⁻¹*triadInverse z.val.1 i j := by
  have h0 := ne_of_gt z.property.1
  have h2 := ne_of_gt z.property.2.1
  have h5 := ne_of_gt z.property.2.2.1
  fin_cases i <;> fin_cases j <;> simp [triadInverse,PiLp.smul_apply,smul_eq_mul] <;>
    field_simp

private theorem coframe_scale (z : physicalChart) (r : ℝ) (hr : r≠0) (k b : Fin 3) :
    coframeGram k b (scale r z.val)=r⁻¹^2*coframeGram k b z.val := by
  simp only [coframeGram,scale,triad_scale z r hr,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem scaled_square {R : Type*} [Ring R] [Algebra ℝ R] (r : ℝ) (T : R) :
    (r^2 • T)*(r^2 • T)=r^4 • (T*T) := by
  rw [smul_mul_smul]
  congr 1
  ring

private theorem weighted_commutator_zero {R : Type*} [Ring R] [Algebra ℝ R]
    (q : Fin 6 → ℝ) (B : Fin 6 → R) (G : R) (h : (∑ i,q i • B i)=0) :
    (∑ i,q i • (B i*G-G*B i))=0 := by
  simp only [smul_sub,Finset.sum_sub_distrib]
  have hl : (∑ i,q i • (B i*G))=(∑ i,q i • B i)*G := by simp only [Finset.sum_mul,smul_mul_assoc]
  have hr : (∑ i,q i • (G*B i))=G*(∑ i,q i • B i) := by simp only [Finset.mul_sum,mul_smul_comm]
  rw [hl,hr,h,mul_zero,zero_mul,sub_self]

/-- Every original contact column scales with degree minus two, so the full CAR Gram has degree minus four. -/
theorem original_gram_scale (z : physicalChart) (r : ℝ) (hr : r≠0) :
    gramFiber (scale r z.val)=r⁻¹^4 • gramFiber z.val := by
  have hc (k : Fin 3) (a : LieIndex) : contactMap k (scale r z.val) (lieBasis a)=
      r⁻¹^2 • contactMap k z.val (lieBasis a) := by
    simp only [contactMap,LinearMap.sum_apply,LinearMap.smul_apply,coframe_scale z r hr,
      Finset.smul_sum,smul_smul]
  simp only [gramFiber,hc,Finset.smul_sum]
  congr 1
  funext k
  congr 1
  funext a
  simpa only using! scaled_square r⁻¹ (contactMap k z.val (lieBasis a))

private theorem fiber_smooth (z : physicalChart) : ContDiffAt ℝ ∞ gramFiber z.val := by
  have hm (k b : Fin 3) : ContDiffAt ℝ ∞ (coframeGram k b) z.val :=
    ContDiffAt.sum (fun i _ => (triadInverse_smooth i k z).mul (triadInverse_smooth i b z))
  have hc (k : Fin 3) (a : LieIndex) :
      ContDiffAt ℝ ∞ (fun w => contactMap k w (lieBasis a)) z.val := by
    simp only [contactMap,LinearMap.sum_apply,LinearMap.smul_apply]
    exact ContDiffAt.sum (fun b _ => (hm k b).smul contDiffAt_const)
  exact ContDiffAt.sum (fun k _ => ContDiffAt.sum (fun a _ => (hc k a).mul (hc k a)))

/-- The original source Gram has an exact radial derivative on the entire physical chart. -/
theorem original_gram_radial (z : physicalChart) :
    fderiv ℝ gramFiber z.val (euler z.val)=(-4 : ℝ) • gramFiber z.val := by
  have hs : HasDerivAt (fun r : ℝ => scale r z.val) (euler z.val) 1 := by
    simpa only [scale,euler,id_eq,one_smul] using
      (((hasDerivAt_id (1 : ℝ)).smul_const z.val.1).prodMk (hasDerivAt_const 1 z.val.2))
  have h1 : scale 1 z.val=z.val := by simp [scale]
  have chain := ((fiber_smooth z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 hs h1.symm
  have power := (((hasDerivAt_id (1 : ℝ)).inv (by norm_num)).pow 4).smul_const (gramFiber z.val)
  have hp : HasDerivAt (fun r : ℝ => r⁻¹^4 • gramFiber z.val) ((-4 : ℝ) • gramFiber z.val) 1 := by
    change HasDerivAt (fun r : ℝ => r⁻¹^4 • gramFiber z.val)
      (((4 : ℝ)*1⁻¹^(4-1)*(-1/1^2)) • gramFiber z.val) 1 at power
    norm_num only [show (4 : ℝ)*1⁻¹^(4-1)*(-1/1^2)= -4 by norm_num] at power
    exact power
  have he : (fun r : ℝ => gramFiber (scale r z.val)) =ᶠ[nhds 1]
      (fun r : ℝ => r⁻¹^4 • gramFiber z.val) := by
    filter_upwards [eventually_ne_nhds (show (1 : ℝ)≠0 by norm_num)] with r hr
    exact original_gram_scale z r hr
  exact chain.unique (hp.congr_of_eventuallyEq he)

/-- The generated spin connection has no radial component. -/
theorem original_connection_radial (z : physicalChart) :
    (∑ i : Fin 6,z.val.1 i • connectionFiber i z.val)=0 := by
  have h0 := ne_of_gt z.property.1
  have h2 := ne_of_gt z.property.2.1
  have h5 := ne_of_gt z.property.2.2.1
  have hb (a : Fin 3) : (∑ i : Fin 6,z.val.1 i*spinConnection z.val.1 i a)=0 := by
    fin_cases a <;> simp [spinConnection,Fin.sum_univ_succ] <;> field_simp <;> ring
  simp only [connectionFiber,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_smul,hb,zero_smul,Finset.sum_const_zero]

/-- The same covariant Gram jet contracts to the exact original positive Gram, with no spin-connection remainder. -/
theorem original_covariant_gram_radial (f : QuantumTest) (z : physicalChart) :
    (∑ i : Fin 6,z.val.1 i • covariantGramJet i f z.val)=(-4 : ℝ) • gramAction f z.val := by
  have he : (∑ i : Fin 6,z.val.1 i • coframeDirection i)=euler z.val := by
    apply Prod.ext
    · apply PiLp.ext
      intro j
      fin_cases j <;> simp [euler,coframeDirection,Fin.sum_univ_succ]
    · simp [euler,coframeDirection,Fin.sum_univ_succ]
  simp only [original_covariant_gram_value,smul_add,Finset.sum_add_distrib]
  have hd : (∑ i : Fin 6,z.val.1 i • (fderiv ℝ gramFiber z.val (coframeDirection i)) (f z.val))=
      (-4 : ℝ) • gramAction f z.val := by
    calc
      _=(∑ i : Fin 6,fderiv ℝ gramFiber z.val (z.val.1 i • coframeDirection i)) (f z.val) := by
        simp only [map_smul,sum_apply,smul_apply]
      _=_ := by
        rw [←map_sum,he,original_gram_radial,original_contact_gram_value]
        rfl
  rw [hd]
  have hz : (∑ i : Fin 6,z.val.1 i • (Complex.I •
      ((connectionFiber i z.val*gramFiber z.val-gramFiber z.val*connectionFiber i z.val) (f z.val))))=0 := by
    have h := weighted_commutator_zero (fun i => z.val.1 i)
      (fun i => connectionFiber i z.val) (gramFiber z.val) (original_connection_radial z)
    have ha := congrArg (fun A : SourceMatterContactNative.FiberEnd => Complex.I • A (f z.val)) h
    simpa only [sum_apply,smul_apply,Finset.smul_sum,smul_comm (z.val.1 _) Complex.I,zero_apply,smul_zero] using! ha
  rw [hz,add_zero]

end LowEnergy.SourceCovariantGramRadial
