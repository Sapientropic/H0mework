import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceBoundedClockNativeCore
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiNativeJointPayment
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockAbelNativeContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockAbelNativeCurvature
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceScalarPairedTransport SourceScalarDoubleCurrent
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceBoundedClockAbel
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open SourceCoframeVolume SourceLocalizedInverseFormPayment
open scoped InnerProductSpace Topology ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev L (a : ScalarIndex) : End := inverseVolumeAction*P a
private abbrev A (μ : ℝ) (F : Index) : End := BoundedClockNativeCore.abelCore μ F
private abbrev J (μ : ℝ) (F : Index) : End := BoundedClockNativeCore.currentCore μ F
private abbrev C (F : Index) : End := compressionCore F
private abbrev B : End := clockCore
private abbrev Chi : End := B*B
private abbrev N (i j : Fin 2) (m ell : ℕ) : End := BoundedClockNativeCore.nativeMetricCore i j m ell
private abbrev E (a : ScalarIndex) (i j : Fin 2) (m ell : ℕ) : End :=
  BoundedClockNativeCore.nativeColumnCore a i j m ell
attribute [local irreducible] SourceClockYukawaCubicCurrent.resolventCore finiteResolvent

private theorem pair_add_left (p q r : QuantumTest) : sourcePair (p+q) r=sourcePair p r+sourcePair q r := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_right (p q r : QuantumTest) : sourcePair p (q+r)=sourcePair p q+sourcePair p r := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_left (p q r : QuantumTest) : sourcePair (p-q) r=sourcePair p r-sourcePair q r := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_right (p q r : QuantumTest) : sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_left (c : ℂ) (p q : QuantumTest) :
    sourcePair (c • p) q=(starRingEnd ℂ c)*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_smul_right (c : ℂ) (p q : QuantumTest) : sourcePair p (c • q)=c*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_reverse_re (p q : QuantumTest) : (sourcePair p q).re=(sourcePair q p).re := by
  simpa only [Complex.conj_re] using congrArg Complex.re (GaussNativeForm.pair_conjugate p q)

private theorem real_commute (f g : SourceCoordinateSlice → ℝ)
    (hf : ∀ z : physicalChart, ContDiffAt ℝ ∞ f z.val)
    (hg : ∀ z : physicalChart, ContDiffAt ℝ ∞ g z.val) : Commute (multiply f hf) (multiply g hg) := by
  apply LinearMap.ext;intro q;apply DFunLike.ext;intro z
  exact smul_comm (f z:ℂ) (g z:ℂ) (q z)
private theorem reciprocal_right : (1+volumeAction)*(1-B)=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz : z∈physicalChart
  · have hd : (1:ℂ)+(volume z:ℂ)≠0 := by
      have hp : 0<1+volume z := by have h:=volume_pos ⟨z,hz⟩;positivity
      exact_mod_cast hp.ne'
    change (f z-(clockProfile z:ℂ) • f z)+(volume z:ℂ) • (f z-(clockProfile z:ℂ) • f z)=f z
    rw [smul_sub,smul_smul]
    have he : (1:ℂ)+(volume z:ℂ)-((clockProfile z:ℂ)+(volume z:ℂ)*(clockProfile z:ℂ))=1 := by
      unfold clockProfile
      push_cast
      field_simp [hd]
      ring
    calc _=((1:ℂ)+(volume z:ℂ)-((clockProfile z:ℂ)+(volume z:ℂ)*(clockProfile z:ℂ))) • f z := by module
         _=f z := by rw [he,one_smul]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem reciprocal_left : (1-B)*(1+volumeAction)=(1:End) := by
  have h : Commute B volumeAction := SourceHamiltonianVolume.real_volume _ _
  have hr : Commute (1-B) volumeAction := (Commute.one_left volumeAction).sub_left h
  exact ((Commute.one_right (1-B)).add_right hr).eq.trans reciprocal_right
private theorem commute_clock {T : End} (h : Commute T volumeAction) : Commute T B := by
  have ht : T*(1+volumeAction)=(1+volumeAction)*T := ((Commute.one_right T).add_right h).eq
  have he := congrArg (fun K : End=>(1-B)*K*(1-B)) ht
  have h1 : (1-B)*(T*(1+volumeAction))*(1-B)=(1-B)*T := by
    calc _=(1-B)*T*((1+volumeAction)*(1-B)) := by noncomm_ring
         _=_ := by rw [reciprocal_right,mul_one]
  have h2 : (1-B)*((1+volumeAction)*T)*(1-B)=T*(1-B) := by
    rw [←mul_assoc (1-B) (1+volumeAction),reciprocal_left,one_mul]
  rw [h1,h2] at he
  change T*B=B*T
  linear_combination (norm:=noncomm_ring) he
private theorem P_clock (a : ScalarIndex) : Commute (P a) B :=
  commute_clock (SourceHamiltonianVolume.native_momentum_volume (scalarDirection a))
private theorem L_clock (a : ScalarIndex) : Commute (L a) Chi := by
  have hU : Commute inverseVolumeAction B := real_commute _ _ _ _
  exact (hU.mul_left (P_clock a)).pow_right 2
private theorem metric_clock (i j : Fin 2) (m ell : ℕ) : Commute (N i j m ell) Chi := by
  have hr : Commute phiRadiusAction B := real_commute _ _ _ _
  have hs : Commute phiInverseAction B := real_commute _ _ _ _
  have ht : Commute (phiThetaAction m ell) B :=
    (((Commute.one_left B).sub_left hs).pow_left (m+1)).sub_left
      (((Commute.one_left B).sub_left hs).pow_left (ell+1))
  have ht2 := ht.pow_left 2
  fin_cases i <;> fin_cases j
  · exact (hr.mul_left ht2).pow_right 2
  · exact ht2.neg_left.pow_right 2
  · exact ht2.neg_left.pow_right 2
  · exact (hs.mul_left ht2).pow_right 2
private theorem column_clock (a : ScalarIndex) (i j : Fin 2) (m ell : ℕ) : Commute (E a i j m ell) Chi := by
  have hp := (P_clock a).pow_right 2
  have he := metric_clock i j m ell
  exact ((hp.mul_left he).sub_left (he.mul_left hp)).smul_left Complex.I
private theorem column_symmetric (a : ScalarIndex) (i j : Fin 2) (m ell : ℕ) :
    E a i j m ell=E a j i m ell := by fin_cases i <;> fin_cases j <;> rfl
private theorem clock_pair (p q : QuantumTest) : sourcePair (Chi p) q=sourcePair p (Chi q) := by
  change sourcePair (B (B p)) q=sourcePair p (B (B q))
  have hb (f g : QuantumTest) : sourcePair (B f) g=sourcePair f (B g) :=
    (multiply_pair _ _ _ _).symm
  rw [hb (B p) q,hb p (B q)]
private theorem abel_pair (μ : ℝ) (hμ : 0<μ) (F : Index) (p q : QuantumTest) :
    sourcePair (A μ F p) q=sourcePair p (A μ F q) := by
  have h := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (actual_bounded_clock_abel_source μ hμ F).2.1).isSymmetric
  change inner ℂ (embed (A μ F p)) (embed q)=inner ℂ (embed p) (embed (A μ F q))
  rw [BoundedClockNativeCore.abelCore_embed μ hμ F,BoundedClockNativeCore.abelCore_embed μ hμ F]
  exact h _ _
private theorem current_source (μ : ℝ) (hμ : 0<μ) (F : Index) :
    J μ F=(-Complex.I*(4*μ:ℂ)) • (A μ F-Chi) := by
  have h := congrArg (fun K : End=>(-Complex.I) • K) (BoundedClockNativeCore.currentCore_source μ hμ F)
  simp only [smul_smul] at h
  have hi : -Complex.I*Complex.I=(1:ℂ) := by rw [neg_mul,Complex.I_mul_I,neg_neg]
  rw [hi,one_smul] at h
  exact h
private theorem current_pair (μ : ℝ) (hμ : 0<μ) (F : Index) (p q : QuantumTest) :
    sourcePair (J μ F p) q= -sourcePair p (J μ F q) := by
  rw [current_source μ hμ F]
  simp only [LinearMap.smul_apply,LinearMap.sub_apply,pair_smul_left,pair_smul_right,
    pair_sub_left,pair_sub_right,abel_pair μ hμ F,clock_pair,map_mul,map_neg,
    Complex.conj_I,Complex.conj_ofReal,map_ofNat]
  ring
private theorem current_commutator (μ : ℝ) (hμ : 0<μ) (F : Index) (T : End) (hT : Commute T Chi) :
    bracket T (J μ F)=(-Complex.I*(4*μ:ℂ)) • bracket T (A μ F) := by
  rw [current_source μ hμ F]
  simp only [bracket,mul_smul_comm,smul_mul_assoc,←smul_sub,mul_sub,sub_mul,hT.eq]
  module
private theorem row_real (μ : ℝ) (hμ : 0<μ) (F : Index) (a : ScalarIndex)
    (i j : Fin 2) (m ell : ℕ) (p q : QuantumTest) :
    (sourcePair (L a (J μ F p)) (E a i j m ell q)+
      sourcePair (E a i j m ell (J μ F q)) (L a p)).re=
      (4*μ)*((sourcePair (L a p) (bracket (E a i j m ell) (A μ F) q)).im-
        (sourcePair (bracket (L a) (A μ F) p) (E a i j m ell q)).im) := by
  have hL : L a (J μ F p)=J μ F (L a p)+bracket (L a) (J μ F) p := by
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply];abel
  have hE : E a i j m ell (J μ F q)=J μ F (E a i j m ell q)+
      bracket (E a i j m ell) (J μ F) q := by
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply];abel
  rw [hL,pair_add_left,Complex.add_re,Complex.add_re,
    pair_reverse_re (E a i j m ell (J μ F q)) (L a p),hE,pair_add_right,
    Complex.add_re,current_pair μ hμ F]
  have hc : (-sourcePair (L a p) (J μ F (E a i j m ell q))).re=
      -(sourcePair (L a p) (J μ F (E a i j m ell q))).re := Complex.neg_re _
  rw [hc,current_commutator μ hμ F (L a) (L_clock a),
    current_commutator μ hμ F (E a i j m ell) (column_clock a i j m ell)]
  simp only [LinearMap.smul_apply,pair_smul_left,pair_smul_right,map_mul,map_neg,
    Complex.conj_I,Complex.conj_ofReal,map_ofNat,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.re_ofNat,Complex.im_ofNat,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,
    mul_zero,zero_sub,neg_zero,neg_neg]
  ring

private theorem sum_row_real (μ : ℝ) (hμ : 0<μ) (F : Index) (m ell : ℕ) (X : Fin 2 → QuantumTest) :
    (∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
      (sourcePair (L a (J μ F (X i))) (E a i j m ell (X j))+
       sourcePair (E a i j m ell (J μ F (X i))) (L a (X j)))).re=
    (4*μ)*((∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
      (sourcePair (L a (X i)) (bracket (E a i j m ell) (A μ F) (X j))-
       sourcePair (bracket (L a) (A μ F) (X i)) (E a i j m ell (X j)))).im) := by
  have hs : (∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
      (sourcePair (E a i j m ell (J μ F (X i))) (L a (X j))))=
      ∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
      (sourcePair (E a i j m ell (J μ F (X j))) (L a (X i))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _
    apply Finset.sum_congr rfl;intro a _
    rw [column_symmetric a j i]
  have ht : (∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
      (sourcePair (L a (J μ F (X i))) (E a i j m ell (X j))+
       sourcePair (E a i j m ell (J μ F (X i))) (L a (X j))))=
      ∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
      (sourcePair (L a (J μ F (X i))) (E a i j m ell (X j))+
       sourcePair (E a i j m ell (J μ F (X j))) (L a (X i))) := by
    simp only [Finset.sum_add_distrib]
    rw [hs]
  rw [ht]
  simp only [Complex.re_sum,row_real μ hμ F,Complex.im_sum,Complex.sub_im,Finset.mul_sum]

/-- The untouched second native half: all seventy weighted commutators share the original two seeds. -/
def curvatureHalf (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  (2*n*μ)*(∑i:Fin 2,∑a:ScalarIndex,
    sourcePair (bracket (L a) (A μ F)
      (SourceClockYukawaCubicCurrent.resolventCore F z hz (coreEquiv.symm (SourceClockPhiNativeJointPayment.inputSeed g i))))
      (∑j:Fin 2,E a i j m ell
        (SourceClockYukawaCubicCurrent.resolventCore F z hz (coreEquiv.symm (SourceClockPhiNativeJointPayment.inputSeed g j))))).im

def nativePi (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  BoundedClockNativeCore.nativePiCore μ F m ell (fun i=>
    SourceClockYukawaCubicCurrent.resolventCore F z hz (coreEquiv.symm (SourceClockPhiNativeJointPayment.inputSeed g i)))

private theorem input_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (i : Fin 2) :
    embed (SourceClockYukawaCubicCurrent.resolventCore F z hz
      (coreEquiv.symm (SourceClockPhiNativeJointPayment.inputSeed g i)))=
      finiteResolvent F z (SourceClockPhiNativeJointPayment.inputSeed g i:H) := by
  simp only [SourceClockYukawaCubicCurrent.resolventCore,LinearMap.coe_mk,AddHom.coe_mk,
    SourceScalarPositiveBulkWard.state,coreEquiv.apply_symm_apply]
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem E_embed (a : ScalarIndex) (i j : Fin 2) (m ell : ℕ) (f : QuantumTest) :
    embed (E a i j m ell f)=SourceClockPhiNativeJointPayment.nativeColumn a i j m ell (embed f) :=
  (SourceClockPhiNativeJointPayment.actual_native_column_core a i j m ell f).symm
private theorem EA_embed (μ : ℝ) (hμ : 0<μ) (F : Index) (a : ScalarIndex)
    (i j : Fin 2) (m ell : ℕ) (f : QuantumTest) :
    embed (bracket (E a i j m ell) (A μ F) f)=
      SourceClockPhiNativeJointPayment.nativeColumn a i j m ell (abelObservable μ F (embed f))-
        abelObservable μ F (SourceClockPhiNativeJointPayment.nativeColumn a i j m ell (embed f)) := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub,E_embed,
    BoundedClockNativeCore.abelCore_embed μ hμ F]

/-- The complete original native row consumes the paid half without adding a new pressure debit. -/
theorem actual_native_curvature_return (μ : ℝ) (hμ : 0<μ) (m ell : ℕ)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    nativePi m ell μ F z hz g+curvatureHalf m ell μ F z hz g=
      SourceClockPhiNativeJointPayment.nativeHalf m ell μ F z hz g := by
  let X : Fin 2 → QuantumTest := fun i=>SourceClockYukawaCubicCurrent.resolventCore F z hz
    (coreEquiv.symm (SourceClockPhiNativeJointPayment.inputSeed g i))
  have hw := BoundedClockNativeCore.whole_native_U_row μ F m ell X
  have hr := sum_row_real μ hμ F m ell X
  have hp : nativePi m ell μ F z hz g=
      (n/2)*(∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
        (sourcePair (L a (J μ F (X i))) (E a i j m ell (X j))+
        sourcePair (E a i j m ell (J μ F (X i))) (L a (X j)))).re := by
    change (∑i:Fin 2,∑j:Fin 2,sourcePair (J μ F (X i))
      (bracket diagonalAction (N i j m ell) (X j))).im=_
    rw [hw]
    have hc (u : ℂ) : (Complex.I*(n:ℂ)/2*u).im=(n/2)*u.re := by
      rw [show Complex.I*(n:ℂ)/2=Complex.I*((n/2:ℝ):ℂ) by push_cast;ring]
      simp only [Complex.mul_im,Complex.mul_re,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,mul_zero,zero_add,sub_zero]
    exact hc _
  rw [hp,hr]
  have hh : SourceClockPhiNativeJointPayment.nativeHalf m ell μ F z hz g=
      (2*n*μ)*(∑i:Fin 2,∑a:ScalarIndex,∑j:Fin 2,
        sourcePair (L a (X i)) (bracket (E a i j m ell) (A μ F) (X j))).im := by
    unfold SourceClockPhiNativeJointPayment.nativeHalf
    congr 1
    apply congrArg Complex.im
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro a _
    simp only [SourceClockPhiNativeJointPayment.columnCommutator,inner_sum]
    apply Finset.sum_congr rfl;intro j _
    change _=inner ℂ (embed (L a (X i))) (embed (bracket (E a i j m ell) (A μ F) (X j)))
    rw [EA_embed μ hμ F,show embed (X j)=finiteResolvent F z (SourceClockPhiNativeJointPayment.inputSeed g j:H) from input_embed F z hz g j]
    rfl
  rw [hh]
  dsimp only [curvatureHalf]
  simp only [sourcePair,map_sum,inner_sum,Finset.sum_sub_distrib,Complex.sub_im]
  have hswap (Z : Fin 2 → Fin 2 → ScalarIndex → ℂ) :
      (∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,Z i j a)=∑i:Fin 2,∑a:ScalarIndex,∑j:Fin 2,Z i j a := by
    apply Finset.sum_congr rfl;intro i _;exact Finset.sum_comm
  rw [hswap,hswap]
  ring

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'

/-- The common-tail error is generated internally; the second curvature half and the original
CF plus full-defect pressure stay together before the positive part. -/
theorem actual_native_curvature_common_payment (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain)
    (η : ℝ) (hη : 0<η) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,∀ m : ℕ,M ≤ m → ∀ ell : ℕ,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (|nativePi m ell μ F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g+
        curvatureHalf m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|-
        η*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)) ≤ ENNReal.ofReal ε := by
  simpa only [actual_native_curvature_return μ hμ] using
    SourceClockPhiNativeJointPayment.actual_native_commutator_half_payment μ hμ g η hη


/-- The Abel damping acts on the actual same-compression commutator; this square is not declared positive. -/
def liouvillian (μ : ℝ) (F : Index) (T : End) : End :=
  (4*μ:ℂ) • T-Complex.I • bracket (C F) T
private theorem bracket_smul (T X : End) (c : ℂ) : bracket T (c • X)=c • bracket T X := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem bracket_sub (T X Y : End) : bracket T (X-Y)=bracket T X-bracket T Y := by
  unfold bracket;noncomm_ring
private theorem bracket_jacobi (T X Y : End) :
    bracket T (bracket X Y)=bracket (bracket T X) Y+bracket X (bracket T Y) := by
  unfold bracket;noncomm_ring
private theorem liouvillian_square (μ : ℝ) (hμ : 0<μ) (F : Index) (T : End) (hT : Commute T Chi) :
    liouvillian μ F (liouvillian μ F (bracket T (A μ F)))=
      (Complex.I*(4*μ:ℂ)) • bracket (bracket T (C F)) Chi+
        bracket (bracket (C F) (bracket T (C F))) (A μ F) := by
  have hj : bracket (C F) (A μ F)=(-Complex.I*(4*μ:ℂ)) • (A μ F-Chi) :=
    current_source μ hμ F
  have hzero : bracket T Chi=0 := sub_eq_zero.mpr hT.eq
  have hjac := bracket_jacobi T (C F) (A μ F)
  rw [hj,bracket_smul,bracket_sub,hzero,sub_zero] at hjac
  have hi : Complex.I*(-Complex.I*(4*μ:ℂ))=(4*μ:ℂ) := by
    calc _= -(Complex.I*Complex.I)*(4*μ:ℂ) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  have hf : liouvillian μ F (bracket T (A μ F))=
      Complex.I • bracket (bracket T (C F)) (A μ F) := by
    have h := congrArg (fun X : End=>Complex.I • X) hjac
    rw [smul_smul,hi,smul_add] at h
    unfold liouvillian
    linear_combination (norm:=module) h
  rw [hf]
  unfold liouvillian
  simp only [bracket_smul,smul_smul,Complex.I_mul_I,neg_one_smul,sub_neg_eq_add]
  rw [bracket_jacobi,hj,bracket_smul,bracket_sub]
  module

/-- The source contact pays its entire original native part; the full double defect and
second source curvature remain in one actual Liouvillian forcing word. -/
theorem actual_second_native_liouvillian (μ : ℝ) (hμ : 0<μ) (F : Index) (a : ScalarIndex) :
    liouvillian μ F (liouvillian μ F (bracket (L a) (A μ F)))=
      (Complex.I*(4*μ:ℂ)) •
        ((-3*(n:ℂ)) • (B*(1-B)^2*L a)-
          bracket (bracket (L a) (defectAction F)) Chi)+
        bracket (bracket (C F) (bracket (L a) (C F))) (A μ F) := by
  rw [liouvillian_square μ hμ F (L a) (L_clock a)]
  have hc : bracket (bracket (L a) (C F)) Chi=
      (-3*(n:ℂ)) • (B*(1-B)^2*L a)-bracket (bracket (L a) (defectAction F)) Chi :=
    SourceClockAbelNativeContact.actual_native_clock_full_defect F a
  rw [hc]

end LowEnergy.SourceClockAbelNativeCurvature
