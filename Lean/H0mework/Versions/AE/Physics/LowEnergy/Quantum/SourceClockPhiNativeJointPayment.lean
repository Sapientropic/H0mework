import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceBoundedClockAbel
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiSecondPressure
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiEndpointNativePressure
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponsePositiveSource
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiNativeJointPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussFockWeights GaussDensityCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart SourceQuantumFockGauge
open SourceCoframeVolume SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiRadiusResponsePositiveSource SourceClockYukawaCubicCurrent
open SourceRelativePowerTail SourceFamilyHilbert SourceFamilyOperator
open FullYSourceCutoffNorm
open FullYSourceFiniteTimeIntegral FullYSourceTimeFamilyGraph FullYSourceCutoffTimeGraph
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev Op := H →L[ℂ] H
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev L2H := Lp H 2 (MeasureTheory.volume : Measure ℝ)
attribute [local irreducible] finiteResolvent SourceClockYukawaCubicCurrent.resolventCore

open SourceBoundedClockAbel (abelObservable)
open SourceClockPhiSecondPressure SourceScalarInverseNativeEnergy SourceClockReflectedForm SourceScalarPairedTransport
open SourceClockRadiusResponseAffine GaussNativePotential SourceCornerForcing SourceRetardedBandCurrent
open SourceLocalizedInverseFormPayment
private theorem phi_inverse_core (f:QuantumTest) : phiInverseBounded (embed f)=embed (phiInverseAction f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem phi_inverse_norm : ‖phiInverseBounded‖ ≤ 1 := GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem phi_inverse_pair (x y:H) : inner ℂ (phiInverseBounded x) y=inner ℂ x (phiInverseBounded y) := by
  refine GaussBoundedMultiplier.core_dense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  obtain ⟨g,rfl⟩:=coreEquiv.surjective b
  change inner ℂ (phiInverseBounded (embed f)) (embed g)=inner ℂ (embed f) (phiInverseBounded (embed g))
  rw [phi_inverse_core,phi_inverse_core]
  exact (multiply_pair _ _ _ _).symm
private theorem phi_inverse_positive : 0 ≤ phiInverseBounded := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  refine ⟨phi_inverse_pair,?_⟩
  intro x
  change 0 ≤ (inner ℂ (phiInverseBounded x) x).re
  rw [phi_inverse_pair]
  refine GaussBoundedMultiplier.core_dense.induction_on x (isClosed_le continuous_const (by fun_prop)) ?_
  intro a
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  change 0 ≤ (inner ℂ (embed f) (phiInverseBounded (embed f))).re
  rw [phi_inverse_core]
  change 0 ≤ (sourcePair f (phiInverseAction f)).re
  rw [sourcePair_integral]
  have hr:(∫z,densityPair f (phiInverseAction f) z ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫z,(densityPair f (phiInverseAction f) z).re ∂GaussHistoryHilbert.configurationMeasure := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re (densityPair_integrable f (phiInverseAction f))).symm
  rw [hr]
  apply integral_nonneg
  intro z
  change 0 ≤ (densityPair f (phiInverseAction f) z).re
  by_cases hz:z∈physicalChart
  · have hp:0 ≤ (densityPair f f z).re := by
      change 0 ≤ RCLike.re (inner ℂ (weight (fun N=>(density N z:ℂ)) (f z)) (f z))
      rw [GaussBoundedMultiplier.weighted_square _ (fun N=>(density_pos N ⟨z,hz⟩).le)]
      exact sq_nonneg _
    have he:densityPair f (phiInverseAction f) z=(phiReciprocal z:ℂ)*densityPair f f z :=
      inner_smul_right _ _ _
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hp
  · have hf:f z=0 := image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]
private def phiComplement : Op := 1-phiInverseBounded
private theorem phi_complement_positive : 0 ≤ phiComplement :=
  sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ phi_inverse_positive).mp phi_inverse_norm)
private theorem phi_complement_le_one : phiComplement ≤ 1 := sub_le_self _ phi_inverse_positive
/-- The same actual affine radial powers, on the full weighted Hilbert space. -/
private def phiTail (m ell:ℕ) : Op := phiComplement^(m+1)-phiComplement^(ell+1)
private theorem phi_power_core (n:ℕ) (f:QuantumTest) :
    (phiComplement^n) (embed f)=embed (((1-phiInverseAction)^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change phiComplement ((phiComplement^n) (embed f))=embed ((1-phiInverseAction) (((1-phiInverseAction)^n) f))
    rw [ih]
    change embed (((1-phiInverseAction)^n) f)-phiInverseBounded (embed (((1-phiInverseAction)^n) f))=_
    rw [phi_inverse_core,←map_sub]
    rfl
private theorem phi_tail_core (m ell:ℕ) (f:QuantumTest) :
    phiTail m ell (embed f)=embed (phiThetaAction m ell f) := by
  simp only [phiTail,sub_apply,phi_power_core,phiThetaAction,LinearMap.sub_apply,map_sub]
private theorem phi_tail_pair (m ell:ℕ) (x y:H) :
    inner ℂ (phiTail m ell x) y=inner ℂ x (phiTail m ell y) := by
  have hp:=((ContinuousLinearMap.nonneg_iff_isPositive _).mp phi_complement_positive).isSymmetric
  simp only [phiTail,sub_apply,inner_sub_left,inner_sub_right]
  rw [power_pair phiComplement hp (m+1),power_pair phiComplement hp (ell+1)]

private abbrev TH := TimeSpace (MeasureTheory.volume:Measure ℝ)
private def readFamily (A:Op) (f:Family L2H sourceFilter) : Family L2H sourceFilter :=
  act sourceFilter (SourceFamilyOperator.constant (A.compLpL 2 MeasureTheory.volume)) f
private theorem family_value_sub {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f g:Family E sourceFilter) (F:Index) : value (f-g) F=value f F-value g F := rfl
private theorem read_value (A:Op) (f:Family L2H sourceFilter) (F:Index) :
    value (readFamily A f) F=A.compLpL 2 MeasureTheory.volume (value f F) := rfl
private theorem read_family_norm (A:Op) (f:Family L2H sourceFilter) :
    ‖readFamily A f‖=‖familyReader (MeasureTheory.volume:Measure ℝ) A (f:TH)‖ := by
  unfold familyReader
  rw [lift_coe,UniformSpace.Completion.norm_coe]
  rfl
private theorem lp_decreasing {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (Q:E →L[ℂ] E) (hQ₀:0 ≤ Q) (hQ₁:Q ≤ 1) (f:Lp E 2 (MeasureTheory.volume:Measure ℝ))
    {m n:ℕ} (hmn:m ≤ n) :
    ‖(Q^n).compLpL 2 MeasureTheory.volume f-(Q^m).compLpL 2 MeasureTheory.volume f‖^2  ≤
      ‖(Q^m).compLpL 2 MeasureTheory.volume f‖^2-‖(Q^n).compLpL 2 MeasureTheory.volume f‖^2 := by
  let a:Lp E 2 (MeasureTheory.volume:Measure ℝ):=(Q^n).compLpL 2 MeasureTheory.volume f
  let b:Lp E 2 (MeasureTheory.volume:Measure ℝ):=(Q^m).compLpL 2 MeasureTheory.volume f
  change ‖a-b‖^2 ≤ ‖b‖^2-‖a‖^2
  rw [square_integral MeasureTheory.volume (a-b),square_integral MeasureTheory.volume b,
    square_integral MeasureTheory.volume a,←integral_sub (square_integrable MeasureTheory.volume b)
      (square_integrable MeasureTheory.volume a)]
  apply integral_mono_ae (square_integrable MeasureTheory.volume (a-b))
    ((square_integrable MeasureTheory.volume b).sub (square_integrable MeasureTheory.volume a))
  filter_upwards [Lp.coeFn_sub a b,(Q^n).coeFn_compLpL f,(Q^m).coeFn_compLpL f] with t hs hn hm
  simp only [hs,Pi.sub_apply]
  change ‖a t-b t‖^2 ≤ ‖b t‖^2-‖a t‖^2
  rw [hn,hm]
  exact positive_power_distance Q hQ₀ hQ₁ (f t) hmn
private theorem lifted_decreasing {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A:ℕ→E →L[ℂ] E)
    (hA:∀x m n,m ≤ n→‖A n x-A m x‖^2 ≤ ‖A m x‖^2-‖A n x‖^2)
    (x:SourceFamilyHilbert.Hilbert E sourceFilter) {m n:ℕ} (hmn:m ≤ n) :
    ‖lift sourceFilter (SourceFamilyOperator.constant (A n)) x-lift sourceFilter (SourceFamilyOperator.constant (A m)) x‖^2  ≤
    ‖lift sourceFilter (SourceFamilyOperator.constant (A m)) x‖^2-
      ‖lift sourceFilter (SourceFamilyOperator.constant (A n)) x‖^2 := by
  refine UniformSpace.Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [lift_coe,lift_coe,←UniformSpace.Completion.coe_sub]
  simp only [UniformSpace.Completion.norm_coe]
  apply le_of_tendsto_of_tendsto (square_tendsto sourceFilter _)
    ((square_tendsto sourceFilter _).sub (square_tendsto sourceFilter _))
  exact Eventually.of_forall (fun F=>hA (value f F) m n hmn)
private theorem lifted_power_distance (f:TH) {m n:ℕ} (hmn:m ≤ n) :
    ‖familyReader MeasureTheory.volume (phiComplement^n) f-familyReader MeasureTheory.volume (phiComplement^m) f‖^2  ≤
    ‖familyReader MeasureTheory.volume (phiComplement^m) f‖^2-
      ‖familyReader MeasureTheory.volume (phiComplement^n) f‖^2 :=
  lifted_decreasing (fun n=>(phiComplement^n).compLpL 2 (MeasureTheory.volume:Measure ℝ))
    (fun x _ _ h=>lp_decreasing phiComplement phi_complement_positive phi_complement_le_one x h) f hmn
private theorem lp_sub {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B:E →L[ℂ] E) : (A-B).compLpL 2 (MeasureTheory.volume:Measure ℝ)=
      A.compLpL 2 MeasureTheory.volume-B.compLpL 2 MeasureTheory.volume := by
  have h:A-B=A+(-1:ℂ) • B:=by rw [neg_one_smul,sub_eq_add_neg]
  rw [h,ContinuousLinearMap.add_compLpL,ContinuousLinearMap.smul_compLpL,neg_one_smul]
  exact (sub_eq_add_neg _ _).symm
private theorem read_family_sub (A B:Op) (f:Family L2H sourceFilter) :
    readFamily (A-B) f=readFamily A f-readFamily B f := by
  apply Family.ext
  funext F
  change (A-B).compLpL 2 MeasureTheory.volume (value f F)=
    A.compLpL 2 MeasureTheory.volume (value f F)-B.compLpL 2 MeasureTheory.volume (value f F)
  exact congrArg (fun T:L2H →L[ℂ] L2H=>T (value f F)) (lp_sub A B)
private theorem read_coe (A:Op) (f:Family L2H sourceFilter) :
    (readFamily A f:TH)=familyReader (MeasureTheory.volume:Measure ℝ) A (f:TH) :=
  (lift_coe sourceFilter (SourceFamilyOperator.constant (A.compLpL 2 MeasureTheory.volume)) f).symm
attribute [local irreducible] phiComplement phiTail readFamily
private theorem family_tail (f:Family L2H sourceFilter) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ,  N  ≤  m → ∀ ell : ℕ,  m  ≤  ell →
      ∀ᶠ F in (sourceFilter:Filter Index),‖value (readFamily (phiTail m ell) f) F‖^2 ≤ ε := by
  intro ε hε
  let u:ℕ→TH:=fun n=>(readFamily (phiComplement^n) f:TH)
  have hd:∀m n,m ≤ n→‖u n-u m‖^2 ≤ ‖u m‖^2-‖u n‖^2 := by
    intro m n hmn
    simpa only [u,read_coe] using lifted_power_distance (f:TH) hmn
  obtain ⟨N,hN⟩:=decreasing_distance_tail u hd
    (Real.sqrt (ε/2)) (Real.sqrt_pos.mpr (by positivity))
  refine ⟨N,fun m hm ell hml=>?_⟩
  let r:=readFamily (phiTail m ell) f
  have hr:‖r‖^2<ε := by
    have h:=hN m hm ell hml
    have hrf:r=readFamily (phiComplement^(m+1)) f-readFamily (phiComplement^(ell+1)) f := by
      dsimp only [r]
      unfold phiTail
      exact read_family_sub _ _ f
    have he: (r:TH)=u (m+1)-u (ell+1) := by
      have h:=congrArg (fun x:Family L2H sourceFilter=>(x:TH)) hrf
      rw [UniformSpace.Completion.coe_sub] at h
      exact h
    rw [←he,UniformSpace.Completion.norm_coe] at h
    have hs:=Real.sq_sqrt (by positivity : 0 ≤ ε/2)
    nlinarith only [h,hs,norm_nonneg r,Real.sqrt_nonneg (ε/2)]
  filter_upwards [(square_tendsto sourceFilter r).eventually (gt_mem_nhds hr)] with F hF
  exact hF.le

private abbrev C (F:Index) : Op := GaussGradedCompression.compression F
private theorem frequency_nonreal (advanced:Bool) (μ:ℝ) (hμ:0 < μ) (w:ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem finite_star (F:Index) (z:ℂ) : finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (C F-star z • 1)=(Ring.inverse (C F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced:Bool) (μ:ℝ) (hμ:0 < μ) (F:Index) :
    Continuous (fun w:ℝ=>finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced
  · exact finite_frequency_continuous μ hμ F
  · have he:(fun w:ℝ=>finiteResolvent F (actualFrequency true μ w))=
        (fun w:ℝ=>(finiteResolvent F (line μ w)).adjoint) := funext (fun w=>finite_star F (line μ w))
    exact he ▸ (ContinuousLinearMap.adjoint.continuous.comp (finite_frequency_continuous μ hμ F))
private theorem whole_memLp (advanced:Bool) (μ:ℝ) (hμ:0 < μ) (F:Index) (g:H) :
    MemLp (fun w:ℝ=>finiteResolvent F (actualFrequency advanced μ w) g) 2 (MeasureTheory.volume:Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (((frequency_continuous advanced μ hμ F).clm_apply continuous_const).aestronglyMeasurable)).mpr
  have hi:Integrable (fun w:ℝ=>‖finiteResolvent F (line μ w) g‖^2) := by
    simpa only [line,mul_comm (μ:ℂ) Complex.I] using SourceActualResolventEnergy.actual_square_integrable F μ hμ g
  have he:∀w,‖finiteResolvent F (actualFrequency advanced μ w) g‖=‖finiteResolvent F (line μ w) g‖ := by
    intro w
    cases advanced
    · rfl
    · exact SourceInverseSourceLeg.actual_conjugate_leg_norm F (line μ w)
        (by simpa only [line_im] using hμ.ne') g
  simpa only [he] using hi
private theorem whole_read (advanced:Bool) (μ:ℝ) (hμ:0 < μ) (F:Index) (g:H) :
    (fun w:ℝ=>value (wholeInputFamily advanced μ hμ g) F w)=ᵐ[MeasureTheory.volume]
      (fun w:ℝ=>finiteResolvent F (actualFrequency advanced μ w) g) :=
  (whole_memLp advanced μ hμ F g).coeFn_toLp

private theorem abel_norm (μ:ℝ) (hμ:0 < μ) (F:Index) : ‖abelObservable μ F‖ ≤ 1 := by
  have h:=SourceBoundedClockAbel.actual_bounded_clock_abel_source μ hμ F
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ h.2.1).mpr h.2.2.1
private def abelOperator (μ:ℝ) (hμ:0 < μ) : Operator Index L2H where
  component F := (abelObservable μ F).compLpL 2 MeasureTheory.volume
  bounded := ⟨1,zero_le_one,fun F x=>
    (((abelObservable μ F).compLpL 2 MeasureTheory.volume).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ((ContinuousLinearMap.norm_compLpL_le _).trans
        (abel_norm μ hμ F)) (norm_nonneg x))⟩
private def abelFamily (μ:ℝ) (hμ:0 < μ) (advanced:Bool) (g:H) : Family L2H sourceFilter :=
  act sourceFilter (abelOperator μ hμ) (wholeInputFamily advanced μ hμ g)
private theorem abel_read (μ:ℝ) (hμ:0 < μ) (advanced:Bool) (F:Index) (g:H) :
    (fun w:ℝ=>value (abelFamily μ hμ advanced g) F w)=ᵐ[MeasureTheory.volume]
      (fun w:ℝ=>abelObservable μ F (finiteResolvent F (actualFrequency advanced μ w) g)) := by
  filter_upwards [(abelObservable μ F).coeFn_compLpL (value (wholeInputFamily advanced μ hμ g) F),
    whole_read advanced μ hμ F g] with w hA hR
  change ((abelObservable μ F).compLpL 2 MeasureTheory.volume (value (wholeInputFamily advanced μ hμ g) F)) w=_
  rw [hA,hR]
private def boundary (n:ℕ) : Op := PositiveContractionRitt.gradient phiComplement n
private def peak (m ell:ℕ) : Op := boundary ell-boundary m
private theorem boundary_norm (n:ℕ) : ‖boundary n‖ ≤ 1 :=
  PositiveContractionRitt.gradient_norm phiComplement phi_complement_positive phi_complement_le_one n
private theorem peak_norm (m ell:ℕ) : ‖peak m ell‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans ((add_le_add (boundary_norm ell) (boundary_norm m)).trans_eq (by norm_num))
private theorem theta_norm (m ell:ℕ) : ‖phiTail m ell‖ ≤ 2 := by
  have hQ:‖phiComplement‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ phi_complement_positive).mpr phi_complement_le_one
  have hpow (k:ℕ):‖phiComplement^k‖ ≤ 1 := by
    induction k with
    | zero =>
      rw [pow_zero]
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      change ‖x‖ ≤ 1*‖x‖
      rw [one_mul]
    | succ k ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans ((mul_le_mul ih hQ (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  unfold phiTail
  exact (norm_sub_le _ _).trans ((add_le_add (hpow _) (hpow _)).trans_eq (by norm_num))
private def coefficient (m ell:ℕ) : Fin 2 → Fin 2 → Op :=
  !![(2:ℂ) • peak m ell-phiTail m ell,(-2:ℂ) • (phiInverseBounded*peak m ell);
    (-2:ℂ) • (phiInverseBounded*peak m ell),phiInverseBounded^2*(phiTail m ell+(2:ℂ) • peak m ell)]
/-- The same two-seed metric's entire native zero-order column, with the final actual θ retained. -/
def nativeColumn (a:ScalarIndex) (i j:Fin 2) (m ell:ℕ) : Op :=
  phiDirectionOperator (scalarBasis a)*coefficient m ell i j*phiTail m ell
private theorem coefficient_norm (m ell:ℕ) (i j:Fin 2) : ‖coefficient m ell i j‖ ≤ 6 := by
  have hs:‖phiInverseBounded‖ ≤ 1:=phi_inverse_norm
  have hs2:‖phiInverseBounded^2‖ ≤ 1 := by
    rw [pow_two]
    exact (norm_mul_le _ _).trans ((mul_le_mul hs hs (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hp:=peak_norm m ell
  have ht:=theta_norm m ell
  have h2:‖(2:ℂ) • peak m ell‖ ≤ 4 := by simpa only [norm_smul,Complex.norm_ofNat,show (2:ℝ)*2=4 by norm_num] using mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 2)
  have hS:‖phiInverseBounded*peak m ell‖ ≤ 2 := (norm_mul_le _ _).trans ((mul_le_mul hs hp (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  fin_cases i <;> fin_cases j
  · exact (norm_sub_le _ _).trans ((add_le_add h2 ht).trans_eq (by norm_num))
  · change ‖(-2:ℂ) • (phiInverseBounded*peak m ell)‖ ≤ 6
    rw [norm_smul,norm_neg,Complex.norm_ofNat]
    linarith
  · change ‖(-2:ℂ) • (phiInverseBounded*peak m ell)‖ ≤ 6
    rw [norm_smul,norm_neg,Complex.norm_ofNat]
    linarith
  · exact (norm_mul_le _ _).trans ((mul_le_mul hs2 ((norm_add_le _ _).trans (add_le_add ht h2))
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
private theorem column_energy (i j:Fin 2) (m ell:ℕ) (x:H) :
    (∑a:ScalarIndex,‖nativeColumn a i j m ell x‖^2) ≤ 9*‖phiTail m ell x‖^2 := by
  change (∑a:ScalarIndex,‖phiDirectionOperator (scalarBasis a) (coefficient m ell i j (phiTail m ell x))‖^2) ≤ _
  rw [original_phi_gradient_energy]
  have hn:=((coefficient m ell i j).le_opNorm (phiTail m ell x)).trans
    (mul_le_mul_of_nonneg_right (coefficient_norm m ell i j) (norm_nonneg _))
  have hh:=pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith only [hh,sq_nonneg ‖phiInverseBounded (coefficient m ell i j (phiTail m ell x))‖]
/-- The literal metric on the original two source inputs. -/
def nativeMetricCore (i j:Fin 2) (m ell:ℕ) : End :=
  !![phiRadiusAction*(phiThetaAction m ell)^2,-(phiThetaAction m ell)^2;
    -(phiThetaAction m ell)^2,phiInverseAction*(phiThetaAction m ell)^2] i j
def nativeColumnCore (a:ScalarIndex) (i j:Fin 2) (m ell:ℕ) : End :=
  Complex.I • SourceScalarDoubleCurrent.bracket (covariantMomentum (scalarDirection a)) (nativeMetricCore i j m ell)
/-- Both literal fixed sources share the same F, frequency and Abel observable. -/
def inputSeed (g:diagonal.domain) (i:Fin 2) : diagonal.domain := ![g,phiRadiusSource g] i
private def inputVector (F:Index) (z:ℂ) (g:diagonal.domain) (i:Fin 2) : H := finiteResolvent F z (inputSeed g i:H)
def columnCommutator (a:ScalarIndex) (i:Fin 2) (m ell:ℕ) (μ:ℝ) (F:Index) (z:ℂ) (g:diagonal.domain) : H :=
  ∑j:Fin 2,(nativeColumn a i j m ell (abelObservable μ F (inputVector F z g j))-
    abelObservable μ F (nativeColumn a i j m ell (inputVector F z g j)))
def columnEnergy (m ell:ℕ) (μ:ℝ) (F:Index) (z:ℂ) (g:diagonal.domain) : ℝ :=
  ∑i:Fin 2,∑a:ScalarIndex,‖columnCommutator a i m ell μ F z g‖^2
private theorem two_square {E:Type*} [NormedAddCommGroup E] (x y:E) :
    ‖x+y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h:=pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]
private theorem column_commutator_energy (m ell:ℕ) (μ:ℝ) (hμ:0 < μ) (F:Index) (z:ℂ) (g:diagonal.domain) :
    columnEnergy m ell μ F z g ≤ 72*∑j:Fin 2,
      (‖phiTail m ell (abelObservable μ F (inputVector F z g j))‖^2+
        ‖phiTail m ell (inputVector F z g j)‖^2) := by
  have ha (x:H):‖abelObservable μ F x‖ ≤ ‖x‖:=((abelObservable μ F).le_opNorm x).trans
    ((mul_le_mul_of_nonneg_right (abel_norm μ hμ F) (norm_nonneg x)).trans_eq (one_mul _))
  have hrow (a:ScalarIndex) (i:Fin 2):‖columnCommutator a i m ell μ F z g‖^2 ≤
      4*∑j:Fin 2,(‖nativeColumn a i j m ell (abelObservable μ F (inputVector F z g j))‖^2+
        ‖nativeColumn a i j m ell (inputVector F z g j)‖^2) := by
    have hdiff (j:Fin 2):
        ‖nativeColumn a i j m ell (abelObservable μ F (inputVector F z g j))-
          abelObservable μ F (nativeColumn a i j m ell (inputVector F z g j))‖^2 ≤
        2*‖nativeColumn a i j m ell (abelObservable μ F (inputVector F z g j))‖^2+
          2*‖nativeColumn a i j m ell (inputVector F z g j)‖^2 := by
      have h:=two_square (nativeColumn a i j m ell (abelObservable μ F (inputVector F z g j)))
        (-(abelObservable μ F (nativeColumn a i j m ell (inputVector F z g j))))
      rw [norm_neg,←sub_eq_add_neg] at h
      have he:=pow_le_pow_left₀ (norm_nonneg _) (ha (nativeColumn a i j m ell (inputVector F z g j))) 2
      nlinarith only [h,he]
    unfold columnCommutator
    rw [Fin.sum_univ_two]
    have h:=two_square
      (nativeColumn a i 0 m ell (abelObservable μ F (inputVector F z g 0))-
        abelObservable μ F (nativeColumn a i 0 m ell (inputVector F z g 0)))
      (nativeColumn a i 1 m ell (abelObservable μ F (inputVector F z g 1))-
        abelObservable μ F (nativeColumn a i 1 m ell (inputVector F z g 1)))
    rw [Fin.sum_univ_two]
    linarith only [h,hdiff 0,hdiff 1]
  unfold columnEnergy
  calc
    _ ≤ ∑i:Fin 2,∑a:ScalarIndex,4*∑j:Fin 2,
      (‖nativeColumn a i j m ell (abelObservable μ F (inputVector F z g j))‖^2+
        ‖nativeColumn a i j m ell (inputVector F z g j)‖^2) :=
          Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun a _=>hrow a i))
    _=4*∑i:Fin 2,∑j:Fin 2,((∑a:ScalarIndex,‖nativeColumn a i j m ell (abelObservable μ F (inputVector F z g j))‖^2)+
        (∑a:ScalarIndex,‖nativeColumn a i j m ell (inputVector F z g j)‖^2)) := by
      simp only [←Finset.sum_add_distrib,←Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ ≤ 4*∑i:Fin 2,∑j:Fin 2,(9*‖phiTail m ell (abelObservable μ F (inputVector F z g j))‖^2+
        9*‖phiTail m ell (inputVector F z g j)‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>add_le_add
        (column_energy i j m ell _) (column_energy i j m ell _)))
    _=_ := by simp only [Fin.sum_univ_two];ring
private theorem acted_integral (B:Op) (f:Family L2H sourceFilter) (F:Index) (u:ℝ→H)
    (hu:(fun w:ℝ=>value f F w)=ᵐ[MeasureTheory.volume]u) :
    (∫⁻w:ℝ,ENNReal.ofReal (‖B (u w)‖^2))=ENNReal.ofReal (‖value (readFamily B f) F‖^2) := by
  let r:L2H:=value f F
  have he:(fun w:ℝ=>‖B (u w)‖^2)=ᵐ[MeasureTheory.volume]
      (fun w:ℝ=>‖value (readFamily B f) F w‖^2) := by
    filter_upwards [B.coeFn_compLpL r,hu] with w ht hr
    rw [read_value]
    change _=‖(B.compLpL 2 MeasureTheory.volume r) w‖^2
    rw [ht,hr]
  have hi:=(square_integrable MeasureTheory.volume (value (readFamily B f) F)).congr he.symm
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _=>sq_nonneg _)),
    integral_congr_ae he,←square_integral]
private theorem input_measurable (B:Op) (advanced:Bool) (μ:ℝ) (hμ:0 < μ) (F:Index) (g:H) :
    Measurable (fun w:ℝ=>ENNReal.ofReal (‖B (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) :=
  (B.continuous.comp ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2 |>.measurable.ennreal_ofReal
private def rowEnergy (m ell:ℕ) (μ:ℝ) (F:Index) (z:ℂ) (g:H) : ℝ :=
  ‖phiTail m ell (abelObservable μ F (finiteResolvent F z g))‖^2+
    ‖phiTail m ell (finiteResolvent F z g)‖^2
private theorem row_integral (m ell:ℕ) (advanced:Bool) (μ:ℝ) (hμ:0 < μ) (F:Index) (g:H) :
    (∫⁻w:ℝ,ENNReal.ofReal (rowEnergy m ell μ F (actualFrequency advanced μ w) g))=
      ENNReal.ofReal (‖value (readFamily (phiTail m ell) (abelFamily μ hμ advanced g)) F‖^2)+
      ENNReal.ofReal (‖value (readFamily (phiTail m ell) (wholeInputFamily advanced μ hμ g)) F‖^2) := by
  simp_rw [rowEnergy,ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  have hm:Measurable (fun w:ℝ=>ENNReal.ofReal (‖phiTail m ell (abelObservable μ F
      (finiteResolvent F (actualFrequency advanced μ w) g))‖^2)) := by
    simpa only [mul_apply_eq_comp] using input_measurable (phiTail m ell*abelObservable μ F) advanced μ hμ F g
  rw [lintegral_add_left hm]
  rw [acted_integral (phiTail m ell) (abelFamily μ hμ advanced g) F _ (abel_read μ hμ advanced F g),
    acted_integral (phiTail m ell) (wholeInputFamily advanced μ hμ g) F _ (whole_read advanced μ hμ F g)]
private theorem row_tail (advanced:Bool) (μ:ℝ) (hμ:0 < μ) (g:H) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,∀ m : ℕ, N ≤ m → ∀ ell : ℕ, m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      (∫⁻w:ℝ,ENNReal.ofReal (rowEnergy m ell μ F (actualFrequency advanced μ w) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩:=family_tail (abelFamily μ hμ advanced g) (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩:=family_tail (wholeInputFamily advanced μ hμ g) (ε/2) (by positivity)
  refine ⟨max N₀ N₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hA hR
  rw [row_integral m ell advanced μ hμ F g]
  calc _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2):=add_le_add (ENNReal.ofReal_le_ofReal hA) (ENNReal.ofReal_le_ofReal hR)
       _=ENNReal.ofReal ε:=by rw [←ENNReal.ofReal_add (by positivity) (by positivity)];congr 1;ring
private theorem row_common_tail (μ:ℝ) (hμ:0 < μ) (g:H) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,∀ m : ℕ, N ≤ m → ∀ ell : ℕ, m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (rowEnergy m ell μ F (actualFrequency advanced μ w) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩:=row_tail false μ hμ g ε hε
  obtain ⟨N₁,h₁⟩:=row_tail true μ hμ g ε hε
  refine ⟨max N₀ N₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hf ht
  intro advanced
  cases advanced
  · exact hf
  · exact ht
private theorem column_energy_integral (m ell:ℕ) (advanced:Bool) (μ:ℝ) (hμ:0 < μ) (F:Index) (g:diagonal.domain) :
    (∫⁻w:ℝ,ENNReal.ofReal (columnEnergy m ell μ F (actualFrequency advanced μ w) g)) ≤
      ENNReal.ofReal (72:ℝ)*((∫⁻w:ℝ,ENNReal.ofReal (rowEnergy m ell μ F (actualFrequency advanced μ w) (g:H)))+
      (∫⁻w:ℝ,ENNReal.ofReal (rowEnergy m ell μ F (actualFrequency advanced μ w) (phiRadiusSource g:H)))) := by
  have hm (k:H):Measurable (fun w:ℝ=>ENNReal.ofReal (rowEnergy m ell μ F (actualFrequency advanced μ w) k)) := by
    simp_rw [rowEnergy,ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    exact (input_measurable (phiTail m ell*abelObservable μ F) advanced μ hμ F k).add
      (input_measurable (phiTail m ell) advanced μ hμ F k)
  calc _ ≤ ∫⁻w:ℝ,ENNReal.ofReal (72*(rowEnergy m ell μ F (actualFrequency advanced μ w) (g:H)+
      rowEnergy m ell μ F (actualFrequency advanced μ w) (phiRadiusSource g:H))) := by
        apply lintegral_mono
        intro w
        apply ENNReal.ofReal_le_ofReal
        simpa only [Fin.sum_univ_two,inputVector,inputSeed,Matrix.cons_val_zero,Matrix.cons_val_one,
          Matrix.head_cons,rowEnergy] using column_commutator_energy m ell μ hμ F (actualFrequency advanced μ w) g
       _=_ := by
        have hs (w:ℝ):ENNReal.ofReal (72*(rowEnergy m ell μ F (actualFrequency advanced μ w) (g:H)+
            rowEnergy m ell μ F (actualFrequency advanced μ w) (phiRadiusSource g:H)))=
            ENNReal.ofReal (72:ℝ)*(ENNReal.ofReal (rowEnergy m ell μ F (actualFrequency advanced μ w) (g:H))+
            ENNReal.ofReal (rowEnergy m ell μ F (actualFrequency advanced μ w) (phiRadiusSource g:H))) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 72),ENNReal.ofReal_add
            (show 0 ≤ rowEnergy m ell μ F (actualFrequency advanced μ w) (g:H) by unfold rowEnergy;positivity)
            (show 0 ≤ rowEnergy m ell μ F (actualFrequency advanced μ w) (phiRadiusSource g:H) by unfold rowEnergy;positivity)]
        simp_rw [hs]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_left (hm (g:H))]
private theorem column_energy_common_tail (μ:ℝ) (hμ:0 < μ) (g:diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,∀ m : ℕ, N ≤ m → ∀ ell : ℕ, m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (columnEnergy m ell μ F (actualFrequency advanced μ w) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩:=row_common_tail μ hμ (g:H) (ε/144) (by positivity)
  obtain ⟨N₁,h₁⟩:=row_common_tail μ hμ (phiRadiusSource g:H) (ε/144) (by positivity)
  refine ⟨max N₀ N₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hf ht
  intro advanced
  calc _ ≤ ENNReal.ofReal (72:ℝ)*(ENNReal.ofReal (ε/144)+ENNReal.ofReal (ε/144)):=
        (column_energy_integral m ell advanced μ hμ F g).trans
          (mul_le_mul le_rfl (add_le_add (hf advanced) (ht advanced)) zero_le zero_le)
       _=ENNReal.ofReal ε:=by
        rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
private def sourceState (i:Fin 2) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : QuantumTest :=
  resolventCore F z hz (coreEquiv.symm (inputSeed g i))
private def nativeInput (a:ScalarIndex) (i:Fin 2) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : H :=
  embed (SourcePhysicalKineticSquare.inverseVolumeAction
    (covariantMomentum (scalarDirection a) (sourceState i F z hz g)))
/-- This is the first half of the coherent native commutator pair, not a free graph input. -/
def nativeHalf (m ell:ℕ) (μ:ℝ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : ℝ :=
  (2*sourceTime 0*μ)*(∑i:Fin 2,∑a:ScalarIndex,
    inner ℂ (nativeInput a i F z hz g) (columnCommutator a i m ell μ F z g)).im
/-- The debit is the original two fixed-input second source pressure, including its full CF/defect return. -/
def nativePressureDebit (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : ℝ :=
  ∑i:Fin 2,let f:=SourcePhysicalKineticSquare.inverseRootAction (sourceState i F z hz g)
    (sourcePair f ((SourceClockPhiSecondBulk.secondJet (compressionCore F)+
      SourceClockPhiSecondBulk.secondJet (defectAction F)+
      (1/2:ℂ) • SourceScalarVirialBulk.vacuumConstantAction) f)).re
private theorem debit_source (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    nativePressureDebit F z hz g=∑i:Fin 2,SourceClockPhiSecondPressure.pressure (sourceState i F z hz g) := by
  unfold nativePressureDebit
  rw [SourceClockPhiSecondBulk.actual_second_compression_source]
  rfl
private theorem lapse_pos : 0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem native_debit (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    sourceTime 0*(∑i:Fin 2,∑a:ScalarIndex,‖nativeInput a i F z hz g‖^2) ≤ nativePressureDebit F z hz g := by
  rw [debit_source,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hc (a:ScalarIndex):‖nativeInput a i F z hz g‖=
      ‖embed (covariantMomentum (scalarDirection a)
        (SourcePhysicalKineticSquare.inverseVolumeAction (sourceState i F z hz g)))‖ := by
    have h:=LinearMap.congr_fun (SourceScalarInverseNativeEnergy.original_native_inverse_commute (scalarDirection a)).eq
      (sourceState i F z hz g)
    exact congrArg (fun f:QuantumTest=>‖embed f‖) h.symm
  simp_rw [hc]
  have h:=SourceClockPhiSecondPressure.original_second_pressure_payment (sourceState i F z hz g)
  have hn:0 ≤ shiftedMoment (sourceState i F z hz g):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hm:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) lapse_pos.le) hn
  exact (le_add_of_nonneg_right hm).trans h
private theorem young_native (μ η x y:ℝ) (hη:0 < η) :
    (2*sourceTime 0*μ)*(x*y) ≤ η*sourceTime 0*x^2+(sourceTime 0*μ^2/η)*y^2 := by
  apply (mul_le_mul_iff_left₀ hη).mp
  have he:(η*sourceTime 0*x^2+(sourceTime 0*μ^2/η)*y^2)*η=
      η^2*sourceTime 0*x^2+sourceTime 0*μ^2*y^2 := by field_simp
  rw [he]
  have h:=mul_nonneg lapse_pos.le (sq_nonneg (η*x-μ*y))
  nlinarith only [h]
private theorem native_half_point (m ell:ℕ) (μ:ℝ) (hμ:0 < μ) (F:Index) (z:ℂ) (hz:z.im≠0)
    (g:diagonal.domain) (η:ℝ) (hη:0 < η) :
    |nativeHalf m ell μ F z hz g|-η*nativePressureDebit F z hz g ≤
      (sourceTime 0*μ^2/η)*columnEnergy m ell μ F z g := by
  have hI:|(∑i:Fin 2,∑a:ScalarIndex,inner ℂ (nativeInput a i F z hz g)
      (columnCommutator a i m ell μ F z g)).im| ≤
      ∑i:Fin 2,∑a:ScalarIndex,‖nativeInput a i F z hz g‖*‖columnCommutator a i m ell μ F z g‖ := by
    apply (Complex.abs_im_le_norm _).trans
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>(norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun a _=>norm_inner_le_norm _ _))))
  have h0:0 ≤ 2*sourceTime 0*μ:=by have hn:=lapse_pos;positivity
  have h1:=mul_le_mul_of_nonneg_left hI h0
  have h2:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_:i∈(Finset.univ:Finset (Fin 2)))=>
    Finset.sum_le_sum (s:=Finset.univ) (fun a (_:a∈(Finset.univ:Finset ScalarIndex))=>
      young_native μ η ‖nativeInput a i F z hz g‖ ‖columnCommutator a i m ell μ F z g‖ hη))
  simp only [Finset.mul_sum,Finset.sum_add_distrib,←mul_assoc] at h1 h2
  have h3:=mul_le_mul_of_nonneg_left (native_debit F z hz g) hη.le
  rw [nativeHalf,abs_mul,abs_of_nonneg h0]
  unfold columnEnergy
  simp only [Finset.mul_sum,←mul_assoc] at h3 ⊢
  linarith only [h1,h2,h3]
/-- One coherent native half is paid by an arbitrarily small actual second-pressure debit;
its error has a common cutoff tail for both causal legs on the unchanged source filter. -/
theorem actual_native_commutator_half_payment (μ:ℝ) (hμ:0 < μ) (g:diagonal.domain) (η:ℝ) (hη:0 < η) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,∀ m : ℕ, N ≤ m → ∀ ell : ℕ, m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (|nativeHalf m ell μ F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g|-
        η*nativePressureDebit F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let c:ℝ:=sourceTime 0*μ^2/η
  have hc:0 < c:=by dsimp only [c];exact div_pos (mul_pos lapse_pos (sq_pos_of_pos hμ)) hη
  obtain ⟨N,hN⟩:=column_energy_common_tail μ hμ g (ε/c) (div_pos hε hc)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  calc _ ≤ ∫⁻w:ℝ,ENNReal.ofReal (c*columnEnergy m ell μ F (actualFrequency advanced μ w) g):=by
        apply lintegral_mono
        intro w
        exact ENNReal.ofReal_le_ofReal (native_half_point m ell μ hμ F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g η hη)
       _=ENNReal.ofReal c*(∫⁻w:ℝ,ENNReal.ofReal (columnEnergy m ell μ F (actualFrequency advanced μ w) g)):=by
        simp_rw [ENNReal.ofReal_mul hc.le]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
       _ ≤ ENNReal.ofReal c*ENNReal.ofReal (ε/c):=mul_le_mul le_rfl (hF advanced) zero_le zero_le
       _=ENNReal.ofReal ε:=by
        rw [←ENNReal.ofReal_mul hc.le]
        congr 1
        field_simp




set_option backward.isDefEq.respectTransparency true
open GaussLiveMomentum SourceScalarDoubleCurrent
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev P (a:ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev Q : End := 1-S
private abbrev D (a:ScalarIndex) : End := phiDirectionAction (scalarBasis a)
private abbrev T (m ell:ℕ) : End := phiThetaAction m ell
private abbrev B (m ell:ℕ) : End := SourceClockPhiRadiusResponseHessian.phiFirstPeak m ell
private abbrev d (a:ScalarIndex) : End := D a*S^2
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (phiReciprocal x:ℂ) • ((phiRadius x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse : r*S=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (phiRadius x:ℂ) • ((phiReciprocal x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem real_commute (c b : SourceCoordinateSlice → ℝ)
    (hc : ∀x:physicalChart,ContDiffAt ℝ ∞ c x.val)
    (hb : ∀x:physicalChart,ContDiffAt ℝ ∞ b x.val) : Commute (multiply c hc) (multiply b hb) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  exact smul_comm (c x:ℂ) (b x:ℂ) (f x)
private theorem inverse_D (a : ScalarIndex) : Commute S (D a) := real_commute _ _ _ _
private theorem inverse_d (a : ScalarIndex) : Commute S (d a) :=
  (inverse_D a).mul_right ((Commute.refl S).pow_right 2)
private theorem inverse_P (a : ScalarIndex) :
    bracket (P a) S=(-Complex.I) • d a := by
  have h : bracket (P a) r=Complex.I • D a :=
    (original_phi_radius_native_jet (scalarDirection a)).1
  have hm : bracket (P a) S= -(S*bracket (P a) r*S) := by
    have h1 : S*P a*r*S=S*P a := by
      calc _=S*P a*(r*S) := by noncomm_ring
           _=_ := by rw [radius_inverse,mul_one]
    have h2 : S*r*P a*S=P a*S := by rw [inverse_radius,one_mul]
    calc _= -(S*P a*r*S-S*r*P a*S) := by rw [h1,h2];unfold bracket;abel
         _=_ := by unfold bracket;noncomm_ring
  rw [hm,h]
  have hd : S*D a*S=d a := by
    rw [(inverse_D a).eq]
    change D a*S*S=D a*S^2
    rw [pow_two,mul_assoc]
  simp only [mul_smul_comm,smul_mul_assoc,neg_smul,hd]

private theorem Q_commute {A : End} (h : Commute S A) : Commute Q A :=
  (Commute.one_left A).sub_left h
private theorem first_commute {A : End} (h : Commute S A) (m ell : ℕ) : Commute (B m ell) A :=
  (((Q_commute h).pow_left ell).smul_left _).sub_left (((Q_commute h).pow_left m).smul_left _)
private theorem jet_theta_commute {A : End} (h : Commute S A) (m ell : ℕ) : Commute (T m ell) A :=
  ((Q_commute h).pow_left (m+1)).sub_left ((Q_commute h).pow_left (ell+1))
private theorem bracket_product (A X Y : End) : bracket A (X*Y)=bracket A X*Y+X*bracket A Y := by
  unfold bracket;noncomm_ring
private theorem bracket_sub (A X Y : End) : bracket A (X-Y)=bracket A X-bracket A Y := by
  unfold bracket;noncomm_ring
private theorem bracket_smul (A X : End) (c : ℂ) : bracket A (c • X)=c • bracket A X := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem inverse_Q (a : ScalarIndex) : bracket (P a) Q=Complex.I • d a := by
  rw [bracket_sub]
  have hz : bracket (P a) (1:End)=0 := by simp [bracket]
  rw [hz,inverse_P,zero_sub,neg_smul,neg_neg]
private theorem geometric_successor (a : ScalarIndex) (k : ℕ) :
    bracket (P a) (Q^(k+1))=((k+1:ℂ)*Complex.I) • (Q^k*d a) := by
  induction k with
  | zero => simpa only [zero_add,Nat.cast_zero,pow_one,pow_zero,one_mul] using inverse_Q a
  | succ k ih =>
    rw [show k+1+1=(k+1)+1 from rfl,pow_succ,bracket_product,ih,inverse_Q]
    have hm : (Q^k*d a)*Q=Q^(k+1)*d a := by
      rw [mul_assoc,(Q_commute (inverse_d a)).symm.eq,←mul_assoc,←pow_succ]
    simp only [smul_mul_assoc,mul_smul_comm]
    rw [hm]
    push_cast
    simp only [pow_succ]
    module
private theorem theta_native (a : ScalarIndex) (m ell : ℕ) :
    bracket (P a) (T m ell)=(-Complex.I) • (B m ell*d a) := by
  rw [T,phiThetaAction,bracket_sub,geometric_successor,geometric_successor]
  simp only [B,SourceClockPhiRadiusResponseHessian.phiFirstPeak,sub_mul,smul_mul_assoc,smul_sub,smul_smul]
  module
private theorem theta_square_native (a : ScalarIndex) (m ell : ℕ) :
    bracket (P a) ((T m ell)^2)=(-2*Complex.I) • (T m ell*B m ell*d a) := by
  rw [pow_two,bracket_product,theta_native]
  have hc : Commute (T m ell) (B m ell*d a) :=
    ((first_commute ((jet_theta_commute (Commute.refl S) m ell).symm) m ell).symm.mul_right
      ((jet_theta_commute (inverse_D a) m ell).mul_right ((jet_theta_commute (Commute.refl S) m ell).pow_right 2)))
  simp only [smul_mul_assoc,mul_smul_comm]
  rw [←hc.eq]
  simp only [←mul_assoc]
  module
private theorem inverse_theta_square_native (a : ScalarIndex) (m ell : ℕ) :
    bracket (P a) (S*(T m ell)^2)=(-Complex.I) •
      (d a*(T m ell)^2+(2:ℂ) • (S*T m ell*B m ell*d a)) := by
  rw [bracket_product,inverse_P,theta_square_native]
  simp only [smul_mul_assoc,mul_smul_comm,smul_add,smul_smul]
  module


private def profileCore (m ell:ℕ) : Fin 2 → Fin 2 → End :=
  !![(2:ℂ) • (B m ell*S)-T m ell,(-2:ℂ) • (S*(B m ell*S));
    (-2:ℂ) • (S*(B m ell*S)),S^2*(T m ell+(2:ℂ) • (B m ell*S))]
private def CoreReturn (A:Op) (a:End) : Prop := ∀f:QuantumTest,A (embed f)=embed (a f)
private theorem core_mul {A B:Op} {a b:End} (ha:CoreReturn A a) (hb:CoreReturn B b) :
    CoreReturn (A*B) (a*b) := by intro f;change A (B (embed f))=embed (a (b f));rw [hb,ha]
private theorem core_add {A B:Op} {a b:End} (ha:CoreReturn A a) (hb:CoreReturn B b) :
    CoreReturn (A+B) (a+b) := by intro f;change A (embed f)+B (embed f)=embed (a f+b f);rw [ha,hb,map_add]
private theorem core_sub {A B:Op} {a b:End} (ha:CoreReturn A a) (hb:CoreReturn B b) :
    CoreReturn (A-B) (a-b) := by intro f;change A (embed f)-B (embed f)=embed (a f-b f);rw [ha,hb,map_sub]
private theorem core_smul {A:Op} {a:End} (ha:CoreReturn A a) (c:ℂ) :
    CoreReturn (c • A) (c • a) := by intro f;change c • A (embed f)=embed (c • a f);rw [ha,map_smul]
private theorem gradient_complex {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q:E →L[ℂ] E) (n:ℕ) :
    PositiveContractionRitt.gradient Q n=(n+1:ℂ) • (Q^n*(1-Q)) := by
  unfold PositiveContractionRitt.gradient
  have hr:=RCLike.real_smul_eq_coe_smul (K:=ℂ) (n+1:ℝ) (Q^n*(1-Q))
  simpa only [RCLike.ofReal_add,RCLike.ofReal_natCast,RCLike.ofReal_one] using hr
private theorem boundary_core (j:ℕ) : CoreReturn (boundary j) ((j+1:ℂ) • (Q^j*S)) := by
  unfold boundary
  rw [gradient_complex]
  have hS:(1:Op)-phiComplement=phiInverseBounded:=by unfold phiComplement;abel
  rw [hS]
  exact core_smul (core_mul (phi_power_core j) phi_inverse_core) _
private theorem peak_core (m ell:ℕ) : CoreReturn (peak m ell) (B m ell*S) := by
  have h:=core_sub (boundary_core ell) (boundary_core m)
  simpa only [peak,B,SourceClockPhiRadiusResponseHessian.phiFirstPeak,sub_mul,smul_mul_assoc] using h
private theorem coefficient_core (i j:Fin 2) (m ell:ℕ) : CoreReturn (coefficient m ell i j) (profileCore m ell i j) := by
  have hs:CoreReturn phiInverseBounded S:=phi_inverse_core
  have ht:CoreReturn (phiTail m ell) (T m ell):=phi_tail_core m ell
  have hb:=peak_core m ell
  fin_cases i <;> fin_cases j
  · exact core_sub (core_smul hb 2) ht
  · exact core_smul (core_mul hs hb) (-2)
  · exact core_smul (core_mul hs hb) (-2)
  · have hs2:CoreReturn (phiInverseBounded^2) (S^2):=by simpa only [pow_two] using core_mul hs hs
    exact core_mul hs2 (core_add ht (core_smul hb 2))
private theorem native_profile_core (a:ScalarIndex) (i j:Fin 2) (m ell:ℕ) :
    CoreReturn (nativeColumn a i j m ell) (D a*profileCore m ell i j*T m ell) :=
  core_mul (core_mul (original_phi_direction_core (scalarBasis a)) (coefficient_core i j m ell))
    (phi_tail_core m ell)
private theorem column_source_cases (a:ScalarIndex) (m ell:ℕ) :
    Complex.I • bracket (P a) (r*(T m ell)^2)=D a*((2:ℂ) • (B m ell*S)-T m ell)*T m ell ∧
    Complex.I • bracket (P a) (-(T m ell)^2)=D a*((-2:ℂ) • (S*(B m ell*S)))*T m ell ∧
    Complex.I • bracket (P a) (S*(T m ell)^2)=D a*(S^2*(T m ell+(2:ℂ) • (B m ell*S)))*T m ell := by
  have hrho:bracket (P a) r=Complex.I • D a :=
    (original_phi_radius_native_jet (scalarDirection a)).1
  have hrS (X:End):r*(S*X)=X:=by rw [←mul_assoc,radius_inverse,one_mul]
  have hSrX (X:End):S*(r*X)=X:=by rw [←mul_assoc,inverse_radius,one_mul]
  have hSD:=inverse_D a
  have hBD:=first_commute hSD m ell
  have hTD:=jet_theta_commute hSD m ell
  have hBS:=first_commute (Commute.refl S) m ell
  have hTS:=jet_theta_commute (Commute.refl S) m ell
  have hTB:Commute (T m ell) (B m ell):=jet_theta_commute hBS.symm m ell
  have hrD:Commute r (D a):=real_commute _ _ _ _
  have hSr:Commute S r:=by show S*r=r*S;rw [inverse_radius,radius_inverse]
  have hBr:=first_commute hSr m ell
  have hTr:=jet_theta_commute hSr m ell
  have hi2:Complex.I*(-2*Complex.I)=2:=by
    calc _= -2*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  have hi1:Complex.I*(-Complex.I)=1:=by rw [mul_neg,Complex.I_mul_I,neg_neg]
  refine ⟨?_,?_,?_⟩
  · rw [bracket_product,hrho,theta_square_native]
    simp only [smul_add,smul_mul_assoc,mul_smul_comm,smul_smul,Complex.I_mul_I,hi2,neg_one_smul]
    unfold d
    noncomm_ring [hSD.eq,hSD.left_comm,hBD.eq,hBD.left_comm,hTD.eq,hTD.left_comm,
      hBS.eq,hBS.left_comm,hTS.eq,hTS.left_comm,hTB.eq,hTB.left_comm,
      hrD.eq,hrD.left_comm,hBr.eq,hBr.left_comm,hTr.eq,hTr.left_comm,hrS,hSrX,radius_inverse,inverse_radius]
  · have hn:bracket (P a) (-(T m ell)^2)= -bracket (P a) ((T m ell)^2):=by unfold bracket;noncomm_ring
    rw [hn,theta_square_native,smul_neg,smul_smul,hi2]
    unfold d
    noncomm_ring [hSD.eq,hSD.left_comm,hBD.eq,hBD.left_comm,hTD.eq,hTD.left_comm,
      hBS.eq,hBS.left_comm,hTS.eq,hTS.left_comm,hTB.eq,hTB.left_comm]
    module
  · rw [inverse_theta_square_native,smul_smul,hi1,one_smul]
    unfold d
    noncomm_ring [hSD.eq,hSD.left_comm,hBD.eq,hBD.left_comm,hTD.eq,hTD.left_comm,
      hBS.eq,hBS.left_comm,hTS.eq,hTS.left_comm,hTB.eq,hTB.left_comm]

private theorem metric_jet (a:ScalarIndex) (i j:Fin 2) (m ell:ℕ) :
    nativeColumnCore a i j m ell=D a*profileCore m ell i j*T m ell := by
  obtain ⟨h00,h01,h11⟩:=column_source_cases a m ell
  fin_cases i <;> fin_cases j
  · simpa [nativeColumnCore,nativeMetricCore,profileCore] using h00
  · simpa [nativeColumnCore,nativeMetricCore,profileCore] using h01
  · simpa [nativeColumnCore,nativeMetricCore,profileCore] using h01
  · simpa [nativeColumnCore,nativeMetricCore,profileCore] using h11
/-- The bounded columns are the actual full native jets of the original two-seed metric. -/
theorem actual_native_column_core (a:ScalarIndex) (i j:Fin 2) (m ell:ℕ) (f:QuantumTest) :
    nativeColumn a i j m ell (embed f)=embed (nativeColumnCore a i j m ell f) := by
  rw [metric_jet]
  exact native_profile_core a i j m ell f

end LowEnergy.SourceClockPhiNativeJointPayment
