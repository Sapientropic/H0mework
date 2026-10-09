import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRenormalizedSecondGreen
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiFixedSourceJets
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRittHigherGradient
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiNativeJointPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiFixedSecondGreenTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRenormalizedSecondGreen SourceClockPhiFixedSourceJets
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockPhiRadiusResponseHessian
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeJointPayment
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarVirialBulk SourcePhysicalKineticSquare
open SourceGaugeRadialCurrent SourceGaugeRadialPair
open MeasureTheory Filter GaussFockWeights GaussDensityCore
open scoped ContDiff Topology InnerProductSpace
abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev S:End:=phiInverseAction
private abbrev Q:End:=1-S
private abbrev r:End:=phiRadiusAction
private abbrev U:End:=inverseVolumeAction
private abbrev a:End:=inverseRootAction
private abbrev D:End:=combinedGenerator
private abbrev A:End:=combinedConjugate
private abbrev Ad:End:= -D*a
private abbrev T (m ell:ℕ):End:=phiThetaAction m ell
private abbrev P:End:=S^2-1
private abbrev C:End:=inverseCurrent
private abbrev B:End:=inverseDoubleCurrent
private def L:End:=((sourceTime 0:ℂ)/8) • ((S^2-S^4)*U)
attribute [local irreducible] diagonalAction

private theorem real_commute (c b:SourceCoordinateSlice → ℝ)
    (hc: ∀ z:physicalChart,ContDiffAt ℝ ∞ c z.val) (hb: ∀ z:physicalChart,ContDiffAt ℝ ∞ b z.val):
    Commute (multiply c hc) (multiply b hb) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (b z:ℂ) (f z)
private theorem inverse_radius:S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse:r*S=(1:End):=(real_commute _ _ _ _).eq.symm.trans inverse_radius
private theorem inverse_theta (m ell:ℕ):Commute S (T m ell):=
  (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (m+1)).sub_right
    (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (ell+1))
private theorem core_step_read (g:diagonal.domain):
    coreEquiv.symm (GaussAdjointHistory.coreStep g)=H0 (coreEquiv.symm g) := by
  have h:coreEquiv (H0 (coreEquiv.symm g))=GaussAdjointHistory.coreStep g := by
    apply Subtype.ext
    rfl
  rw [←h,coreEquiv.symm_apply_apply]

/-- This is the original fixed column, read back from its own H0 two-seed cancellation. -/
theorem actual_fixed_column_source (m ell:ℕ) (g:diagonal.domain):
    fixedColumn m ell g= -(A ((S*T m ell) (phiRadiusCurrent (coreEquiv.symm g)))) := by
  have hr:coreEquiv.symm (phiRadiusSource g)=r (coreEquiv.symm g):=coreEquiv.symm_apply_apply _
  have hcol:fixedColumn m ell g=
      ∑i:Fin 2,A (phaseRow m ell i (coreEquiv.symm (GaussAdjointHistory.coreStep (inputSeed g i)))) := rfl
  rw [hcol,Fin.sum_univ_two]
  simp only [phaseRow,inputSeed,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [core_step_read,core_step_read,hr]
  have he:H0 (r (coreEquiv.symm g))=r (H0 (coreEquiv.symm g))+phiRadiusCurrent (coreEquiv.symm g) := by
    have h:=LinearMap.congr_fun original_phi_radius_hamiltonian_current (coreEquiv.symm g)
    change H0 (r (coreEquiv.symm g))-r (H0 (coreEquiv.symm g))=phiRadiusCurrent (coreEquiv.symm g) at h
    linear_combination (norm:=module) h
  have hSr:S*T m ell*r=T m ell := by
    rw [(inverse_theta m ell).eq,mul_assoc,inverse_radius,mul_one]
  have hs:=LinearMap.congr_fun hSr (H0 (coreEquiv.symm g))
  rw [he]
  simp only [LinearMap.neg_apply,Module.End.mul_apply,map_add,map_neg] at hs ⊢
  have hsA:=congrArg A hs
  linear_combination (norm:=module) -hsA

private theorem inverse_bracket (X:End):bracket X S= -(S*bracket X r*S) := by
  have h1:S*X*r*S=S*X := by rw [mul_assoc,radius_inverse,mul_one]
  have h2:S*r*X*S=X*S := by rw [inverse_radius,one_mul]
  unfold bracket
  linear_combination (norm:=noncomm_ring) h1-h2
private theorem reciprocal_smooth:ContDiff ℝ ∞ phiReciprocal :=
  SourceClockRadiusResponseAffine.affine_radius_smooth.inv (fun _=>(Real.sqrt_pos.2 (by positivity)).ne')
private theorem reciprocal_gauge_derivative (z:SourceCoordinateSlice):
    fderiv ℝ phiReciprocal z (gaugeEuler z)=0 := by
  have hp:HasDerivAt (fun t:ℝ=>z+t • gaugeEuler z) (gaugeEuler z) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const (gaugeEuler z) |>.const_add z
  have hd:HasFDerivAt phiReciprocal (fderiv ℝ phiReciprocal z) z:=
    (reciprocal_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hh:=hd.comp_hasDerivAt_of_eq 0 hp (by simp)
  have he:(fun t:ℝ=>phiReciprocal (z+t • gaugeEuler z))=fun _=>phiReciprocal z := by
    funext t
    unfold phiReciprocal phiRadius SourceClockRadiusResponseAffine.affineRadius scalarField gaugeEuler
    simp only [Prod.smul_mk,Prod.snd_add,Prod.fst_add,smul_zero,add_zero]
  change HasDerivAt (fun t:ℝ=>phiReciprocal (z+t • gaugeEuler z))
    (fderiv ℝ phiReciprocal z (gaugeEuler z)) 0 at hh
  rw [he] at hh
  exact hh.unique (hasDerivAt_const 0 _)
private theorem inverse_real (f:QuantumTest):(S f:SourceCoordinateSlice → FockFiber)=fun z=>phiReciprocal z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm
private theorem gauge_inverse:Commute SourceGaugeScaleTransport.generator S := by
  have hg:Commute gaugeEulerAction S := by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    change gaugeEulerAction (S f) z=S (gaugeEulerAction f) z
    rw [gauge_euler_apply,inverse_real,fderiv_fun_smul (reciprocal_smooth.differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
    simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,reciprocal_gauge_derivative]
    change phiReciprocal z • fderiv ℝ f z (gaugeEuler z)+0 • f z=
      (phiReciprocal z:ℂ) • gaugeEulerAction f z
    rw [zero_smul,add_zero,gauge_euler_apply]
    exact (algebraMap_smul ℂ _ _).symm
  unfold SourceGaugeScaleTransport.generator
  exact hg.add_left ((Commute.one_left S).smul_left _)

private theorem combined_inverse:bracket D S=S^3-S := by
  have he:bracket phiEulerAction S=S^3-S := by
    rw [inverse_bracket,original_phi_euler_radius]
    calc
      _=S*S*S-S*r*S := by noncomm_ring
      _=_:=by rw [inverse_radius,one_mul];noncomm_ring
  have hp:bracket SourceScalarAffineScaleTransport.generator S=S^3-S := by
    unfold SourceScalarAffineScaleTransport.generator bracket at he ⊢
    linear_combination (norm:=noncomm_ring) he
  have hg:bracket SourceGaugeScaleTransport.generator S=0:=sub_eq_zero.mpr gauge_inverse.eq
  unfold D combinedGenerator bracket
  unfold bracket at hp hg
  linear_combination (norm:=noncomm_ring) hp-hg

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
private def phiComplement : GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H := 1-phiInverseBounded
private theorem phi_complement_positive : 0 ≤ phiComplement :=
  sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ phi_inverse_positive).mp phi_inverse_norm)
private theorem phi_complement_le_one : phiComplement ≤ 1 := sub_le_self _ phi_inverse_positive
private theorem phi_power_core (n:ℕ) (f:QuantumTest):
    (phiComplement^n) (embed f)=embed ((Q^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change phiComplement ((phiComplement^n) (embed f))=embed (Q ((Q^n) f))
    rw [ih]
    change embed ((Q^n) f)-phiInverseBounded (embed ((Q^n) f))=_
    rw [phi_inverse_core,←map_sub]
    rfl
private theorem inverse_power_core (n:ℕ) (f:QuantumTest):
    (phiInverseBounded^n) (embed f)=embed ((S^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change phiInverseBounded ((phiInverseBounded^n) (embed f))=embed (S ((S^n) f))
    rw [ih,phi_inverse_core]
private def coefficient (n:ℕ) (j:Fin 5):ℝ:=
  ![1,(n+1:ℝ),(n:ℝ)*(n+1:ℝ),(n:ℝ)*(n+1:ℝ)*((n:ℝ)-1),
    (n:ℝ)*(n+1:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)] j
private def boundaryCore (j:Fin 5) (n:ℕ):End:=
  (coefficient n j:ℂ) • (S^(j:ℕ)*Q^(n+1-(j:ℕ)))
private def boundaryRead (j:Fin 5) (n:ℕ):GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H:=
  coefficient n j • (phiInverseBounded^(j:ℕ)*phiComplement^(n+1-(j:ℕ)))
private def jet (j:Fin 5) (m ell:ℕ):End:=(-1:ℂ)^(j:ℕ) • (boundaryCore j m-boundaryCore j ell)
private theorem boundary_core (j:Fin 5) (n:ℕ) (f:QuantumTest):
    boundaryRead j n (embed f)=embed (boundaryCore j n f) := by
  unfold boundaryRead boundaryCore
  simp only [smul_apply,mul_apply_eq_comp,LinearMap.smul_apply,Module.End.mul_apply,map_smul]
  rw [phi_power_core,inverse_power_core]
  exact (algebraMap_smul ℂ _ _).symm
private theorem inverse_complement:Commute phiInverseBounded phiComplement:=
  (Commute.one_right _).sub_right (Commute.refl _)
private theorem boundary_zero (n:ℕ):boundaryRead ⟨0,by decide⟩ n=phiComplement^(n+1) := by
  simp [boundaryRead,coefficient]
private theorem boundary_first (n:ℕ):boundaryRead ⟨1,by decide⟩ n=PositiveContractionRitt.gradient phiComplement n := by
  change (n+1:ℝ) • (phiInverseBounded*phiComplement^n)=
    (n+1:ℝ) • (phiComplement^n*(1-phiComplement))
  rw [show (1:GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H)-phiComplement=phiInverseBounded by unfold phiComplement;abel]
  exact congrArg (fun R:GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H=>(n+1:ℝ) • R) (inverse_complement.pow_right n).eq
private theorem boundary_second (n:ℕ):boundaryRead ⟨2,by decide⟩ n=PositiveContractionRitt.secondGradient phiComplement n := by
  have he:(n+1-2:ℕ)=n-1:=by omega
  change ((n:ℝ)*(n+1:ℝ)) • (phiInverseBounded^2*phiComplement^(n+1-2))=
    ((n:ℝ)*(n+1:ℝ)) • (phiComplement^(n-1)*(1-phiComplement)^2)
  rw [he,show (1:GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H)-phiComplement=phiInverseBounded by unfold phiComplement;abel]
  exact congrArg (fun R:GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H=>((n:ℝ)*(n+1:ℝ)) • R) ((inverse_complement.pow_left 2).pow_right (n-1)).eq
private theorem boundary_third (n:ℕ):boundaryRead ⟨3,by decide⟩ n=PositiveContractionRitt.thirdGradient phiComplement n := by
  have he:(n+1-3:ℕ)=n-2:=by omega
  change ((n:ℝ)*(n+1:ℝ)*((n:ℝ)-1)) • (phiInverseBounded^3*phiComplement^(n+1-3))=
    ((n:ℝ)*(n+1:ℝ)*((n:ℝ)-1)) • (phiComplement^(n-2)*(1-phiComplement)^3)
  rw [he,show (1:GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H)-phiComplement=phiInverseBounded by unfold phiComplement;abel]
  exact congrArg (fun R:GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H=>((n:ℝ)*(n+1:ℝ)*((n:ℝ)-1)) • R) ((inverse_complement.pow_left 3).pow_right (n-2)).eq
private theorem boundary_fourth (n:ℕ):boundaryRead ⟨4,by decide⟩ n=PositiveContractionRitt.fourthGradient phiComplement n := by
  have he:(n+1-4:ℕ)=n-3:=by omega
  change ((n:ℝ)*(n+1:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)) • (phiInverseBounded^4*phiComplement^(n+1-4))=
    ((n:ℝ)*(n+1:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)) • (phiComplement^(n-3)*(1-phiComplement)^4)
  rw [he,show (1:GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H)-phiComplement=phiInverseBounded by unfold phiComplement;abel]
  exact congrArg (fun R:GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H=>((n:ℝ)*(n+1:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)) • R) ((inverse_complement.pow_left 4).pow_right (n-3)).eq

private def Tail (f:ℕ → ℕ → QuantumTest):Prop:=
      ∀ ε:ℝ,0 < ε → ∃ N:ℕ, ∀ m, N ≤ m → ∀ ell,m ≤ ell → ‖embed (f m ell)‖ < ε
private theorem tail_zero:Tail (fun _ _=>0) := by
  intro ε hε
  exact ⟨0,fun _ _ _ _=>by simpa only [map_zero,norm_zero] using hε⟩
private theorem tail_add{f h:ℕ → ℕ → QuantumTest}(hf:Tail f) (hh:Tail h):Tail (fun m ell=>f m ell+h m ell) := by
  intro ε hε
  obtain ⟨N,hN⟩:=hf (ε/2) (by positivity)
  obtain ⟨M,hM⟩:=hh (ε/2) (by positivity)
  refine ⟨max N M,fun m hm ell hel=>?_⟩
  rw [map_add]
  exact (norm_add_le _ _).trans_lt (by linarith [hN m (le_trans (le_max_left _ _) hm) ell hel,hM m (le_trans (le_max_right _ _) hm) ell hel])
private theorem tail_smul (c:ℂ){f:ℕ → ℕ → QuantumTest}(hf:Tail f):Tail (fun m ell=>c • f m ell) := by
  intro ε hε
  obtain ⟨N,hN⟩:=hf (ε/(‖c‖+1)) (by positivity)
  refine ⟨N,fun m hm ell hel=>?_⟩
  rw [map_smul,norm_smul]
  have hh:=hN m hm ell hel
  have hp:0 < ‖c‖+1:=by positivity
  have hb:‖c‖*‖embed (f m ell)‖ ≤ (‖c‖+1)*‖embed (f m ell)‖:=by nlinarith [norm_nonneg (embed (f m ell))]
  exact hb.trans_lt ((mul_lt_mul_of_pos_left hh hp).trans_eq (by field_simp))
private theorem tail_congr{f h:ℕ → ℕ → QuantumTest}(hf:Tail f) (he: ∀ m ell,f m ell=h m ell):Tail h := by
  intro ε hε
  obtain ⟨N,hN⟩:=hf ε hε
  exact ⟨N,fun m hm ell hel=>by rw [←he];exact hN m hm ell hel⟩
private theorem jet_tail (j:Fin 5) (f:QuantumTest):Tail (fun m ell=>jet j m ell f) := by
  have hj: ∀ m ell,embed (jet j m ell f)=(-1:ℂ)^(j:ℕ) •
      (boundaryRead j m (embed f)-boundaryRead j ell (embed f)) := by
    intro m ell
    simp only [jet,LinearMap.smul_apply,LinearMap.sub_apply,map_smul,map_sub,←boundary_core]
  intro ε hε
  have hnorm:‖(-1:ℂ)^(j:ℕ)‖=1:=by simp
  rcases j with ⟨j,hjlt⟩
  interval_cases j
  · obtain ⟨N,hN⟩:=SourceRelativePowerTail.decreasing_distance_tail
      (fun n=>(phiComplement^n) (embed f))
      (fun _ _ h=>SourceRelativePowerTail.positive_power_distance phiComplement
        phi_complement_positive phi_complement_le_one (embed f) h) ε hε
    refine ⟨N,fun m hm ell hel=>?_⟩
    rw [hj,norm_smul,hnorm,one_mul,boundary_zero,boundary_zero]
    exact hN m hm ell hel
  all_goals
    have ht:Tendsto (fun n=>boundaryRead ⟨_,hjlt⟩ n (embed f)) atTop (𝓝 0) := by
      first
      | simpa only [boundary_first] using PositiveContractionRitt.gradient_strong phiComplement phi_complement_positive phi_complement_le_one (embed f)
      | simpa only [boundary_second] using PositiveContractionRitt.secondGradient_strong phiComplement phi_complement_positive phi_complement_le_one (embed f)
      | simpa only [boundary_third] using PositiveContractionRitt.thirdGradient_strong phiComplement phi_complement_positive phi_complement_le_one (embed f)
      | simpa only [boundary_fourth] using PositiveContractionRitt.fourthGradient_strong phiComplement phi_complement_positive phi_complement_le_one (embed f)
    obtain ⟨N,hN⟩:=Metric.tendsto_atTop.1 ht (ε/2) (by positivity)
    refine ⟨N,fun m hm ell hel=>?_⟩
    rw [hj,norm_smul,hnorm,one_mul]
    have hm':=hN m hm
    have hl':=hN ell (le_trans hm hel)
    simp only [dist_zero_right] at hm' hl'
    exact (norm_sub_le _ _).trans_lt (by linarith)

private theorem bracket_product (X Y Z:End):bracket X (Y*Z)=bracket X Y*Z+Y*bracket X Z := by
  unfold bracket
  noncomm_ring
private theorem bracket_sub (X Y Z:End):bracket X (Y-Z)=bracket X Y-bracket X Z := by
  unfold bracket
  noncomm_ring
private theorem bracket_smul (X Y:End) (c:ℂ):bracket X (c • Y)=c • bracket X Y := by
  unfold bracket
  simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem first_power (X Y Z:End) (h:bracket X Y=Z) (hc:Commute Z Y) (k:ℕ):
    bracket X (Y^(k+1))=(k+1:ℂ) • (Y^k*Z) := by
  induction k with
  | zero => simpa only [zero_add,pow_one,pow_zero,Nat.cast_zero,zero_add,one_mul,one_smul] using h
  | succ k ih =>
    rw [pow_succ,bracket_product,ih,h]
    have hp:Y^k*Z*Y=Y^(k+1)*Z:=by rw [mul_assoc,hc.eq,←mul_assoc,←pow_succ]
    simp only [smul_mul_assoc,hp]
    push_cast
    module
private theorem SP:Commute S P := (Commute.refl S).pow_right 2 |>.sub_right (Commute.one_right S)
private theorem SQ:Commute S Q := (Commute.one_right S).sub_right (Commute.refl S)
private theorem PQ:Commute P Q :=
  (Commute.one_right P).sub_right SP.symm
private theorem D_S_power (j:ℕ):bracket D (S^j)=(j:ℂ) • (S^j*P) := by
  induction j with
  | zero => simp [bracket]
  | succ j ih =>
    rw [pow_succ,bracket_product,ih,combined_inverse]
    have hδ:S^3-S=S*P:=by unfold P;noncomm_ring
    rw [hδ]
    have hp:S^j*P*S=S^(j+1)*P:=by rw [mul_assoc,SP.symm.eq,←mul_assoc,←pow_succ]
    simp only [smul_mul_assoc,hp,←mul_assoc,←pow_succ]
    push_cast
    module
private theorem D_Q_power (k:ℕ):bracket D (Q^(k+1))= -(k+1:ℂ) • (S*Q^k*P) := by
  have he:bracket D Q= -(S*P) := by
    have h:=combined_inverse
    unfold Q bracket at h ⊢
    unfold P
    linear_combination (norm:=noncomm_ring) -h
  have hc:Commute (-(S*P)) Q:=(SQ.mul_left PQ).neg_left
  rw [first_power D Q (-(S*P)) he hc]
  rw [mul_neg,←mul_assoc,(SQ.symm.pow_left k).eq]
  module
private theorem coefficient_step (n:ℕ) (hn:4 ≤ n) (j:Fin 4):
    (coefficient n ⟨(j:ℕ)+1,by omega⟩:ℂ)=
      (coefficient n ⟨j,by omega⟩:ℂ)*((n-(j:ℕ):ℕ)+1:ℂ) := by
  rcases j with ⟨j,hj⟩
  interval_cases j <;> dsimp [coefficient]
  all_goals try rw [Nat.cast_sub (by omega)]
  all_goals push_cast;ring
private theorem boundary_D (j:Fin 4) (n:ℕ) (hn:4 ≤ n):
    bracket D (boundaryCore ⟨j,by omega⟩ n)=
      (j:ℂ) • (boundaryCore ⟨j,by omega⟩ n*P)-
      boundaryCore ⟨(j:ℕ)+1,by omega⟩ n*P := by
  have he:n+1-(j:ℕ)=(n-(j:ℕ))+1:=by omega
  have hnxt:n+1-((j:ℕ)+1)=n-(j:ℕ):=by omega
  unfold boundaryCore
  rw [bracket_smul,bracket_product,D_S_power,he,D_Q_power,hnxt,coefficient_step n hn j]
  have hp:S^(j:ℕ)*P*Q^(n-(j:ℕ)+1)=S^(j:ℕ)*Q^(n-(j:ℕ)+1)*P:=by rw [mul_assoc,(PQ.pow_right _).eq,←mul_assoc]
  have hs:S^(j:ℕ)*(S*Q^(n-(j:ℕ))*P)=S^((j:ℕ)+1)*Q^(n-(j:ℕ))*P:=by simp only [←mul_assoc,←pow_succ]
  simp only [smul_add,smul_mul_assoc,mul_smul_comm,smul_smul,hp,hs]
  module
private theorem jet_D (j:Fin 4) (m ell:ℕ) (hm:4 ≤ m) (he:m ≤ ell):
    bracket D (jet ⟨j,by omega⟩ m ell)=
      (j:ℂ) • (jet ⟨j,by omega⟩ m ell*P)+jet ⟨(j:ℕ)+1,by omega⟩ m ell*P := by
  unfold jet
  rw [bracket_smul,bracket_sub,boundary_D j m hm,boundary_D j ell (le_trans hm he)]
  simp only [smul_mul_assoc,sub_mul,pow_succ]
  module
private theorem aS:Commute a S:=real_commute _ _ _ _
private theorem a_jet (j:Fin 5) (m ell:ℕ):Commute a (jet j m ell) := by
  have hq:Commute a Q:=(Commute.one_right a).sub_right aS
  unfold jet boundaryCore
  exact (((aS.pow_right _).mul_right (hq.pow_right _)).smul_right _ |>.sub_right
    (((aS.pow_right _).mul_right (hq.pow_right _)).smul_right _)).smul_right _
private theorem jet_Ad (j:Fin 4) (m ell:ℕ) (hm:4 ≤ m) (he:m ≤ ell):
    Ad*jet ⟨j,by omega⟩ m ell=
      jet ⟨j,by omega⟩ m ell*Ad-(j:ℂ) • (jet ⟨j,by omega⟩ m ell*P*a)-
      jet ⟨(j:ℕ)+1,by omega⟩ m ell*P*a := by
  have h:=jet_D j m ell hm he
  have ha: a*jet ⟨j,by omega⟩ m ell=jet ⟨j,by omega⟩ m ell*a:=(a_jet _ m ell).eq
  unfold Ad
  unfold bracket at h
  rw [mul_assoc,ha,←mul_assoc]
  linear_combination (norm:=noncomm_ring) -(h*a)

private theorem rS:Commute r S := radius_inverse.trans inverse_radius.symm
private theorem rQ:Commute r Q := (Commute.one_right r).sub_right rS
private theorem r_boundary (j:Fin 5) (n:ℕ):Commute r (boundaryCore j n) :=
  ((rS.pow_right _).mul_right (rQ.pow_right _)).smul_right _
private theorem S_boundary (j:Fin 5) (n:ℕ):Commute S (boundaryCore j n) :=
  (((Commute.refl S).pow_right _).mul_right (SQ.pow_right _)).smul_right _
private theorem B_Q:Commute B Q := by
  have h:Commute B S:=sub_eq_zero.mp actual_inverse_third_current_zero
  exact (Commute.one_right B).sub_right h
private theorem B_factor:B=(2:ℂ) • (S^2*L) := by
  have hu:Commute U S:=real_commute _ _ _ _
  have hp:S^2*((S^2-S^4)*U)=U*(S^4-S^6):=by
    rw [((hu.pow_right 4).sub_right (hu.pow_right 6)).eq]
    noncomm_ring
  unfold B inverseDoubleCurrent L
  simp only [mul_smul_comm,smul_smul,hp]
  congr 1
  ring
private theorem jet_zero (m ell:ℕ):jet ⟨0,by decide⟩ m ell=T m ell := by
  simp [jet,boundaryCore,coefficient,T,phiThetaAction,Q]
private theorem coefficient_one (n:ℕ):coefficient n ⟨1,by decide⟩=(n+1:ℝ):=rfl
private theorem coefficient_two (n:ℕ):coefficient n ⟨2,by decide⟩=(n:ℝ)*(n+1:ℝ):=rfl
private theorem coefficient_three (n:ℕ):coefficient n ⟨3,by decide⟩=(n:ℝ)*(n+1:ℝ)*((n:ℝ)-1):=rfl
private theorem jet_first (m ell:ℕ):jet ⟨1,by decide⟩ m ell=S*phiFirstPeak m ell := by
  unfold jet boundaryCore phiFirstPeak
  rw [coefficient_one,coefficient_one]
  simp only [pow_one,Nat.add_sub_cancel,neg_one_smul,mul_sub,mul_smul_comm]
  push_cast
  module
private theorem jet_second (m ell:ℕ):jet ⟨2,by decide⟩ m ell=S^2*phiSecondPeak m ell := by
  unfold jet boundaryCore phiSecondPeak
  rw [coefficient_two,coefficient_two]
  have he: ∀ n:ℕ,n+1-2=n-1:=by intro n;omega
  simp only [he,neg_one_sq,one_smul,mul_sub,mul_smul_comm]
  push_cast
  module
private theorem H_jet_zero (m ell:ℕ):bracket H0 (jet ⟨0,by decide⟩ m ell)=
    jet ⟨1,by decide⟩ m ell*r*C+jet ⟨2,by decide⟩ m ell*L := by
  rw [jet_zero,actual_phi_theta_hamiltonian_source,jet_first,jet_second]
  change phiFirstPeak m ell*C+(1/2:ℂ) • (phiSecondPeak m ell*B)=_
  rw [B_factor]
  have hp:Commute r (phiFirstPeak m ell) := by
    unfold phiFirstPeak
    exact ((rQ.pow_right _).smul_right _).sub_right ((rQ.pow_right _).smul_right _)
  have hs:Commute S (phiSecondPeak m ell) := by
    unfold phiSecondPeak
    exact ((SQ.pow_right _).smul_right _).sub_right ((SQ.pow_right _).smul_right _)
  have h1:S*phiFirstPeak m ell*r=phiFirstPeak m ell:=by rw [mul_assoc,hp.symm.eq,←mul_assoc,inverse_radius,one_mul]
  have h2:phiSecondPeak m ell*(S^2*L)=S^2*phiSecondPeak m ell*L:=by rw [←mul_assoc,(hs.pow_left 2).eq]
  rw [h1,mul_smul_comm,h2,smul_smul]
  norm_num
attribute [local irreducible] L

private theorem H_boundary_first (n:ℕ) (hn:4 ≤ n):
    bracket H0 (boundaryCore ⟨1,by decide⟩ n)=boundaryCore ⟨1,by decide⟩ n*r*C-boundaryCore ⟨2,by decide⟩ n*r*C-
      (2:ℂ) • (boundaryCore ⟨2,by decide⟩ n*L)+boundaryCore ⟨3,by decide⟩ n*L := by
  have hn1:n-1+1=n:=by omega
  have hn2:n-1-1=n-2:=by omega
  have hc:bracket C (Q^n)=-(n:ℂ) • (Q^(n-1)*B) := by
    have he:bracket C Q= -B:=by
      have h:C*S-S*C=B:=actual_inverse_double_current
      unfold Q bracket
      linear_combination (norm:=noncomm_ring) -h
    have h:=first_power C Q (-B) he B_Q.neg_left (n-1)
    rw [hn1] at h
    simpa only [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one,sub_add_cancel,mul_neg,smul_neg,neg_smul] using h
  have hCQ:C*Q^n=Q^n*C-(n:ℂ) • (Q^(n-1)*B):=by
    unfold bracket at hc
    linear_combination (norm:=module) hc
  have hh:=actual_phi_cutoff_power_hamiltonian_source (n-1)
  rw [hn1,hn2] at hh
  rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one] at hh
  have hr1:S*Q^n*r=Q^n:=by rw [mul_assoc,(rQ.pow_right n).symm.eq,←mul_assoc,inverse_radius,one_mul]
  have hr2:S^2*Q^(n-1)*r=S*Q^(n-1):=by
    have hSr:S^2*r=S:=by rw [pow_two,mul_assoc,inverse_radius,mul_one]
    rw [mul_assoc,(rQ.pow_right _).symm.eq,←mul_assoc,hSr]
  have hu:Commute S L := by
    unfold L
    exact (((Commute.refl S).pow_right 2).sub_right ((Commute.refl S).pow_right 4) |>.mul_right
      (real_commute _ _ _ _).symm).smul_right _
  have hp1:Q^(n-1)*S^2*L=S^2*Q^(n-1)*L:=by rw [((SQ.pow_left 2).pow_right _).symm.eq]
  have hp2:S*Q^(n-2)*S^2*L=S^3*Q^(n-2)*L:=by
    rw [mul_assoc S,((SQ.pow_left 2).pow_right _).symm.eq]
    noncomm_ring
  have hb1:boundaryCore ⟨1,by decide⟩ n=(n+1:ℂ) • (S*Q^n):=by
    unfold boundaryCore
    rw [coefficient_one]
    simp only [pow_one,Nat.add_sub_cancel]
    push_cast
    rfl
  have hb2:boundaryCore ⟨2,by decide⟩ n=((n:ℂ)*(n+1:ℂ)) • (S^2*Q^(n-1)):=by
    unfold boundaryCore
    rw [coefficient_two,show n+1-2=n-1 by omega]
    push_cast
    rfl
  have hb3:boundaryCore ⟨3,by decide⟩ n=((n:ℂ)*(n+1:ℂ)*((n:ℂ)-1)) • (S^3*Q^(n-2)):=by
    unfold boundaryCore
    rw [coefficient_three,show n+1-3=n-2 by omega]
    push_cast
    rfl
  rw [hb1,hb2,hb3]
  simp only [sub_add_cancel] at hh
  change bracket H0 (Q^n)= -(n:ℂ) • (Q^(n-1)*C)+
    (((n:ℂ)-1)*(n:ℂ)/2) • (Q^(n-2)*B) at hh
  rw [bracket_smul,bracket_product,show bracket H0 S=C by rfl,hCQ,hh]
  simp only [B_factor,mul_add,mul_sub,smul_mul_assoc,mul_smul_comm,smul_add,smul_sub,smul_smul,←mul_assoc,hr1,hr2,hp1,hp2]
  module
private theorem H_jet_first (m ell:ℕ) (hm:4 ≤ m) (he:m ≤ ell):
    bracket H0 (jet ⟨1,by decide⟩ m ell)=jet ⟨1,by decide⟩ m ell*r*C+jet ⟨2,by decide⟩ m ell*r*C+
      (2:ℂ) • (jet ⟨2,by decide⟩ m ell*L)+jet ⟨3,by decide⟩ m ell*L := by
  unfold jet
  rw [bracket_smul,bracket_sub,H_boundary_first m hm,H_boundary_first ell (le_trans hm he)]
  norm_num only [Fin.val_one,Fin.val_natCast,neg_one_sq,pow_succ]
  simp only [smul_mul_assoc,sub_mul]
  module

private theorem tail_eventual_congr{f h:ℕ → ℕ → QuantumTest}(hf:Tail f) (M:ℕ)
    (he: ∀ m ell,M ≤ m → m ≤ ell → f m ell=h m ell):Tail h := by
  intro ε hε
  obtain ⟨N,hN⟩:=hf ε hε
  refine ⟨max M N,fun m hm ell hel=>?_⟩
  rw [←he m ell (le_trans (le_max_left _ _) hm) hel]
  exact hN m (le_trans (le_max_right _ _) hm) ell hel
private theorem tail_sum{ι:Type*}[Fintype ι](f:ι → ℕ → ℕ → QuantumTest) (hf: ∀ i,Tail (f i)):
    Tail (fun m ell=>∑i,f i m ell) := by
  classical
  have hs: ∀ s:Finset ι,Tail (fun m ell=>∑i∈s,f i m ell):=by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using tail_zero
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using tail_add (hf i) ih
  simpa only [] using hs Finset.univ
private def seedCurrent (g:diagonal.domain):QuantumTest:=phiRadiusCurrent (coreEquiv.symm g)
private def eta (g:diagonal.domain) (j:Fin 2):QuantumTest:=
  ![-A (S (seedCurrent g)),-(a*P) (S (seedCurrent g))] j
private def psi (g:diagonal.domain) (j:Fin 4):QuantumTest:=
  ![H0 (eta g 0), (r*C) (eta g 0)+H0 (eta g 1)+(r*C) (eta g 1),
    L (eta g 0)+(r*C) (eta g 1)+(2:ℂ) • L (eta g 1),L (eta g 1)] j
private theorem A_theta (m ell:ℕ) (hm:4 ≤ m) (he:m ≤ ell):
    A*T m ell=T m ell*A+jet ⟨1,by decide⟩ m ell*a*P := by
  have h:=jet_D ⟨0,by decide⟩ m ell hm he
  rw [jet_zero] at h
  norm_num only [Fin.val_zero,Nat.cast_zero,zero_smul,zero_add] at h
  have ha:Commute a (T m ell):=by simpa only [jet_zero] using a_jet ⟨0,by decide⟩ m ell
  change (a*D)*T m ell=T m ell*(a*D)+jet ⟨1,by decide⟩ m ell*a*P
  unfold bracket at h
  have hj:Commute a (jet ⟨1,by decide⟩ m ell):=a_jet _ m ell
  have hd:D*T m ell=T m ell*D+jet ⟨1,by decide⟩ m ell*P:=by
    linear_combination (norm:=noncomm_ring) h
  rw [mul_assoc,hd,mul_add]
  simp only [←mul_assoc]
  rw [ha.eq,hj.eq]
private theorem column_expansion (m ell:ℕ) (hm:4 ≤ m) (he:m ≤ ell) (g:diagonal.domain):
    fixedColumn m ell g=∑j:Fin 2,jet ⟨j,by omega⟩ m ell (eta g j) := by
  rw [actual_fixed_column_source,Fin.sum_univ_two]
  simp only [Fin.coe_ofNat_eq_mod,Nat.reduceMod,eta,Matrix.cons_val_zero,Matrix.cons_val_one,jet_zero]
  have h:=LinearMap.congr_fun (A_theta m ell hm he) (S (seedCurrent g))
  have hs:S*T m ell=T m ell*S:=(inverse_theta m ell).eq
  rw [hs]
  simp only [Module.End.mul_apply,LinearMap.add_apply,map_neg] at h ⊢
  change -(A (T m ell (S (seedCurrent g))))= -(T m ell (A (S (seedCurrent g))))-
    jet ⟨1,by decide⟩ m ell (a (P (S (seedCurrent g))))
  linear_combination (norm:=module) -h
private theorem hcolumn_expansion (m ell:ℕ) (hm:4 ≤ m) (he:m ≤ ell) (g:diagonal.domain):
    H0 (fixedColumn m ell g)=∑j:Fin 4,jet ⟨j,by omega⟩ m ell (psi g j) := by
  rw [column_expansion m ell hm he,map_sum]
  rw [Fin.sum_univ_two]
  have h0:=LinearMap.congr_fun (H_jet_zero m ell) (eta g 0)
  have h1:=LinearMap.congr_fun (H_jet_first m ell hm he) (eta g 1)
  simp only [bracket,Module.End.mul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply] at h0 h1
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_one,Fin.val_succ,Fin.sum_univ_zero,
    psi,Matrix.cons_val_zero,Matrix.cons_val_succ,map_add,map_smul,Module.End.mul_apply]
  linear_combination (norm:=module) h0+h1
private theorem column_tail (g:diagonal.domain):Tail (fun m ell=>fixedColumn m ell g) := by
  have ht:Tail (fun m ell=>∑j:Fin 2,jet ⟨j,by omega⟩ m ell (eta g j)):=by
    apply tail_sum
    intro j
    exact jet_tail ⟨j,by omega⟩ (eta g j)
  apply tail_eventual_congr ht 4
  intro m ell hm he
  exact (column_expansion m ell hm he g).symm
private theorem hcolumn_tail (g:diagonal.domain):Tail (fun m ell=>H0 (fixedColumn m ell g)) := by
  have ht:Tail (fun m ell=>∑j:Fin 4,jet ⟨j,by omega⟩ m ell (psi g j)):=by
    apply tail_sum
    intro j
    exact jet_tail ⟨j,by omega⟩ (psi g j)
  apply tail_eventual_congr ht 4
  intro m ell hm he
  exact (hcolumn_expansion m ell hm he g).symm
private theorem adjoint_jet_tail (j:Fin 4) (f:QuantumTest):Tail (fun m ell=>Ad (jet ⟨j,by omega⟩ m ell f)) := by
  have ht:Tail (fun m ell=>jet ⟨j,by omega⟩ m ell (Ad f)+
      (-(j:ℂ)) • jet ⟨j,by omega⟩ m ell ((P*a) f)+
      (-1:ℂ) • jet ⟨(j:ℕ)+1,by omega⟩ m ell ((P*a) f)):=
    tail_add (tail_add (jet_tail _ _) (tail_smul _ (jet_tail _ _))) (tail_smul _ (jet_tail _ _))
  apply tail_eventual_congr ht 4
  intro m ell hm he
  have h:=LinearMap.congr_fun (jet_Ad j m ell hm he) f
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply] at h
  linear_combination (norm:=module) -h
private theorem adjoint_column_tail (g:diagonal.domain):Tail (fun m ell=>Ad (fixedColumn m ell g)) := by
  have ht:=tail_sum (fun j:Fin 2=>fun m ell=>Ad (jet ⟨j,by omega⟩ m ell (eta g j)))
    (fun j=>adjoint_jet_tail ⟨j,by omega⟩ _)
  apply tail_eventual_congr ht 4
  intro m ell hm he
  rw [column_expansion m ell hm he,map_sum]
private theorem adjoint_hcolumn_tail (g:diagonal.domain):Tail (fun m ell=>Ad (H0 (fixedColumn m ell g))) := by
  have ht:=tail_sum (fun j:Fin 4=>fun m ell=>Ad (jet ⟨j,by omega⟩ m ell (psi g j)))
    (fun j=>adjoint_jet_tail j _)
  apply tail_eventual_congr ht 4
  intro m ell hm he
  rw [hcolumn_expansion m ell hm he,map_sum]

private theorem phi_power_norm (n:ℕ) (x:H):‖(phiComplement^n) x‖ ≤ ‖x‖ := by
  have hn:‖phiComplement‖ ≤ 1:=(CStarAlgebra.norm_le_one_iff_of_nonneg _ phi_complement_positive).mpr phi_complement_le_one
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp]
    exact ((phiComplement.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _))).trans ih
private theorem theta_norm (m ell:ℕ) (f:QuantumTest):‖embed (T m ell f)‖ ≤ 2*‖embed f‖ := by
  have ht:embed (T m ell f)=(phiComplement^(m+1)) (embed f)-(phiComplement^(ell+1)) (embed f):=by
    rw [phi_power_core,phi_power_core,←map_sub]
    rfl
  rw [ht]
  exact (norm_sub_le _ _).trans (by linarith [phi_power_norm (m+1) (embed f),phi_power_norm (ell+1) (embed f)])
private theorem row_norm (m ell:ℕ) (i:Fin 2) (f:QuantumTest):
    ‖embed (phaseRow m ell i f)‖ ≤ 2*‖embed f‖ := by
  fin_cases i
  · exact theta_norm m ell f
  · change ‖embed (-(S (T m ell f)))‖ ≤ 2*‖embed f‖
    rw [map_neg,norm_neg,←phi_inverse_core]
    have hs:‖phiInverseBounded (embed (T m ell f))‖ ≤ ‖embed (T m ell f)‖:=
      (phiInverseBounded.le_opNorm _).trans ((mul_le_mul_of_nonneg_right phi_inverse_norm (norm_nonneg _)).trans_eq (one_mul _))
    exact hs.trans (theta_norm m ell f)
private theorem row_tail (i:Fin 2){f:ℕ → ℕ → QuantumTest}(hf:Tail f):Tail (fun m ell=>phaseRow m ell i (f m ell)) := by
  intro ε hε
  obtain ⟨N,hN⟩:=hf (ε/2) (by positivity)
  exact ⟨N,fun m hm ell he=>(row_norm m ell i _).trans_lt (by linarith [hN m hm ell he])⟩
private theorem second_tester_tail (g:diagonal.domain) (i:Fin 2):Tail (fun m ell=>fixedSecondTester m ell g i) :=
  row_tail i (adjoint_hcolumn_tail g)
private theorem first_tester_tail (g:diagonal.domain) (i:Fin 2):Tail (fun m ell=>fixedFirstTester m ell g i) :=
  row_tail i (adjoint_column_tail g)
private def endpoint (g:diagonal.domain) (j:Fin 6) (m ell:ℕ):QuantumTest:=
  ![fixedColumn m ell g,H0 (fixedColumn m ell g),fixedSecondTester m ell g 0,
    fixedFirstTester m ell g 0,fixedSecondTester m ell g 1,fixedFirstTester m ell g 1] j
private theorem endpoint_tail (g:diagonal.domain) (j:Fin 6):Tail (endpoint g j) := by
  fin_cases j
  · exact column_tail g
  · exact hcolumn_tail g
  · exact second_tester_tail g 0
  · exact first_tester_tail g 0
  · exact second_tester_tail g 1
  · exact first_tester_tail g 1
private theorem finite_square_tail {E:Type*}[NormedAddCommGroup E]
    (u:Fin 6 → ℕ → ℕ → E)
    (ht: ∀ j:Fin 6, ∀ δ:ℝ,0<δ → ∃ N:ℕ, ∀ m,N ≤ m → ∀ ell,m ≤ ell → ‖u j m ell‖<δ)
    (ε:ℝ) (hε:0<ε): ∃ N:ℕ, ∀ m,N ≤ m → ∀ ell,m ≤ ell → ∑j:Fin 6,‖u j m ell‖^2 ≤ ε := by
  classical
  have hδ:0<Real.sqrt ε/3:=by positivity
  choose Ns hNs using (fun j:Fin 6=>ht j (Real.sqrt ε/3) hδ)
  refine ⟨Finset.univ.sup Ns,fun m hm ell he=>?_⟩
  have hb: ∀ j:Fin 6,‖u j m ell‖^2 ≤ ε/9:=by
    intro j
    have hN:Ns j ≤ m:=(Finset.le_sup (f:=Ns) (Finset.mem_univ j)).trans hm
    have h:=hNs j m hN ell he
    have hs:=Real.sq_sqrt hε.le
    nlinarith [norm_nonneg (u j m ell),Real.sqrt_nonneg ε]
  have hsum:(∑j:Fin 6,‖u j m ell‖^2) ≤ ∑j:Fin 6,ε/9:=Finset.sum_le_sum (fun j _=>hb j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsum
  linarith
/-- A single source-generated N pays the original fixed-column and both Green testers. -/
theorem actual_fixed_second_green_endpoint_common_tail (g:diagonal.domain) (ε:ℝ) (hε:0<ε):
     ∃ N:ℕ, ∀ m:ℕ,N ≤ m → ∀ ell:ℕ,m ≤ ell →
      ‖embed (fixedColumn m ell g)‖^2+‖embed (diagonalAction (fixedColumn m ell g))‖^2+
        ∑i:Fin 2,(‖embed (fixedSecondTester m ell g i)‖^2+‖embed (fixedFirstTester m ell g i)‖^2) ≤ ε := by
  have ht: ∀ j:Fin 6, ∀ δ:ℝ,0<δ → ∃ N:ℕ, ∀ m,N ≤ m → ∀ ell,m ≤ ell → ‖embed (endpoint g j m ell)‖<δ :=
    fun j=>endpoint_tail g j
  obtain ⟨N,hN⟩:=finite_square_tail (fun j m ell=>embed (endpoint g j m ell)) ht ε hε
  refine ⟨N,fun m hm ell he=>?_⟩
  have hs:(∑j:Fin 6,‖embed (endpoint g j m ell)‖^2)=
      ‖embed (fixedColumn m ell g)‖^2+‖embed (H0 (fixedColumn m ell g))‖^2+
        ∑i:Fin 2,(‖embed (fixedSecondTester m ell g i)‖^2+‖embed (fixedFirstTester m ell g i)‖^2):=by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,endpoint,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
    rw [show (Fin.succ (0:Fin 1):Fin 2)=1 by rfl]
    ring
  change ‖embed (fixedColumn m ell g)‖^2+‖embed (H0 (fixedColumn m ell g))‖^2+
    ∑i:Fin 2,(‖embed (fixedSecondTester m ell g i)‖^2+‖embed (fixedFirstTester m ell g i)‖^2) ≤ ε
  rw [←hs]
  exact hN m hm ell he

end LowEnergy.SourceClockPhiFixedSecondGreenTail
