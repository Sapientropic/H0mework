import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceNativeScaleForce
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCutoffDilationWard
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCoframeCompressionCovariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceMixedNativeReturn
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussCoframeForm GaussDiagonalHistory
open GaussYukawaCoefficient GaussRadialDomain GaussLiveMomentum GaussQuantumMultiplier
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolumeCurrent SourceCoframeDilation SourceEulerCore
open SourceDilationRemainder SourceHamiltonianScaleJet SourceDilationAlgebra SourceCutoffDilationWard
open SourceClosedCostNativeProbe SourceJointScaleBudget SourceEscapeCurrent
open FullYSourceResolventGraphSplice GaussUnitaryHistory SourceRelativePowerTail
open scoped ContDiff InnerProductSpace RealInnerProductSpace

/-- Both coefficient branches are the original real-linear maps, including the independent dual. -/
def branchMap (sharp : Bool) : Scalar →L[ℝ] FockFiber →L[ℂ] FockFiber :=
  if sharp then GaussFullHamiltonian.adjointMap else sourceMap

def constantAction (sharp : Bool) (v : Scalar) : CoreEnd :=
  localMultiplier (fun _ => branchMap sharp v) (fun _ => contDiffAt_const)

def scalarAction (sharp : Bool) : CoreEnd :=
  localMultiplier (fun z => branchMap sharp (z.2.1 : Scalar))
    (fun _ => ((branchMap sharp).contDiff.comp GaussRadialMomentum.scalarCoordinate.contDiff).contDiffAt)

def fullAction (sharp : Bool) : CoreEnd :=
  if sharp then GaussFullHamiltonian.adjointAction else GaussYukawaOperator.originalAction

def thetaAction (m ell : ℕ) : CoreEnd :=
  (1-inverseAction)^(m+1)-(1-inverseAction)^(ell+1)

def primitive (sharp : Bool) (m ell : ℕ) : CoreEnd :=
  ∑ a : ScalarIndex, constantAction sharp (scalarBasis a)*weightedMomentum (scalarDirection a)*thetaAction m ell

private theorem constant_pair_native (v : Scalar) (f g : QuantumTest) :
    sourcePair f (constantAction true v g)=sourcePair (constantAction false v f) g := by
  rw [sourcePair_integral,sourcePair_integral]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z) (f z))
    ((sourceMap v).adjoint (g z))=
    inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z)
      (sourceMap v (f z))) (g z)
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hc : Commute (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z))
      (sourceMap v) := by
    rw [source_map_return]
    exact weight_commute _ _
  exact congrArg (fun y : FockFiber => inner ℂ y (g z))
    (congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z)) hc.eq).symm

theorem constant_pair (sharp : Bool) (v : Scalar) (f g : QuantumTest) :
    sourcePair f (constantAction sharp v g)=sourcePair (constantAction (!sharp) v f) g := by
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (constant_pair_native v g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using h.symm
  · exact constant_pair_native v f g

private theorem affine_commute (A : CoreEnd) (hE : Commute eulerAction A)
    (hN : Commute number A) : Commute dilation A := by
  apply sub_eq_zero.mp
  have he : eulerAction*A-A*eulerAction=(0 : ℂ) • A := by rw [hE.eq,sub_self,zero_smul]
  rw [dilation_operator]
  simpa only [mul_zero,zero_smul,Module.End.one_eq_id] using! affine_dilation _ _ _ 0 he hN

theorem constant_dilation (sharp : Bool) (v : Scalar) : Commute dilation (constantAction sharp v) := by
  have hn : Commute dilation (constantAction false v) := by
    apply affine_commute
    · exact euler_invariant_multiplier _ _ (fun _ _ => rfl)
    · apply number_multiplier
      intro z
      change Commute fiberNumber (sourceMap v)
      rw [source_map_return]
      exact number_commute _
  cases sharp
  · exact hn
  · apply LinearMap.ext
    intro g
    apply SourceCoframeVolume.pair_ext
    intro f
    change sourcePair f (dilation (constantAction true v g))=
      sourcePair f (constantAction true v (dilation g))
    rw [dilation_pair,constant_pair_native,constant_pair_native]
    have h := LinearMap.congr_fun hn.eq f
    change dilation (constantAction false v f)=constantAction false v (dilation f) at h
    rw [←h,←dilation_pair]

private theorem scale_zero {A : CoreEnd} (h : Commute dilation A) : scaleDerivative A=0 := by
  change (3*Complex.I/2) • (dilation*A-A*dilation)=0
  rw [h.eq,sub_self,smul_zero]

private theorem scale_product (A B : CoreEnd) :
    scaleDerivative (A*B)=scaleDerivative A*B+A*scaleDerivative B := by
  change (3*Complex.I/2) • (dilation*(A*B)-(A*B)*dilation)=
    ((3*Complex.I/2) • (dilation*A-A*dilation))*B+
      A*((3*Complex.I/2) • (dilation*B-B*dilation))
  have h : dilation*(A*B)-(A*B)*dilation=(dilation*A-A*dilation)*B+A*(dilation*B-B*dilation) := by
    noncomm_ring
  rw [h,smul_add]
  simp only [sub_mul,mul_sub,smul_sub,smul_mul_assoc,mul_smul_comm]

theorem theta_dilation (m ell : ℕ) : Commute dilation (thetaAction m ell) := by
  have h : Commute dilation (1-inverseAction) := (Commute.one_right _).sub_right inverse_dilation
  exact (h.pow_right (m+1)).sub_right (h.pow_right (ell+1))

theorem primitive_scale (sharp : Bool) (m ell : ℕ) :
    scaleDerivative (primitive sharp m ell)=(-3 : ℂ) • primitive sharp m ell := by
  simp only [primitive,map_sum,scale_product,scale_zero (constant_dilation sharp _),
    scale_zero (theta_dilation m ell),weighted_momentum_scale,zero_mul,mul_zero,zero_add,add_zero,
    mul_smul_comm,smul_mul_assoc,Finset.smul_sum]

private theorem constant_local (sharp : Bool) (v : Scalar) : Commute localAction (constantAction sharp v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (branchMap sharp v) (localPotential z : ℂ) (f z)).symm

private theorem theta_local (m ell : ℕ) : Commute localAction (thetaAction m ell) := by
  have hi : Commute localAction inverseAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (localPotential z : ℂ) (reciprocal z : ℂ) (f z)
  exact (((Commute.one_right _).sub_right hi).pow_right (m+1)).sub_right
    (((Commute.one_right _).sub_right hi).pow_right (ell+1))

private theorem force_product (L A T B : CoreEnd) (hA : Commute L A) (hB : Commute L B) :
    force L (A*T*B)=A*force L T*B := by
  change Complex.I • (L*(A*T*B)-(A*T*B)*L)=_
  have h : L*(A*T*B)-(A*T*B)*L=A*(L*T-T*L)*B := by
    calc
      _ = (L*A)*T*B-A*T*(B*L) := by noncomm_ring
      _ = _ := by rw [hA.eq,←hB.eq]; noncomm_ring
  rw [h]
  simp only [force,mul_smul_comm,smul_mul_assoc]

private theorem shifted_force (A T : CoreEnd) (hT : scaleDerivative T=(-3 : ℂ) • T) :
    shiftedDerivative (force A T)=force (scaleDerivative A) T := by
  change scaleDerivative (force A T)+(3 : ℂ) • force A T=_
  simp only [force,map_smul,map_sub,scale_product,hT,smul_mul_assoc,mul_smul_comm]
  module

private theorem full_shifted_force (T : CoreEnd) (hT : scaleDerivative T=(-3 : ℂ) • T) :
    shiftedProjected (force diagonalAction T)=(48 : ℂ) • force localAction T := by
  unfold shiftedProjected
  simp only [shifted_force _ _ hT]
  have hh := congrArg (fun A => force A T) source_local_from_scale_jet
  simp only [force,add_mul,mul_add,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm] at hh ⊢
  convert! hh using 1 <;> module

private theorem scalar_sum (sharp : Bool) :
    (∑ a : ScalarIndex,constantAction sharp (scalarBasis a)*
      SourceClosedCostNativeProbe.coordinateAction (scalarDirection a))=scalarAction sharp := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.sum_apply,sum_apply]
  change (∑ a : ScalarIndex,branchMap sharp (scalarBasis a)
    ((inner ℝ (z.2.1 : Scalar) (scalarBasis a) : ℂ) • f z))=
      branchMap sharp (z.2.1 : Scalar) (f z)
  have he : ∑ a : ScalarIndex,(inner ℝ (z.2.1 : Scalar) (scalarBasis a)) • scalarBasis a=
      (z.2.1 : Scalar) := by
    simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm] using scalarBasis.sum_repr (z.2.1 : Scalar)
  conv_rhs => rw [←he,map_sum,sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul,map_smul]
  rfl

/-- The actual Yukawa sum and both coefficient branches return from the full signed H0. -/
theorem source_mixed_force (sharp : Bool) (m ell : ℕ) :
    shiftedProjected (force diagonalAction (primitive sharp m ell))=
      (-96*(sourceTime 0 : ℂ)^2) • (scalarAction sharp*thetaAction m ell) := by
  rw [full_shifted_force _ (primitive_scale sharp m ell)]
  have hsum : force localAction (primitive sharp m ell)=
      ∑ a : ScalarIndex,constantAction sharp (scalarBasis a)*
        force localAction (weightedMomentum (scalarDirection a))*thetaAction m ell := by
    unfold primitive force
    simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact force_product _ _ _ _ (constant_local sharp _) (theta_local m ell)
  rw [hsum,Finset.smul_sum]
  have he (a : ScalarIndex) : (48 : ℂ) • force localAction (weightedMomentum (scalarDirection a))=
      (-96*(sourceTime 0 : ℂ)^2) • SourceClosedCostNativeProbe.coordinateAction (scalarDirection a) := by
    rw [←full_shifted_force _ (weighted_momentum_scale _)]
    exact shifted_force_coordinate _
  calc
    _ = ∑ a : ScalarIndex,(-96*(sourceTime 0 : ℂ)^2) •
        (constantAction sharp (scalarBasis a)*SourceClosedCostNativeProbe.coordinateAction (scalarDirection a)*
          thetaAction m ell) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [←smul_mul_assoc,←mul_smul_comm,he,mul_smul_comm,smul_mul_assoc]
    _ = _ := by rw [←Finset.smul_sum,←Finset.sum_mul,scalar_sum]

private theorem complement_core (f : QuantumTest) :
    sourceComplement (embed f)=embed ((1-inverseAction) f) := by
  change embed f-inverseRadius (embed f)=_
  rw [inverse_core,←map_sub]
  rfl

private theorem power_core (n : ℕ) (f : QuantumTest) :
    (sourceComplement^n) (embed f)=embed (((1-inverseAction)^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change sourceComplement ((sourceComplement^n) (embed f))=_
    rw [ih,complement_core]
    rfl

theorem theta_core (m ell : ℕ) (f : QuantumTest) :
    relativeTail m ell (embed f)=embed (thetaAction m ell f) := by
  change (sourceComplement^(m+1)) (embed f)-(sourceComplement^(ell+1)) (embed f)=_
  rw [power_core,power_core,←map_sub]
  rfl

private theorem inverse_full (sharp : Bool) (f : QuantumTest) :
    inverseAction (fullAction sharp f)=
      (if sharp then sharpVertexAction else GaussYukawaCoefficient.action) f := by
  cases sharp
  · apply DFunLike.ext
    intro z
    change (reciprocal z : ℂ) • sourceMap (scalarField z) (f z)=normalized z (f z)
    rw [normalized,normalizedScalar,map_smul]
    rfl
  · apply DFunLike.ext
    intro z
    change (reciprocal z : ℂ) • GaussFullHamiltonian.adjointMap (scalarField z) (f z)=
      GaussFullHamiltonian.adjointMap (scalarField z) ((reciprocal z : ℂ) • f z)
    exact (map_smul _ _ _).symm

private theorem inverse_action_injective : Function.Injective inverseAction := by
  intro f g h
  apply DFunLike.ext
  intro z
  have hz := congrArg (fun a : QuantumTest => a z) h
  change (reciprocal z : ℂ) • f z=(reciprocal z : ℂ) • g z at hz
  exact (smul_right_injective FockFiber (by exact_mod_cast (inv_pos.mpr (radius_pos z)).ne' : (reciprocal z : ℂ)≠0)) hz

/-- The literal finite cutoff is read on the original core; no completed inverse-radius is used. -/
theorem literal_full_return (sharp : Bool) (m ell : ℕ) :
    literalIncrementAction sharp m ell=fullAction sharp*thetaAction m ell := by
  apply LinearMap.ext
  intro f
  apply inverse_action_injective
  apply embed_injective
  rw [←inverse_core,←literal_increment_core]
  have h := congrArg (fun A : H →L[ℂ] H => A (embed f)) (SourceCornerForcing.actual_increment_factor sharp m ell)
  change inverseRadius (SourceEscapeSeedTail.actualIncrement sharp m ell (embed f))=
    SourceCornerForcing.sourceVertex sharp (relativeTail m ell (embed f)) at h
  rw [h,theta_core]
  change _=embed (inverseAction (fullAction sharp (thetaAction m ell f)))
  rw [inverse_full]
  cases sharp
  · exact GaussYukawaOperator.bounded_core _
  · exact sharp_vertex_core _

theorem full_scalar_split (sharp : Bool) :
    fullAction sharp=constantAction sharp vacuum+scalarAction sharp := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hv : fullAction sharp f z=branchMap sharp (vacuum+(z.2.1 : Scalar)) (f z) := by
    cases sharp <;> rfl
  rw [hv]
  change branchMap sharp (vacuum+(z.2.1 : Scalar)) (f z)=
    branchMap sharp vacuum (f z)+branchMap sharp (z.2.1 : Scalar) (f z)
  rw [map_add,add_apply]

/-- Vacuum remains a separate bounded coefficient; the complete linear insertion is a source force. -/
theorem literal_mixed_return (sharp : Bool) (m ell : ℕ) :
    (-96*(sourceTime 0 : ℂ)^2) • literalIncrementAction sharp m ell=
      (-96*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*thetaAction m ell)+
        shiftedProjected (force diagonalAction (primitive sharp m ell)) := by
  rw [literal_full_return,full_scalar_split,add_mul,smul_add,source_mixed_force]



private def nativeConstant (v : Scalar) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (fun _ => sourceMap v) (fun _ => contDiffAt_const)
    (fun _ w => by rw [source_map_return]; exact weight_commute w _)
    ‖sourceMap v‖ (norm_nonneg _) (fun _ f => (sourceMap v).le_opNorm f)

def constantBounded (sharp : Bool) (v : Scalar) : H →L[ℂ] H :=
  if sharp then (nativeConstant v).adjoint else nativeConstant v

theorem constant_bounded_core (sharp : Bool) (v : Scalar) (f : QuantumTest) :
    constantBounded sharp v (embed f)=embed (constantAction sharp v f) := by
  have hn (a : QuantumTest) : nativeConstant v (embed a)=embed (constantAction false v a) :=
    GaussBoundedMultiplier.extension_core _ _ _ _ _ _ a
  cases sharp
  · exact hn f
  · apply ext_inner_left ℂ
    intro y
    refine GaussBoundedMultiplier.core_dense.induction_on y
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    obtain ⟨g,rfl⟩ := coreEquiv.surjective a
    change inner ℂ (embed g) ((nativeConstant v).adjoint (embed f))=
      sourcePair g (constantAction true v f)
    rw [ContinuousLinearMap.adjoint_inner_right,hn,constant_pair_native]
    rfl

theorem vacuum_tail_bound (sharp : Bool) (m ell : ℕ) (x : H) :
    ‖constantBounded sharp vacuum (relativeTail m ell x)‖≤
      ‖sourceMap vacuum‖*‖relativeTail m ell x‖ := by
  have hn : ‖constantBounded sharp vacuum‖≤‖sourceMap vacuum‖ := by
    have hb : ‖nativeConstant vacuum‖≤‖sourceMap vacuum‖ :=
      GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
    cases sharp
    · exact hb
    · simpa only [constantBounded,if_true,LinearIsometryEquiv.norm_map] using hb
  exact ((constantBounded sharp vacuum).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

/-- Finite read on the actual R_F input span includes the zero-action escape channel. -/
def coreRead (F : Index) (g : diagonal.domain) (A : CoreEnd) : H →L[ℂ] H :=
  ((embed.comp (A.comp (coreEquiv.symm.toLinearMap.comp
    (Submodule.inclusion (input_span_core F g))))).toContinuousLinearMap).comp
      (inputSpan F g).orthogonalProjectionOnto

private theorem core_read_add (F : Index) (g : diagonal.domain) (A B : CoreEnd) :
    coreRead F g (A+B)=coreRead F g A+coreRead F g B := by
  apply ContinuousLinearMap.ext
  intro x
  change embed ((A+B) _)=embed (A _)+embed (B _)
  exact map_add embed _ _

private theorem core_read_smul (F : Index) (g : diagonal.domain) (c : ℂ) (A : CoreEnd) :
    coreRead F g (c • A)=c • coreRead F g A := by
  apply ContinuousLinearMap.ext
  intro x
  exact map_smul embed c _

def sourceRead (F : Index) (g : diagonal.domain) : CoreEnd →ₗ[ℂ] H →L[ℂ] H where
  toFun := coreRead F g
  map_add' := core_read_add F g
  map_smul' := core_read_smul F g

theorem source_read_resolvent (F : Index) (g : diagonal.domain) (A : CoreEnd)
    (z : ℂ) (hz : z.im≠0) :
    sourceRead F g A (finiteResolvent F z (g : H))=
      embed (A (coreEquiv.symm (sourceCore F z hz g))) := by
  have hp := (inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨finiteResolvent F z (g : H),resolvent_input_span F z hz g⟩
  change embed (A (coreEquiv.symm
    (Submodule.inclusion (input_span_core F g)
      ((inputSpan F g).orthogonalProjectionOnto (finiteResolvent F z (g : H))))))=_
  rw [hp]
  rfl

def jet (n : ℕ) (A : CoreEnd) : CoreEnd := scaleDerivative^[n] A

private theorem shifted_expansion (A : CoreEnd) :
    shiftedProjected A=jet 3 A+(12 : ℂ) • jet 2 A+(44 : ℂ) • jet 1 A+(48 : ℂ) • jet 0 A := by
  simp only [jet,Function.iterate_succ_apply,Function.iterate_zero_apply,
    shiftedProjected,shiftedDerivative,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,
    map_add,map_smul]
  module

def rawJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (j : ℕ) : H →L[ℂ] H :=
  sourceRead F g (jet j (force diagonalAction (primitive sharp m ell)))

private theorem nat_smul_operator (n : ℕ) (A : H →L[ℂ] H) :
    (n : ℂ) • A=(n : H →L[ℂ] H)*A := by
  exact (Nat.cast_smul_eq_nsmul ℂ n A).trans (nsmul_eq_mul n A)

def rawPolynomial (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) : H →L[ℂ] H :=
  rawJet sharp m ell F g 3+12*rawJet sharp m ell F g 2+
    44*rawJet sharp m ell F g 1+48*rawJet sharp m ell F g 0

private theorem raw_polynomial_read (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    rawPolynomial sharp m ell F g=
      sourceRead F g (shiftedProjected (force diagonalAction (primitive sharp m ell))) := by
  rw [shifted_expansion]
  simp only [map_add,map_smul]
  change rawPolynomial sharp m ell F g=rawJet sharp m ell F g 3+
    (12 : ℂ) • rawJet sharp m ell F g 2+(44 : ℂ) • rawJet sharp m ell F g 1+
      (48 : ℂ) • rawJet sharp m ell F g 0
  have h12 : (12 : ℂ) • rawJet sharp m ell F g 2=12*rawJet sharp m ell F g 2 := by
    simpa only [Nat.cast_ofNat] using! nat_smul_operator 12 (rawJet sharp m ell F g 2)
  have h44 : (44 : ℂ) • rawJet sharp m ell F g 1=44*rawJet sharp m ell F g 1 := by
    simpa only [Nat.cast_ofNat] using! nat_smul_operator 44 (rawJet sharp m ell F g 1)
  have h48 : (48 : ℂ) • rawJet sharp m ell F g 0=48*rawJet sharp m ell F g 0 := by
    simpa only [Nat.cast_ofNat] using! nat_smul_operator 48 (rawJet sharp m ell F g 0)
  rw [h12,h44,h48]
  rfl

private theorem core_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)

/-- This is a direct all-F return of the original literal insertion, with vacuum and all escape retained. -/
theorem actual_mixed_insertion (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    (-96*(sourceTime 0 : ℂ)^2) •
        SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H))=
      (-96*(sourceTime 0 : ℂ)^2) •
        constantBounded sharp vacuum (relativeTail m ell (finiteResolvent F z (g : H)))+
      rawPolynomial sharp m ell F g (finiteResolvent F z (g : H)) := by
  let q := coreEquiv.symm (sourceCore F z hz g)
  have hq : embed q=finiteResolvent F z (g : H) := core_embed _
  rw [raw_polynomial_read,source_read_resolvent,←hq,literal_increment_core,
    theta_core,constant_bounded_core]
  have h := congrArg embed (LinearMap.congr_fun (literal_mixed_return sharp m ell) q)
  simpa only [LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,map_add,map_smul] using! h



end LowEnergy.SourceMixedNativeReturn
