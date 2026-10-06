import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarBalancedForce
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceGaugeRadialPair
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceEulerBracket

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarGaugeScale
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open SaturationMonoid.PhysicsCore StageNineHolonomicField StageNineP286GaugeConnectionVariationDensity
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussYukawaCoefficient GaussRadialDomain
open SourceCoframeVolumeCurrent SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceGaugeRadialCurrent SourceGaugeRadialPair SourceScalarBalancedForce
open scoped ContDiff InnerProductSpace BigOperators Topology
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

/-- The original weighted gauge Euler, as an inner derivation of the original core. -/
def deltaGauge : End →ₗ[ℂ] End where
  toFun A := gaugeEulerAction*A-A*gaugeEulerAction
  map_add' A B := by simp only [mul_add,add_mul]; abel
  map_smul' c A := by simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

def gaugeEulerLinear : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice :=
  (0 : SourceCoordinateSlice →L[ℝ] Coframe).prod
    ((0 : SourceCoordinateSlice →L[ℝ] scalarSlice).prod
      ((ContinuousLinearMap.snd ℝ scalarSlice coordinateSlice).comp
        (ContinuousLinearMap.snd ℝ Coframe (scalarSlice × coordinateSlice))))

private theorem gauge_derivative (z : SourceCoordinateSlice) :
    HasFDerivAt gaugeEuler gaugeEulerLinear z := gaugeEulerLinear.hasFDerivAt

/-- Differentiate the actual inverse split, including its scalar compensation. -/
theorem inverse_gauge_euler (v : Ambient) (hv : v.1=0) (z : physicalChart) :
    fderiv ℝ inverseL z.val (gaugeEuler z.val) v=
      -((inverseL z.val v).1,(inverseL z.val v).2.1,0) := by
  let u := inverseL z.val v
  have hs := congrArg Prod.fst (inverse_right z v)
  change action (vacuum+(z.val.2.1 : Scalar)) u.1+(u.2.1 : Scalar)=v.1 at hs
  rw [hv] at hs
  have he : variationL (gaugeEuler z.val) u=splitMap z.val (u.1,u.2.1,0) := by
    apply Prod.ext
    · change scalarP286ActionBilinear u.1 0=
        action (vacuum+(z.val.2.1 : Scalar)) u.1+(u.2.1 : Scalar)
      rw [map_zero,hs]
    · change nativeGauge u.1 (z.val.2.2 : Gauge)=nativeGauge u.1 (z.val.2.2 : Gauge)+0
      rw [add_zero]
  rw [inverse_derivative]
  change -inverseL z.val (variationL (gaugeEuler z.val) u)=_
  rw [he,inverse_left]

private theorem inverse_value_derivative (v : Ambient) (z : physicalChart) :
    HasFDerivAt (fun w => inverseL w v)
      ((fderiv ℝ inverseL z.val).flip v) z.val := by
  have hd := (((inverse_smooth z).differentiableAt (by simp)).hasFDerivAt).clm_apply
    (hasFDerivAt_const v z.val)
  simpa only [ContinuousLinearMap.comp_zero,zero_add] using! hd

private theorem direction_euler (v : Ambient) (hv : v.1=0) (z : physicalChart) :
    fderiv ℝ (direction v) z.val (gaugeEuler z.val)=
      (0,-(inverseL z.val v).2.1,0) := by
  have hd := (hasFDerivAt_const (0 : Coframe) z.val).prodMk
    ((inverse_value_derivative v z).snd)
  have h := congrArg (fun D : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice => D (gaugeEuler z.val)) hd.fderiv
  change fderiv ℝ (direction v) z.val (gaugeEuler z.val)=
    (0,(fderiv ℝ inverseL z.val (gaugeEuler z.val) v).2) at h
  simpa only [inverse_gauge_euler v hv z,Prod.neg_mk,neg_zero] using h

private theorem direction_bracket (v : Ambient) (hv : v.1=0) (z : physicalChart) :
    VectorField.lieBracket ℝ gaugeEuler (direction v) z.val= -direction v z.val := by
  rw [VectorField.lieBracket,direction_euler v hv z,(gauge_derivative z.val).fderiv]
  apply Prod.ext
  · change (0 : Coframe)-0= -0
    simp only [sub_self,neg_zero]
  · apply Prod.ext
    · change -(inverseL z.val v).2.1-0= -(inverseL z.val v).2.1
      exact sub_zero _
    · change 0-(inverseL z.val v).2.2= -(inverseL z.val v).2.2
      exact zero_sub _

private theorem euler_directional (v : Ambient) (hv : v.1=0) :
    deltaGauge (directional v)= -directional v := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change gaugeEulerAction (directional v f) z-directional v (gaugeEulerAction f) z= -directional v f z
  by_cases hz : z ∈ physicalChart
  · have hD : (directional v f : SourceCoordinateSlice → FockFiber)=
        (fun x => fderiv ℝ f x (direction v x)) := funext (directional_apply v f)
    have hE : (gaugeEulerAction f : SourceCoordinateSlice → FockFiber)=
        (fun x => fderiv ℝ f x (gaugeEuler x)) := funext (gauge_euler_apply f)
    rw [gauge_euler_apply,directional_apply,directional_apply,hD,hE]
    have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
      (V := gaugeEuler) (W := direction v) (x := z) f.contDiff.contDiffAt (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      ((direction_smooth v ⟨z,hz⟩).differentiableAt (by simp)) (gauge_derivative z).differentiableAt
    rw [direction_bracket v hv ⟨z,hz⟩,map_neg] at h
    exact h.symm
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz ((gaugeEulerAction (directional v f)).tsupport_subset h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz ((directional v (gaugeEulerAction f)).tsupport_subset h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz ((directional v f).tsupport_subset h))]
    simp only [sub_self,neg_zero]

private theorem connection_euler (v : Ambient) (hv : v.1=0) (z : physicalChart) :
    fderiv ℝ (connection v) z.val (gaugeEuler z.val)= -connection v z.val := by
  have hd := GaussNativeMatter.nativeFock.toContinuousLinearMap.hasFDerivAt.comp z.val
    ((inverse_value_derivative v z).fst)
  have h := congrArg (fun D : SourceCoordinateSlice →L[ℝ] (FockFiber →L[ℂ] FockFiber) => D (gaugeEuler z.val)) hd.fderiv
  change fderiv ℝ (connection v) z.val (gaugeEuler z.val)=
    GaussNativeMatter.nativeFock (fderiv ℝ inverseL z.val (gaugeEuler z.val) v).1 at h
  simpa only [inverse_gauge_euler v hv z,Prod.neg_mk,map_neg,connection] using! h

private theorem multiplier_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B : E → V →L[ℂ] V) (f : E → V) (z e : E)
    (hB : DifferentiableAt ℝ B z) (hf : DifferentiableAt ℝ f z)
    (h : fderiv ℝ B z e= -B z) :
    fderiv ℝ (fun x => B x (f x)) z e=B z (fderiv ℝ f z e)-B z (f z) := by
  have hr := (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp z hB.hasFDerivAt
  have hd := hr.clm_apply hf.hasFDerivAt
  change HasFDerivAt (fun x => B x (f x)) _ z at hd
  rw [hd.fderiv]
  change B z (fderiv ℝ f z e)+(fderiv ℝ B z e) (f z)=_
  rw [h,neg_apply]
  abel

private theorem euler_connection (v : Ambient) (hv : v.1=0) :
    deltaGauge (localMultiplier (connection v) (connection_smooth v))=
      -localMultiplier (connection v) (connection_smooth v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let A := localMultiplier (connection v) (connection_smooth v)
  change gaugeEulerAction (A f) z-A (gaugeEulerAction f) z= -A f z
  by_cases hz : z ∈ physicalChart
  · have hh : (A f : SourceCoordinateSlice → FockFiber)=fun x => connection v x (f x) := rfl
    rw [gauge_euler_apply,hh]
    change fderiv ℝ (fun x => connection v x (f x)) z (gaugeEuler z)-
      connection v z (gaugeEulerAction f z)= -connection v z (f z)
    rw [gauge_euler_apply]
    have h := multiplier_derivative (E := SourceCoordinateSlice) (V := FockFiber)
      (connection v) f z (gaugeEuler z)
      ((connection_smooth v ⟨z,hz⟩).differentiableAt (by simp))
      ((f.contDiff.differentiable (by simp)) z) (connection_euler v hv ⟨z,hz⟩)
    rw [h]
    abel
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz ((gaugeEulerAction (A f)).tsupport_subset h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz ((A (gaugeEulerAction f)).tsupport_subset h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz ((A f).tsupport_subset h))]
    simp only [sub_self,neg_zero]

/-- True gauge momentum weight, including the compensating native connection. -/
theorem original_gauge_momentum_scale (v : Ambient) (hv : v.1=0) :
    deltaGauge (covariantMomentum v)= -covariantMomentum v := by
  rw [covariantMomentum,map_smul,map_add,euler_directional v hv,euler_connection v hv]
  simp only [←neg_add,smul_neg]

private theorem euler_pair_shift (f g : QuantumTest) :
    sourcePair f (gaugeEulerAction g)=
      -sourcePair (gaugeEulerAction f) g-(36 : ℂ)*sourcePair f g := by
  rw [gauge_euler_pair,gauge_euler_transpose]
  simp only [sourcePair,map_sub,map_neg,map_smul,inner_sub_left,inner_neg_left,
    inner_smul_left,map_ofNat]

private theorem transpose_scale (A B : End) (pair : ∀ f g,sourcePair f (B g)=sourcePair (A f) g)
    (hA : deltaGauge A= -A) : deltaGauge B= -B := by
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have hp := congrArg (fun C : End => sourcePair (C f) g) hA
  change sourcePair (gaugeEulerAction (A f)-A (gaugeEulerAction f)) g=sourcePair (-A f) g at hp
  have hx := euler_pair_shift f (B g)
  rw [pair (gaugeEulerAction f) g,pair f g] at hx
  have hy := euler_pair_shift (A f) g
  rw [←pair f (gaugeEulerAction g)] at hy
  change sourcePair f (gaugeEulerAction (B g)-B (gaugeEulerAction g))=sourcePair f (-B g)
  simp only [sourcePair,map_sub,map_neg,inner_sub_left,inner_sub_right,inner_neg_left,
    inner_neg_right] at hp hx hy ⊢
  have hb := pair f g
  unfold sourcePair at hb
  linear_combination hp+hx-hy+hb

/-- The adjoint branch uses the original weighted transpose, including its 36 divergence. -/
theorem original_gauge_adjoint_scale (v : Ambient) (hv : v.1=0) :
    deltaGauge (GaussMomentumAdjoint.adjoint v)= -GaussMomentumAdjoint.adjoint v :=
  transpose_scale _ _ (GaussNativeForm.adjoint_pair v) (original_gauge_momentum_scale v hv)

private theorem invariant_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (f h : E → V) (γ : ℝ → E) (z e : E)
    (hg : HasDerivAt γ e 1) (hz : γ 1=z)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (law : ∀ r,h (γ r)=A (f (γ r))) :
    fderiv ℝ h z e=A (fderiv ℝ f z e) := by
  have hf0 := hf.hasFDerivAt.comp_hasDerivAt_of_eq 1 hg hz.symm
  have hh0 := hh.hasFDerivAt.comp_hasDerivAt_of_eq 1 hg hz.symm
  have hp := A.hasFDerivAt.comp_hasDerivAt 1 hf0
  have he : h ∘ γ=A ∘ (f ∘ γ) := funext law
  rw [he] at hh0
  exact hh0.unique hp

private theorem euler_multiplier (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (law : ∀ f z,A f z=B z (f z)) (invariant : ∀ r z,B (gaugeScale r z)=B z) :
    Commute gaugeEulerAction A := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change gaugeEulerAction (A f) z=A (gaugeEulerAction f) z
  rw [gauge_euler_apply,law,gauge_euler_apply]
  have h := invariant_derivative (E := SourceCoordinateSlice) (V := FockFiber)
    ((B z).restrictScalars ℝ) f (A f) (fun r => gaugeScale r z) z (gaugeEuler z)
    (gauge_scale_derivative z 1) (gauge_scale_one z)
    ((f.contDiff.differentiable (by simp)) z) (((A f).contDiff.differentiable (by simp)) z)
    (fun r => by rw [law,invariant]; rfl)
  simpa only [ContinuousLinearMap.coe_restrictScalars'] using! h

private theorem ad_product {R : Type*} [Ring R] (E A B : R) :
    E*(A*B)-(A*B)*E=(E*A-A*E)*B+A*(E*B-B*E) := by noncomm_ring

private theorem delta_product (A B : End) :
    deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B :=
  ad_product (R := End) _ _ _

private theorem delta_zero (A : End) (h : Commute gaugeEulerAction A) : deltaGauge A=0 :=
  sub_eq_zero.mpr h.eq

private theorem commute_product {R : Type*} [Ring R] (E A B : R)
    (hA : Commute E A) (hB : Commute E B) : Commute E (A*B) := hA.mul_right hB

private theorem commute_polynomial {R : Type*} [Ring R] (E A : R)
    (h : Commute E A) (m ell : ℕ) : Commute E ((1-A)^(m+1)-(1-A)^(ell+1)) :=
  ((Commute.one_right E).sub_right h).pow_right (m+1) |>.sub_right
    (((Commute.one_right E).sub_right h).pow_right (ell+1))

private theorem constant_invariant (sharp : Bool) (v : Scalar) :
    Commute gaugeEulerAction (constantAction sharp v) :=
  euler_multiplier _ (fun _ => branchMap sharp v) (fun _ _ => rfl) (fun _ _ => rfl)

private theorem scalar_invariant (sharp : Bool) : Commute gaugeEulerAction (scalarAction sharp) :=
  euler_multiplier _ (fun z => branchMap sharp (z.2.1 : Scalar)) (fun _ _ => rfl) (fun _ _ => rfl)

private theorem full_invariant (sharp : Bool) : Commute gaugeEulerAction (fullAction sharp) := by
  rw [full_scalar_split]
  exact (constant_invariant sharp vacuum).add_right (scalar_invariant sharp)

private theorem inverse_invariant : Commute gaugeEulerAction inverseAction :=
  euler_multiplier _ (fun z => (reciprocal z : ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _ => rfl) (fun _ _ => rfl)

private theorem theta_invariant (m ell : ℕ) : Commute gaugeEulerAction (thetaAction m ell) :=
  commute_polynomial (R := End) _ _ inverse_invariant m ell

/-- Both branches of the literal insertion and its independent cutoff have gauge degree zero. -/
theorem original_insertion_gauge_scale (sharp : Bool) (m ell : ℕ) :
    deltaGauge (fullInsertion sharp m ell)=0 :=
  delta_zero _ (commute_product (R := End) _ _ _ (full_invariant sharp) (theta_invariant m ell))

private theorem contact_invariant (v : Ambient) : Commute gaugeEulerAction (matterContact v) :=
  euler_multiplier _ (contactFiber v) (fun _ _ => rfl) (fun _ _ => rfl)

private theorem weight_invariant (i j : Fin 3) :
    Commute gaugeEulerAction (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) :=
  euler_multiplier _ (fun z => (gaugeWeight z i j : ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _ => rfl) (fun _ _ => rfl)

private theorem delta_bracket (A B : End) :
    deltaGauge (bracket A B)=bracket (deltaGauge A) B+bracket A (deltaGauge B) := by
  change deltaGauge (A*B-B*A)=_
  rw [map_sub,delta_product,delta_product]
  unfold bracket
  abel

private theorem contact_bracket_invariant (v : Ambient) (sharp : Bool) (m ell : ℕ) :
    deltaGauge (bracket (matterContact v) (fullInsertion sharp m ell))=0 := by
  rw [delta_bracket,delta_zero _ (contact_invariant v),original_insertion_gauge_scale]
  simp only [bracket,zero_mul,mul_zero,sub_self,add_zero]

/-- The complete surviving electric/matter current has degree minus one, with both momentum branches. -/
theorem mixed_current_gauge_scale (sharp : Bool) (m ell : ℕ) :
    deltaGauge (gaugeMatterCurrent sharp m ell)= -gaugeMatterCurrent sharp m ell := by
  have hP (i : Fin 3) (a : LieIndex) := original_gauge_momentum_scale (gaugeDirection i a) rfl
  have hA (i : Fin 3) (a : LieIndex) := original_gauge_adjoint_scale (gaugeDirection i a) rfl
  simp only [gaugeMatterCurrent,map_smul,map_sum,map_add,delta_product,
    hA,hP,
    delta_zero _ (weight_invariant _ _),contact_bracket_invariant,
    zero_mul,mul_zero,add_zero,zero_add,neg_mul,mul_neg,←neg_add,
    Finset.sum_neg_distrib,smul_neg]

private def scalarEulerLinear : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice :=
  (0 : SourceCoordinateSlice →L[ℝ] Coframe).prod
    (((ContinuousLinearMap.fst ℝ scalarSlice coordinateSlice).comp
      (ContinuousLinearMap.snd ℝ Coframe (scalarSlice × coordinateSlice))).prod
        (0 : SourceCoordinateSlice →L[ℝ] coordinateSlice))

private theorem scalar_derivative (z : SourceCoordinateSlice) :
    HasFDerivAt SourceScalarRadialContact.scalarEuler scalarEulerLinear z := scalarEulerLinear.hasFDerivAt

private theorem euler_scalar : deltaGauge SourceScalarRadialContact.scalarEulerAction=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change gaugeEulerAction (SourceScalarRadialContact.scalarEulerAction f) z-
    SourceScalarRadialContact.scalarEulerAction (gaugeEulerAction f) z=0
  have hS : (SourceScalarRadialContact.scalarEulerAction f : SourceCoordinateSlice → FockFiber)=
      fun x => fderiv ℝ f x (SourceScalarRadialContact.scalarEuler x) :=
    funext (SourceScalarRadialContact.scalar_euler_apply f)
  have hE : (gaugeEulerAction f : SourceCoordinateSlice → FockFiber)=
      fun x => fderiv ℝ f x (gaugeEuler x) := funext (gauge_euler_apply f)
  rw [gauge_euler_apply,SourceScalarRadialContact.scalar_euler_apply,hS,hE]
  have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
    (V := gaugeEuler) (W := SourceScalarRadialContact.scalarEuler) (x := z) f.contDiff.contDiffAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    (scalar_derivative z).differentiableAt (gauge_derivative z).differentiableAt
  have hb : VectorField.lieBracket ℝ gaugeEuler SourceScalarRadialContact.scalarEuler z=0 := by
    rw [VectorField.lieBracket,(scalar_derivative z).fderiv,(gauge_derivative z).fderiv]
    change (0 : SourceCoordinateSlice)-0=0
    exact sub_self _
  rw [hb,map_zero] at h
  exact h.symm

private theorem scalar_insertion_invariant (sharp : Bool) (m ell : ℕ) :
    deltaGauge (bracket SourceScalarRadialContact.scalarEulerAction (fullInsertion sharp m ell))=0 := by
  rw [delta_bracket,euler_scalar,original_insertion_gauge_scale]
  simp only [bracket,zero_mul,mul_zero,sub_self,add_zero]

/-- Gauge Euler differentiates the already paid coframe cubic on the full original double commutator. -/
theorem original_cubic_gauge_current (sharp : Bool) (m ell : ℕ) :
    deltaGauge (cubic (bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell))))=
      (-48 : ℂ) • gaugeMatterCurrent sharp m ell := by
  rw [original_double_oscillator_current,map_add,map_smul,scalar_insertion_invariant,
    SourceScalarGaugeForce.original_electric_matter_current,original_mixed_current,
    map_smul,mixed_current_gauge_scale,smul_zero,zero_add,smul_neg,neg_smul]

/-- The ordered source polynomial (delta_g + 1) Q(delta_c), with no compression substituted for either derivation. -/
theorem original_gauge_coframe_return (sharp : Bool) (m ell : ℕ) :
    deltaGauge (cubic (bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell))))+
      cubic (bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell)))=
      (-96*(sourceTime 0 : ℂ)^2) •
        bracket (R := End) SourceScalarRadialContact.scalarEulerAction (fullInsertion sharp m ell) := by
  rw [original_cubic_gauge_current,original_double_oscillator_current,
    SourceScalarGaugeForce.original_electric_matter_current,original_mixed_current]
  module

/-- This retains the whole coframe remainder and its actual gauge derivative. -/
def scaleGaugeRemainder (sharp : Bool) (m ell : ℕ) : End :=
  scaleDoubleRemainder sharp m ell+
    deltaGauge (cubic (bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell))))

/-- The original coframe remainder, its gauge derivative, and the full double-H gauge derivative are all explicit. -/
theorem original_gauge_remainder (sharp : Bool) (m ell : ℕ) :
    scaleGaugeRemainder sharp m ell=scaleDoubleRemainder sharp m ell+
      deltaGauge (scaleDoubleRemainder sharp m ell)+(48 : ℂ) •
        deltaGauge (bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell))) := by
  have hc : cubic (bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell)))=
      scaleDoubleRemainder sharp m ell+(48 : ℂ) •
        bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell)) := by
    simp only [cubic,scaleDoubleRemainder,LinearMap.add_apply,LinearMap.comp_apply,
      LinearMap.smul_apply,LinearMap.id_apply]
  rw [scaleGaugeRemainder,hc,map_add,map_smul,add_assoc]

/-- The full oscillator force after the source gauge current is absorbed into its genuine source jets. -/
def gaugeScaleForce (sharp : Bool) (m ell : ℕ) : End :=
  -(2*(sourceTime 0 : ℂ)^2) • (fullAction sharp*cutoffEuler m ell)+
    (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*thetaAction m ell)-
    (1/48 : ℂ) • scaleGaugeRemainder sharp m ell

/-- The original full oscillator force is exactly the generated gauge/coframe force. -/
theorem original_force_return (sharp : Bool) (m ell : ℕ) :
    oscillatorForce sharp m ell=gaugeScaleForce sharp m ell := by
  simp only [oscillatorForce,gaugeScaleForce,scaleGaugeRemainder,original_cubic_gauge_current,
    SourceScalarGaugeForce.original_electric_matter_current,original_mixed_current]
  module

/-- The same compressed force keeps its three genuine projection defects and original Hardy solver. -/
theorem actual_balanced_gauge_return (sharp : Bool) (m ell : ℕ) (F : GaussUnitaryHistory.Index)
    (g : diagonal.domain) :
    SourceScalarForceBudget.balancedForce sharp m ell F g=
      sourceRead F g (gaugeScaleForce sharp m ell)-SourceScalarDoubleCurrent.doubleProjectionFlux sharp m ell F g-
      (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F := by
  have h := actual_balanced_force_current sharp m ell F g
  have hf : gaugeMatterCurrent sharp m ell-
      (2*(sourceTime 0 : ℂ)^2) • (fullAction sharp*cutoffEuler m ell)+
      (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*thetaAction m ell)-
      (1/48 : ℂ) • scaleDoubleRemainder sharp m ell=gaugeScaleForce sharp m ell := by
    have hh := original_force_return sharp m ell
    simpa only [oscillatorForce,SourceScalarGaugeForce.original_electric_matter_current,original_mixed_current] using! hh
  exact h.trans (congrArg (fun A : End => sourceRead F g A-
    SourceScalarDoubleCurrent.doubleProjectionFlux sharp m ell F g-
    (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F) hf)

end LowEnergy.SourceScalarGaugeScale
