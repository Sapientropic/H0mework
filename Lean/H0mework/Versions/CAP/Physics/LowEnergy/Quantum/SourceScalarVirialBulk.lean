import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceScalarVirialIMS
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceScalarGaugeScale
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceScalarMixedEndpointBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarVirialBulk
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeEnergy GaussNativeForm GaussNativeMatter GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceDilationRemainder
open SourceScalarFlatJoint SourceScalarRadialContact SourceScalarVirialCurrent
open SourceGaugeRadialCurrent SourceGaugeRadialPair SourceScalarGaugeScale
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionVariationDensity
open scoped ContDiff InnerProductSpace
abbrev End := SourceScalarGaugeScale.End

def vacuumSlice : scalarSlice := ⟨vacuum,vacuum_mem_scalarSlice⟩
def phiEuler (z : SourceCoordinateSlice) : SourceCoordinateSlice := (0,vacuumSlice+z.2.1,0)
def phiEulerAction : End := scalarEulerAction+GaussCoframeCore.derivative (scalarAxis vacuumSlice)

private def phiLinear : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice :=
  (0 : SourceCoordinateSlice →L[ℝ] Coframe).prod
    (((ContinuousLinearMap.fst ℝ scalarSlice coordinateSlice).comp
      (ContinuousLinearMap.snd ℝ Coframe (scalarSlice × coordinateSlice))).prod
      (0 : SourceCoordinateSlice →L[ℝ] coordinateSlice))

private theorem phi_derivative (z : SourceCoordinateSlice) : HasFDerivAt phiEuler phiLinear z := by
  have h := phiLinear.hasFDerivAt (x := z) |>.const_add (scalarAxis vacuumSlice)
  convert! h using 1
  funext x
  simp [phiEuler,scalarAxis,phiLinear]

/-- The shift is the original vacuum in its actual scalar slice, not a changed scalar field. -/
theorem phi_euler_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    phiEulerAction f z=fderiv ℝ f z (phiEuler z) := by
  change scalarEulerAction f z+GaussCoframeCore.derivative (scalarAxis vacuumSlice) f z=_
  rw [scalar_euler_apply,GaussCoframeCore.derivative_apply,←map_add]
  congr 1
  apply Prod.ext
  · change (0 : Coframe)+0=0
    exact zero_add _
  · apply Prod.ext
    · exact add_comm _ _
    · change (0 : coordinateSlice)+0=0
      exact zero_add _

/-- Scalar input: the actual inverse has degree (-1,0,-1) under dilation of vacuum+q. -/
theorem original_inverse_phi_scalar (v : Ambient) (hv : v.2=0) (z : physicalChart) :
    fderiv ℝ inverseL z.val (phiEuler z.val) v=
      -((inverseL z.val v).1,0,(inverseL z.val v).2.2) := by
  let u := inverseL z.val v
  have hg := congrArg Prod.snd (inverse_right z v)
  change nativeGauge u.1 (z.val.2.2 : Gauge)+(u.2.2 : Gauge)=v.2 at hg
  rw [hv] at hg
  have he : variationL (phiEuler z.val) u=splitMap z.val (u.1,0,u.2.2) := by
    apply Prod.ext
    · change scalarP286ActionBilinear u.1 (vacuum+(z.val.2.1 : Scalar))=
        action (vacuum+(z.val.2.1 : Scalar)) u.1+0
      rw [add_zero]
      rfl
    · change nativeGauge u.1 0=nativeGauge u.1 (z.val.2.2 : Gauge)+(u.2.2 : Gauge)
      rw [map_zero,hg]
  rw [inverse_derivative]
  change -inverseL z.val (variationL (phiEuler z.val) u)=_
  rw [he,inverse_left]

/-- Gauge input: the true inverse scalar compensator has degree one; the orbit/gauge pieces have degree zero. -/
theorem original_inverse_phi_gauge (v : Ambient) (hv : v.1=0) (z : physicalChart) :
    fderiv ℝ inverseL z.val (phiEuler z.val) v=(0,(inverseL z.val v).2.1,0) := by
  let u := inverseL z.val v
  have hs := congrArg Prod.fst (inverse_right z v)
  change action (vacuum+(z.val.2.1 : Scalar)) u.1+(u.2.1 : Scalar)=v.1 at hs
  rw [hv] at hs
  have he : variationL (phiEuler z.val) u=splitMap z.val (0,-u.2.1,0) := by
    apply Prod.ext
    · change action (vacuum+(z.val.2.1 : Scalar)) u.1=action (vacuum+(z.val.2.1 : Scalar)) 0+↑(-u.2.1)
      rw [map_zero,zero_add]
      exact eq_neg_of_add_eq_zero_left hs
    · change nativeGauge u.1 0=nativeGauge 0 (z.val.2.2 : Gauge)+0
      simp only [map_zero,LinearMap.zero_apply,zero_add]
  rw [inverse_derivative]
  change -inverseL z.val (variationL (phiEuler z.val) u)=_
  rw [he,inverse_left]
  simp only [Prod.neg_mk,neg_zero,neg_neg]
  rfl

/-- The same scalar momentum is gauge-Euler invariant; no orthogonal row is discarded. -/
theorem original_inverse_gauge_scalar (v : Ambient) (hv : v.2=0) (z : physicalChart) :
    fderiv ℝ inverseL z.val (gaugeEuler z.val) v=(0,0,(inverseL z.val v).2.2) := by
  let u := inverseL z.val v
  have hg := congrArg Prod.snd (inverse_right z v)
  change nativeGauge u.1 (z.val.2.2 : Gauge)+(u.2.2 : Gauge)=v.2 at hg
  rw [hv] at hg
  have he : variationL (gaugeEuler z.val) u=splitMap z.val (0,0,-u.2.2) := by
    apply Prod.ext
    · change scalarP286ActionBilinear u.1 0=action (vacuum+(z.val.2.1 : Scalar)) 0+0
      rw [map_zero,map_zero,add_zero]
    · change nativeGauge u.1 (z.val.2.2 : Gauge)=nativeGauge 0 (z.val.2.2 : Gauge)+↑(-u.2.2)
      rw [map_zero,LinearMap.zero_apply,zero_add]
      exact eq_neg_of_add_eq_zero_left hg
  rw [inverse_derivative]
  change -inverseL z.val (variationL (gaugeEuler z.val) u)=_
  rw [he,inverse_left]
  simp only [Prod.neg_mk,neg_zero,neg_neg]
  rfl

private theorem inverse_value_derivative (v : Ambient) (z : physicalChart) :
    HasFDerivAt (fun w => inverseL w v) ((fderiv ℝ inverseL z.val).flip v) z.val := by
  have hd := (((inverse_smooth z).differentiableAt (by simp)).hasFDerivAt).clm_apply
    (hasFDerivAt_const v z.val)
  simpa only [ContinuousLinearMap.comp_zero,zero_add] using! hd

private theorem direction_derivative (v : Ambient) (z : physicalChart) (e : SourceCoordinateSlice) :
    fderiv ℝ (direction v) z.val e=(0,(fderiv ℝ inverseL z.val e v).2) := by
  have hd := (hasFDerivAt_const (0 : Coframe) z.val).prodMk ((inverse_value_derivative v z).snd)
  exact congrArg (fun D : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice => D e) hd.fderiv

private theorem phi_scalar_bracket (v : Ambient) (hv : v.2=0) (z : physicalChart) :
    VectorField.lieBracket ℝ phiEuler (direction v) z.val= -direction v z.val := by
  rw [VectorField.lieBracket,direction_derivative,original_inverse_phi_scalar v hv z,(phi_derivative z.val).fderiv]
  apply Prod.ext
  · change (0 : Coframe)-0= -0
    simp only [sub_self,neg_zero]
  · apply Prod.ext
    · change -0-(inverseL z.val v).2.1= -(inverseL z.val v).2.1
      simp only [neg_zero,zero_sub]
    · change -(inverseL z.val v).2.2-0= -(inverseL z.val v).2.2
      exact sub_zero _

private theorem phi_gauge_bracket (v : Ambient) (hv : v.1=0) (z : physicalChart) :
    VectorField.lieBracket ℝ phiEuler (direction v) z.val=0 := by
  rw [VectorField.lieBracket,direction_derivative,original_inverse_phi_gauge v hv z,(phi_derivative z.val).fderiv]
  change ((0,(inverseL z.val v).2.1,0) : SourceCoordinateSlice)-(0,(inverseL z.val v).2.1,0)=0
  exact sub_self _

private def gaugeLinear : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice :=
  (0 : SourceCoordinateSlice →L[ℝ] Coframe).prod
    ((0 : SourceCoordinateSlice →L[ℝ] scalarSlice).prod
      ((ContinuousLinearMap.snd ℝ scalarSlice coordinateSlice).comp
        (ContinuousLinearMap.snd ℝ Coframe (scalarSlice × coordinateSlice))))

private theorem gauge_derivative (z : SourceCoordinateSlice) : HasFDerivAt gaugeEuler gaugeLinear z :=
  gaugeLinear.hasFDerivAt

private theorem gauge_scalar_bracket (v : Ambient) (hv : v.2=0) (z : physicalChart) :
    VectorField.lieBracket ℝ gaugeEuler (direction v) z.val=0 := by
  rw [VectorField.lieBracket,direction_derivative,original_inverse_gauge_scalar v hv z,(gauge_derivative z.val).fderiv]
  change ((0,0,(inverseL z.val v).2.2) : SourceCoordinateSlice)-(0,0,(inverseL z.val v).2.2)=0
  exact sub_self _

private theorem connection_derivative (v : Ambient) (z : physicalChart) (e : SourceCoordinateSlice) :
    fderiv ℝ (connection v) z.val e=nativeFock (fderiv ℝ inverseL z.val e v).1 := by
  have hd := nativeFock.toContinuousLinearMap.hasFDerivAt.comp z.val ((inverse_value_derivative v z).fst)
  exact congrArg (fun D : SourceCoordinateSlice →L[ℝ] (FockFiber →L[ℂ] FockFiber) => D e) hd.fderiv

private theorem real_fock_smul (r : ℝ) (x : FockFiber) : r • x=(r : ℂ) • x := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem directional_degree (E : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (e z))
    (he : ∀ z,DifferentiableAt ℝ e z) (v : Ambient) (c : ℝ)
    (hb : ∀ z : physicalChart,VectorField.lieBracket ℝ e (direction v) z.val=c • direction v z.val) :
    E*directional v-directional v*E=(c : ℂ) • directional v := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change E (directional v f) z-directional v (E f) z=(c : ℂ) • directional v f z
  by_cases hz : z∈physicalChart
  · have hD : (directional v f : SourceCoordinateSlice → FockFiber)=
        fun x => fderiv ℝ f x (direction v x) := funext (directional_apply v f)
    have hEf : (E f : SourceCoordinateSlice → FockFiber)=fun x => fderiv ℝ f x (e x) := funext (hE f)
    rw [hE,directional_apply,directional_apply,hD,hEf]
    have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
      (V := e) (W := direction v) (x := z) f.contDiff.contDiffAt (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      ((direction_smooth v ⟨z,hz⟩).differentiableAt (by simp)) (he z)
    rw [hb ⟨z,hz⟩,map_smul,real_fock_smul] at h
    exact h.symm
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz (q.tsupport_subset h))
    rw [h0,h0,h0,sub_self,smul_zero]

private theorem multiplier_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B : E → V →L[ℂ] V) (f : E → V) (z e : E) (c : ℝ)
    (hB : DifferentiableAt ℝ B z) (hf : DifferentiableAt ℝ f z)
    (h : fderiv ℝ B z e=(c : ℂ) • B z) :
    fderiv ℝ (fun x => B x (f x)) z e=B z (fderiv ℝ f z e)+(c : ℂ) • B z (f z) := by
  have hr := (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp z hB.hasFDerivAt
  have hd := (hr.clm_apply hf.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => B x (f x)) z=_ at hd
  rw [hd]
  change B z (fderiv ℝ f z e)+(fderiv ℝ B z e) (f z)=_
  rw [h]
  rfl

private theorem connection_degree (E : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (e z)) (v : Ambient) (c : ℝ)
    (hc : ∀ z : physicalChart,fderiv ℝ (connection v) z.val (e z.val)=(c : ℂ) • connection v z.val) :
    E*localMultiplier (connection v) (connection_smooth v)-
      localMultiplier (connection v) (connection_smooth v)*E=
      (c : ℂ) • localMultiplier (connection v) (connection_smooth v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let A := localMultiplier (connection v) (connection_smooth v)
  change E (A f) z-A (E f) z=(c : ℂ) • A f z
  by_cases hz : z∈physicalChart
  · rw [hE]
    change fderiv ℝ (fun x => connection v x (f x)) z (e z)-connection v z (E f z)=_
    rw [hE,multiplier_derivative (connection v) f z (e z) c
      ((connection_smooth v ⟨z,hz⟩).differentiableAt (by simp))
      ((f.contDiff.differentiable (by simp)) z) (hc ⟨z,hz⟩)]
    exact add_sub_cancel_left _ _
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz (q.tsupport_subset h))
    rw [h0,h0,h0,sub_self,smul_zero]

private theorem scaled_ad_eigen {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (E B : R) (c k : ℂ) (h : E*B-B*E=c • B) :
    E*(k • B)-(k • B)*E=c • (k • B) := by
  rw [mul_smul_comm,smul_mul_assoc,←smul_sub,h,smul_comm k c B]

private theorem momentum_degree (E : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (e z))
    (he : ∀ z,DifferentiableAt ℝ e z) (v : Ambient) (c : ℝ)
    (hb : ∀ z : physicalChart,VectorField.lieBracket ℝ e (direction v) z.val=c • direction v z.val)
    (hc : ∀ z : physicalChart,fderiv ℝ (connection v) z.val (e z.val)=(c : ℂ) • connection v z.val) :
    E*covariantMomentum v-covariantMomentum v*E=(c : ℂ) • covariantMomentum v := by
  have hD := directional_degree E e hE he v c hb
  have hC := connection_degree E e hE v c hc
  have h : E*(directional v+localMultiplier (connection v) (connection_smooth v))-
      (directional v+localMultiplier (connection v) (connection_smooth v))*E=
      (c : ℂ) • (directional v+localMultiplier (connection v) (connection_smooth v)) := by
    simp only [mul_add,add_mul,smul_add]
    linear_combination (norm := module) hD+hC
  exact scaled_ad_eigen (R := End) E _ (c : ℂ) (-Complex.I) h

/-- Every one of the original seventy scalar momenta has shifted-scalar degree -1. -/
theorem original_scalar_momentum_phi (v : Ambient) (hv : v.2=0) :
    phiEulerAction*covariantMomentum v-covariantMomentum v*phiEulerAction= -covariantMomentum v := by
  have h := momentum_degree phiEulerAction phiEuler phi_euler_apply
    (fun z => (phi_derivative z).differentiableAt) v (-1)
    (fun z => by simpa only [neg_one_smul] using phi_scalar_bracket v hv z)
    (fun z => by
      rw [connection_derivative,original_inverse_phi_scalar v hv z]
      simp only [Complex.ofReal_neg,Complex.ofReal_one]
      have h := (map_neg nativeFock (inverseL z.val v).1).trans
        (neg_one_smul ℂ (nativeFock (inverseL z.val v).1)).symm
      run_tac Lean.Elab.Tactic.withMainContext do
        (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
        Lean.Elab.Tactic.replaceMainGoal [])
  simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul] using! h

theorem original_gauge_momentum_phi (v : Ambient) (hv : v.1=0) :
    phiEulerAction*covariantMomentum v-covariantMomentum v*phiEulerAction=0 := by
  have h := momentum_degree phiEulerAction phiEuler phi_euler_apply
    (fun z => (phi_derivative z).differentiableAt) v 0
    (fun z => by simpa only [zero_smul] using phi_gauge_bracket v hv z)
    (fun z => by
      rw [connection_derivative,original_inverse_phi_gauge v hv z]
      change nativeFock 0=(0 : ℂ) • connection v z.val
      have h := (map_zero nativeFock).trans (zero_smul ℂ (connection v z.val)).symm
      run_tac Lean.Elab.Tactic.withMainContext do
        (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
        Lean.Elab.Tactic.replaceMainGoal [])
  simpa only [Complex.ofReal_zero,zero_smul] using! h

theorem original_scalar_momentum_gauge (v : Ambient) (hv : v.2=0) :
    deltaGauge (covariantMomentum v)=0 := by
  have h := momentum_degree gaugeEulerAction gaugeEuler gauge_euler_apply
    (fun z => (gauge_derivative z).differentiableAt) v 0
    (fun z => by simpa only [zero_smul] using gauge_scalar_bracket v hv z)
    (fun z => by
      rw [connection_derivative,original_inverse_gauge_scalar v hv z]
      change nativeFock 0=(0 : ℂ) • connection v z.val
      have h := (map_zero nativeFock).trans (zero_smul ℂ (connection v z.val)).symm
      run_tac Lean.Elab.Tactic.withMainContext do
        (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
        Lean.Elab.Tactic.replaceMainGoal [])
  simpa only [deltaGauge,Complex.ofReal_zero,zero_smul] using! h

def deltaPhi : End →ₗ[ℂ] End where
  toFun A := phiEulerAction*A-A*phiEulerAction
  map_add' A B := by noncomm_ring
  map_smul' c A := by simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private theorem i_skew (x y : ℂ) (h : (-Complex.I)*x=Complex.I*y) : x= -y := by
  apply mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero)
  rw [h]
  ring

private theorem vacuum_derivative_pair (f g : QuantumTest) :
    sourcePair f (GaussCoframeCore.derivative (scalarAxis vacuumSlice) g)=
      -sourcePair (GaussCoframeCore.derivative (scalarAxis vacuumSlice) f) g := by
  have h := flat_momentum_pair vacuumSlice f g
  change inner ℂ (embed f) (embed ((-Complex.I) • GaussCoframeCore.derivative (scalarAxis vacuumSlice) g))=
    inner ℂ (embed ((-Complex.I) • GaussCoframeCore.derivative (scalarAxis vacuumSlice) f)) (embed g) at h
  simp only [map_smul,inner_smul_right,inner_smul_left,map_neg,Complex.conj_I,neg_neg] at h
  exact i_skew _ _ h

private theorem phi_pair_shift (f g : QuantumTest) :
    sourcePair f (phiEulerAction g)= -sourcePair (phiEulerAction f) g-(61 : ℂ)*sourcePair f g := by
  have hs := scalar_euler_current f g
  have hd := vacuum_derivative_pair f g
  simp only [phiEulerAction,LinearMap.add_apply,sourcePair,map_add,inner_add_right,inner_add_left] at hd hs ⊢
  linear_combination (norm := ring) hs+hd

private theorem gauge_pair_shift (f g : QuantumTest) :
    sourcePair f (gaugeEulerAction g)= -sourcePair (gaugeEulerAction f) g-(36 : ℂ)*sourcePair f g := by
  rw [gauge_euler_pair,gauge_euler_transpose]
  simp only [sourcePair,map_sub,map_neg,map_smul,inner_sub_left,inner_neg_left,inner_smul_left,map_ofNat]

private theorem transpose_degree (E A B : End) (c rho : ℂ) (hc : starRingEnd ℂ c=c)
    (he : ∀ f g,sourcePair f (E g)= -sourcePair (E f) g-rho*sourcePair f g)
    (hp : ∀ f g,sourcePair f (B g)=sourcePair (A f) g)
    (hA : E*A-A*E=c • A) : E*B-B*E=c • B := by
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have ha := congrArg (fun C : End => sourcePair (C f) g) hA
  change sourcePair (E (A f)-A (E f)) g=sourcePair (c • A f) g at ha
  have hx := he f (B g)
  rw [hp (E f) g,hp f g] at hx
  have hy := he (A f) g
  rw [←hp f (E g)] at hy
  change sourcePair f (E (B g)-B (E g))=sourcePair f (c • B g)
  simp only [sourcePair,map_sub,map_smul,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,hc] at ha hx hy ⊢
  have hb := hp f g
  unfold sourcePair at hb
  linear_combination (norm := ring) ha+hx-hy-c*hb

theorem original_scalar_adjoint_phi (v : Ambient) (hv : v.2=0) :
    deltaPhi (GaussMomentumAdjoint.adjoint v)= -GaussMomentumAdjoint.adjoint v := by
  have h := transpose_degree phiEulerAction (covariantMomentum v) (GaussMomentumAdjoint.adjoint v)
    (-1) 61 (by simp) phi_pair_shift (adjoint_pair v)
    (by simpa only [neg_one_smul] using! original_scalar_momentum_phi v hv)
  simpa only [neg_one_smul] using! h

theorem original_gauge_adjoint_phi (v : Ambient) (hv : v.1=0) :
    deltaPhi (GaussMomentumAdjoint.adjoint v)=0 := by
  have h := transpose_degree phiEulerAction (covariantMomentum v) (GaussMomentumAdjoint.adjoint v)
    0 61 (by simp) phi_pair_shift (adjoint_pair v)
    (by simpa only [zero_smul] using! original_gauge_momentum_phi v hv)
  simpa only [zero_smul] using! h

theorem original_scalar_adjoint_gauge (v : Ambient) (hv : v.2=0) :
    deltaGauge (GaussMomentumAdjoint.adjoint v)=0 := by
  have h := transpose_degree gaugeEulerAction (covariantMomentum v) (GaussMomentumAdjoint.adjoint v)
    0 36 (by simp) gauge_pair_shift (adjoint_pair v)
    (by simpa only [zero_smul] using! original_scalar_momentum_gauge v hv)
  simpa only [zero_smul] using! h

private theorem ad_product {R : Type*} [Ring R] (E A B : R) :
    E*(A*B)-(A*B)*E=(E*A-A*E)*B+A*(E*B-B*E) := by noncomm_ring
private theorem phi_product (A B : End) : deltaPhi (A*B)=deltaPhi A*B+A*deltaPhi B :=
  ad_product _ _ _
private theorem gauge_product (A B : End) : deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B :=
  ad_product _ _ _

private def phiScale (r : ℝ) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (z.1,r • (vacuumSlice+z.2.1)-vacuumSlice,z.2.2)
private theorem phi_scale_one (z : SourceCoordinateSlice) : phiScale 1 z=z := by
  simp [phiScale]
private theorem phi_scale_derivative (z : SourceCoordinateSlice) :
    HasDerivAt (fun r => phiScale r z) (phiEuler z) 1 := by
  simpa only [phiScale,phiEuler,id_eq,one_smul] using!
    (hasDerivAt_const (1 : ℝ) z.1).prodMk
      ((((hasDerivAt_id (1 : ℝ)).smul_const (vacuumSlice+z.2.1)).sub_const vacuumSlice).prodMk
        (hasDerivAt_const (1 : ℝ) z.2.2))

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

private theorem euler_multiplier (E : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (flow : ℝ → SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (e z))
    (hg : ∀ z,HasDerivAt (fun r => flow r z) (e z) 1) (h1 : ∀ z,flow 1 z=z)
    (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (law : ∀ f z,A f z=B z (f z)) (hinv : ∀ r z,B (flow r z)=B z) : E*A-A*E=0 := by
  apply sub_eq_zero.mpr
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change E (A f) z=A (E f) z
  rw [hE,law,hE]
  have h := invariant_derivative (E := SourceCoordinateSlice) (V := FockFiber)
    ((B z).restrictScalars ℝ) f (A f) (fun r => flow r z) z (e z)
    (hg z) (h1 z) ((f.contDiff.differentiable (by simp)) z) (((A f).contDiff.differentiable (by simp)) z)
    (fun r => by rw [law,hinv]; rfl)
  simpa only [ContinuousLinearMap.coe_restrictScalars'] using! h

private theorem phi_multiplier (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (law : ∀ f z,A f z=B z (f z)) (hinv : ∀ r z,B (phiScale r z)=B z) : deltaPhi A=0 :=
  euler_multiplier phiEulerAction phiEuler phiScale phi_euler_apply phi_scale_derivative phi_scale_one A B law hinv
private theorem gauge_multiplier (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (law : ∀ f z,A f z=B z (f z)) (hinv : ∀ r z,B (gaugeScale r z)=B z) : deltaGauge A=0 :=
  euler_multiplier gaugeEulerAction gaugeEuler gaugeScale gauge_euler_apply
    (fun z => gauge_scale_derivative z 1) gauge_scale_one A B law hinv

private theorem phi_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv : ∀ r z,c (phiScale r z)=c z) : deltaPhi (multiply c hc)=0 :=
  phi_multiplier _ (fun z => (c z : ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _ => rfl) (fun r z => congrArg (fun x : ℝ => (x : ℂ) • ContinuousLinearMap.id ℂ FockFiber) (hinv r z))
private theorem gauge_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv : ∀ r z,c (gaugeScale r z)=c z) : deltaGauge (multiply c hc)=0 :=
  gauge_multiplier _ (fun z => (c z : ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _ => rfl) (fun r z => congrArg (fun x : ℝ => (x : ℂ) • ContinuousLinearMap.id ℂ FockFiber) (hinv r z))

private theorem sandwich_degree (D : End →ₗ[ℂ] End)
    (hD : ∀ A B,D (A*B)=D A*B+A*D B) (v w : Ambient)
    (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (a b : ℂ) (hA : D (GaussMomentumAdjoint.adjoint v)=a • GaussMomentumAdjoint.adjoint v)
    (hM : D (multiply c hc)=0) (hP : D (covariantMomentum w)=b • covariantMomentum w) :
    D (sandwich v w c hc)=(a+b) • sandwich v w c hc := by
  change D (GaussMomentumAdjoint.adjoint v*(multiply c hc*covariantMomentum w))=
    (a+b) • (GaussMomentumAdjoint.adjoint v*(multiply c hc*covariantMomentum w))
  rw [hD,hD,hA,hM,hP]
  simp only [zero_mul,zero_add,smul_mul_assoc,mul_smul_comm,add_smul]

/-- The whole native70 scalar kinetic sector has degree -2 under the shifted source Euler. -/
theorem original_scalar_kinetic_phi : deltaPhi scalarKinetic=(-2 : ℂ) • scalarKinetic := by
  have hs (i : ScalarIndex) : deltaPhi (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth)=
      (-2 : ℂ) • sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth := by
    have h := sandwich_degree deltaPhi phi_product (scalarDirection i) (scalarDirection i)
      scalarWeight scalarWeight_smooth (-1) (-1)
      (by simpa only [neg_one_smul] using! original_scalar_adjoint_phi (scalarDirection i) rfl)
      (phi_real _ _ (fun _ _ => rfl))
      (by simpa only [neg_one_smul] using! original_scalar_momentum_phi (scalarDirection i) rfl)
    norm_num only [show (-1 : ℂ)+ -1= -2 by norm_num] at h
    exact h
  simp only [scalarKinetic,map_smul,map_sum,hs,←Finset.smul_sum]
  module

theorem original_scalar_kinetic_gauge : deltaGauge scalarKinetic=0 := by
  have hs (i : ScalarIndex) : deltaGauge (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth)=0 := by
    have h := sandwich_degree deltaGauge gauge_product (scalarDirection i) (scalarDirection i)
      scalarWeight scalarWeight_smooth 0 0
      (by simpa only [zero_smul] using! original_scalar_adjoint_gauge (scalarDirection i) rfl)
      (gauge_real _ _ (fun _ _ => rfl))
      (by simpa only [zero_smul] using! original_scalar_momentum_gauge (scalarDirection i) rfl)
    simpa only [zero_add,zero_smul] using! h
  simp only [scalarKinetic,map_smul,map_sum,hs,Finset.sum_const_zero,smul_zero]

theorem original_gauge_kinetic_phi : deltaPhi gaugeKinetic=0 := by
  have hs (a : LieIndex) (i j : Fin 3) : deltaPhi (sandwich (gaugeDirection i a) (gaugeDirection j a)
      (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j))=0 := by
    have h := sandwich_degree deltaPhi phi_product (gaugeDirection i a) (gaugeDirection j a)
      (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) 0 0
      (by simpa only [zero_smul] using! original_gauge_adjoint_phi (gaugeDirection i a) rfl)
      (phi_real _ _ (fun _ _ => rfl))
      (by simpa only [zero_smul] using! original_gauge_momentum_phi (gaugeDirection j a) rfl)
    simpa only [zero_add,zero_smul] using! h
  simp only [gaugeKinetic,map_smul,map_sum,hs,Finset.sum_const_zero,smul_zero]

theorem original_gauge_kinetic_gauge : deltaGauge gaugeKinetic=(-2 : ℂ) • gaugeKinetic := by
  have hs (a : LieIndex) (i j : Fin 3) : deltaGauge (sandwich (gaugeDirection i a) (gaugeDirection j a)
      (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j))=
      (-2 : ℂ) • sandwich (gaugeDirection i a) (gaugeDirection j a)
        (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) := by
    have h := sandwich_degree deltaGauge gauge_product (gaugeDirection i a) (gaugeDirection j a)
      (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) (-1) (-1)
      (by simpa only [neg_one_smul] using! original_gauge_adjoint_scale (gaugeDirection i a) rfl)
      (gauge_real _ _ (fun _ _ => rfl))
      (by simpa only [neg_one_smul] using! original_gauge_momentum_scale (gaugeDirection j a) rfl)
    norm_num only [show (-1 : ℂ)+ -1= -2 by norm_num] at h
    exact h
  simp only [gaugeKinetic,map_smul,map_sum,hs,←Finset.smul_sum]
  module

private theorem coframe_derivative_commute (E : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (e z)) (he : ∀ z,DifferentiableAt ℝ e z)
    (i : Fin 6) (hde : ∀ z,fderiv ℝ e z (GaussCoframeCore.coframeDirection i)=0) :
    E*GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)-
      GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)*E=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change E (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f) z-
      GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (E f) z=0
  have hD : (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f : SourceCoordinateSlice → FockFiber)=
      fun x => fderiv ℝ f x (GaussCoframeCore.coframeDirection i) := funext (GaussCoframeCore.derivative_apply _ f)
  have hEf : (E f : SourceCoordinateSlice → FockFiber)=fun x => fderiv ℝ f x (e x) := funext (hE f)
  rw [hE,GaussCoframeCore.derivative_apply,hD,hEf]
  have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
    (V := e) (W := fun _ => GaussCoframeCore.coframeDirection i) (x := z) f.contDiff.contDiffAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) (differentiableAt_const _) (he z)
  have hb : VectorField.lieBracket ℝ e (fun _ => GaussCoframeCore.coframeDirection i) z=0 := by
    rw [VectorField.lieBracket,(hasFDerivAt_const (GaussCoframeCore.coframeDirection i) z).fderiv,
      zero_apply,hde,sub_self]
  rw [hb,map_zero] at h
  exact h.symm

private theorem phi_coframe_momentum (i : Fin 6) : deltaPhi (GaussCoframeCore.momentum i)=0 := by
  have h := coframe_derivative_commute phiEulerAction phiEuler phi_euler_apply
    (fun z => (phi_derivative z).differentiableAt) i (fun z => by rw [(phi_derivative z).fderiv]; rfl)
  have hs := scaled_ad_eigen (R := End) phiEulerAction _ 0 (-Complex.I)
    (by simpa only [zero_smul] using! h)
  simpa only [zero_smul] using! hs
private theorem gauge_coframe_momentum (i : Fin 6) : deltaGauge (GaussCoframeCore.momentum i)=0 := by
  have h := coframe_derivative_commute gaugeEulerAction gaugeEuler gauge_euler_apply
    (fun z => (gauge_derivative z).differentiableAt) i (fun z => by rw [(gauge_derivative z).fderiv]; rfl)
  have hs := scaled_ad_eigen (R := End) gaugeEulerAction _ 0 (-Complex.I)
    (by simpa only [zero_smul] using! h)
  simpa only [zero_smul] using! hs
private theorem phi_coframe_adjoint (i : Fin 6) : deltaPhi (GaussCoframeCore.adjoint i)=0 := by
  have h := transpose_degree phiEulerAction (GaussCoframeCore.momentum i) (GaussCoframeCore.adjoint i)
    0 61 (by simp) phi_pair_shift (GaussCoframeKinetic.adjoint_pair i)
    (by simpa only [zero_smul] using! phi_coframe_momentum i)
  simpa only [zero_smul] using! h
private theorem gauge_coframe_adjoint (i : Fin 6) : deltaGauge (GaussCoframeCore.adjoint i)=0 := by
  have h := transpose_degree gaugeEulerAction (GaussCoframeCore.momentum i) (GaussCoframeCore.adjoint i)
    0 36 (by simp) gauge_pair_shift (GaussCoframeKinetic.adjoint_pair i)
    (by simpa only [zero_smul] using! gauge_coframe_momentum i)
  simpa only [zero_smul] using! h

private theorem end_comp (A B : End) : A.comp B=A*B := rfl

private theorem coframe_action_invariant (D : End →ₗ[ℂ] End)
    (hD : ∀ A B,D (A*B)=D A*B+A*D B)
    (hm : ∀ i,D (GaussCoframeCore.momentum i)=0) (ha : ∀ i,D (GaussCoframeCore.adjoint i)=0)
    (hs : ∀ a,D (GaussCoframeSpin.current a)=0) (hn : D GaussCoframeForm.number=0)
    (hcoef : ∀ i j,D (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j))=0)
    (hcur : ∀ j,D (multiply (GaussCoframeForm.currentCoefficient j) (GaussCoframeForm.currentCoefficient_smooth j))=0)
    (hneg : D (multiply (fun z => -GaussCoframeForm.currentCoefficient 0 z)
      (fun z => (GaussCoframeForm.currentCoefficient_smooth 0 z).neg))=0)
    (hinv : D (multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth)=0)
    (hnum : D (multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth)=0)
    (hvol : D (multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth)=0) :
    D GaussCoframeForm.coframeAction=0 := by
  simp only [GaussCoframeForm.coframeAction,GaussCoframeKinetic.kinetic,GaussCoframeKinetic.term,
    GaussCoframeForm.currentAction,GaussCoframeForm.mixed,GaussCoframeForm.spinSquare,GaussCoframeForm.numberShift,
    end_comp,map_add,map_sum,map_smul,hD,hm,ha,hs,hn,hcoef,hcur,hneg,hinv,hnum,hvol,
    zero_mul,mul_zero,add_zero,smul_zero,Finset.sum_const_zero]

/-- Every original coframe kinetic/current/spin/Number/volume component is scalar-affine invariant. -/
theorem original_coframe_phi : deltaPhi GaussCoframeForm.coframeAction=0 := by
  apply coframe_action_invariant deltaPhi phi_product phi_coframe_momentum phi_coframe_adjoint
  · intro a
    exact phi_multiplier _ (fun _ => GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a))
      (fun _ _ => rfl) (fun _ _ => rfl)
  · exact phi_multiplier _ (fun _ => SourceQuantumFockGauge.fiberNumber)
      SourceEulerCore.number_fiber (fun _ _ => rfl)
  · intro i j; exact phi_real _ _ (fun _ _ => rfl)
  · intro j; exact phi_real _ _ (fun _ _ => rfl)
  · exact phi_real _ _ (fun _ _ => rfl)
  · exact phi_real _ _ (fun _ _ => rfl)
  · exact phi_real _ _ (fun _ _ => rfl)
  · exact phi_real _ _ (fun _ _ => rfl)

theorem original_coframe_gauge : deltaGauge GaussCoframeForm.coframeAction=0 := by
  apply coframe_action_invariant deltaGauge gauge_product gauge_coframe_momentum gauge_coframe_adjoint
  · intro a
    exact gauge_multiplier _ (fun _ => GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a))
      (fun _ _ => rfl) (fun _ _ => rfl)
  · exact gauge_multiplier _ (fun _ => SourceQuantumFockGauge.fiberNumber)
      SourceEulerCore.number_fiber (fun _ _ => rfl)
  · intro i j; exact gauge_real _ _ (fun _ _ => rfl)
  · intro j; exact gauge_real _ _ (fun _ _ => rfl)
  · exact gauge_real _ _ (fun _ _ => rfl)
  · exact gauge_real _ _ (fun _ _ => rfl)
  · exact gauge_real _ _ (fun _ _ => rfl)
  · exact gauge_real _ _ (fun _ _ => rfl)

private theorem homogeneous_multiplier (E : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (flow : ℝ → SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (e z))
    (hg : ∀ z,HasDerivAt (fun r => flow r z) (e z) 1) (h1 : ∀ z,flow 1 z=z)
    (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber) (p : ℕ)
    (law : ∀ f z,A f z=B z (f z)) (hp : ∀ r z,B (flow r z)=((r^p : ℝ) : ℂ) • B z) :
    E*A-A*E=(p : ℂ) • A := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (hg z) (h1 z).symm
  have hA := ((A f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (hg z) (h1 z).symm
  have hb := (B z).restrictScalars ℝ |>.hasFDerivAt |>.comp_hasDerivAt 1 hf
  have hr : HasDerivAt (fun r : ℝ => ((r^p : ℝ) : ℂ)) (p : ℂ) 1 := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).pow p)
    simpa only [Function.comp_def,id_eq,one_pow,mul_one,Complex.ofRealCLM_apply,Complex.ofReal_natCast] using! h
  have hh := hr.smul hb
  have hx : (fun r => A f (flow r z))=(fun r : ℝ => ((r^p : ℝ) : ℂ) • B z (f (flow r z))) := by
    funext r
    rw [law,hp]
    rfl
  change HasDerivAt (fun r => A f (flow r z)) _ 1 at hA
  rw [hx] at hA
  have hu := hA.unique hh
  simp only [Function.comp_def,one_pow,Complex.ofReal_one,one_smul,h1,
    ContinuousLinearMap.coe_restrictScalars'] at hu
  change E (A f) z-A (E f) z=(p : ℂ) • A f z
  rw [hE,law,hE,law,hu]
  exact add_sub_cancel_left _ _

private theorem phi_homogeneous (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (p : ℕ) (law : ∀ f z,A f z=B z (f z))
    (hp : ∀ r z,B (phiScale r z)=((r^p : ℝ) : ℂ) • B z) : deltaPhi A=(p : ℂ) • A :=
  homogeneous_multiplier phiEulerAction phiEuler phiScale phi_euler_apply phi_scale_derivative phi_scale_one A B p law hp
private theorem gauge_homogeneous (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (p : ℕ) (law : ∀ f z,A f z=B z (f z))
    (hp : ∀ r z,B (gaugeScale r z)=((r^p : ℝ) : ℂ) • B z) : deltaGauge A=(p : ℂ) • A :=
  homogeneous_multiplier gaugeEulerAction gaugeEuler gaugeScale gauge_euler_apply
    (fun z => gauge_scale_derivative z 1) gauge_scale_one A B p law hp

private theorem phi_real_degree (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (p : ℕ)
    (hp : ∀ r z,c (phiScale r z)=r^p*c z) : deltaPhi (multiply c hc)=(p : ℂ) • multiply c hc := by
  apply phi_homogeneous _ (fun z => (c z : ℂ) • ContinuousLinearMap.id ℂ FockFiber) p (fun _ _ => rfl)
  intro r z
  rw [hp,Complex.ofReal_mul,smul_smul]
private theorem gauge_real_degree (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (p : ℕ)
    (hp : ∀ r z,c (gaugeScale r z)=r^p*c z) : deltaGauge (multiply c hc)=(p : ℂ) • multiply c hc := by
  apply gauge_homogeneous _ (fun z => (c z : ℂ) • ContinuousLinearMap.id ℂ FockFiber) p (fun _ _ => rfl)
  intro r z
  rw [hp,Complex.ofReal_mul,smul_smul]

open GaussNativePotential
private theorem phi_field (r : ℝ) (z : SourceCoordinateSlice) : scalarField (phiScale r z)=r • scalarField z := by
  change vacuum+(r • (vacuum+(z.2.1 : Scalar))-vacuum)=r • (vacuum+(z.2.1 : Scalar))
  abel
private theorem gauge_connection (r : ℝ) (z : SourceCoordinateSlice) (i : Fin 3) :
    connectionField (gaugeScale r z) i=r • connectionField z i := map_smul (SourceCartanCubic.gaugeCoordinate i) r _
private theorem phi_gradient (r : ℝ) (z : SourceCoordinateSlice) (i : Fin 3) :
    scalarGradient (phiScale r z) i=r • scalarGradient z i := by
  change scalarP286ActionBilinear (connectionField z i) (scalarField (phiScale r z))=_
  rw [phi_field,map_smul]
  rfl
private theorem gauge_gradient (r : ℝ) (z : SourceCoordinateSlice) (i : Fin 3) :
    scalarGradient (gaugeScale r z) i=r • scalarGradient z i := by
  change action (scalarField z) (connectionField (gaugeScale r z) i)=r • action (scalarField z) (connectionField z i)
  rw [gauge_connection,map_smul]
private theorem bracket_scale (r : ℝ) (a b : NativeLie) :
    (SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket (r • a) (r • b) : NativeLie)=
      r^2 • SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket a b := by
  erw [SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket_smul_left,
    SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket_smul_right,smul_smul]
  rw [pow_two]
private theorem gauge_magnetic (r : ℝ) (z : SourceCoordinateSlice) (i : Fin 3) :
    magneticField (gaugeScale r z) i=r^2 • magneticField z i := by
  simp only [magneticField,SourceQuantumGaugeCenterMagnetic.magneticOfConnection,gauge_connection,bracket_scale]
  fin_cases i <;> rfl

private theorem metric_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) (x : ι → E) (r : ℝ) :
    (∑ i,∑ j,M i j*inner ℝ (r • x i) (r • x j))=
      r^2*(∑ i,∑ j,M i j*inner ℝ (x i) (x j)) := by
  simp only [real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private def scalarSpatial (z : SourceCoordinateSlice) : ℝ :=
  -(sourceTime 0*volume z/2 * ∑ i : Fin 3,∑ j : Fin 3,
    inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j))
private theorem scalar_spatial_smooth (z : physicalChart) : ContDiffAt ℝ ∞ scalarSpatial z.val := by
  apply ContDiffAt.neg
  exact (contDiffAt_const.mul volume_smooth.contDiffAt |>.div_const 2).mul
    (ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
      (inverseSpatial_smooth i j z).mul ((scalarGradient_smooth i).contDiffAt.inner ℝ (scalarGradient_smooth j).contDiffAt))))
private theorem magnetic_smooth (z : physicalChart) : ContDiffAt ℝ ∞ magneticPotential z.val := by
  exact (volume_smooth.contDiffAt.div_const _).mul
    (ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
      (inverseSpatial_smooth i j z).mul ((magneticField_smooth i).contDiffAt.inner ℝ (magneticField_smooth j).contDiffAt))))

def scalarSpatialAction : End := multiply scalarSpatial scalar_spatial_smooth
def magneticAction : End := multiply magneticPotential magnetic_smooth

private theorem spatial_homogeneous (flow : ℝ → SourceCoordinateSlice → SourceCoordinateSlice)
    (hv : ∀ r z,volume (flow r z)=volume z)
    (hi : ∀ r z (i j : Fin 3),inverseSpatial (flow r z) i j=inverseSpatial z i j)
    (hg : ∀ r z i,scalarGradient (flow r z) i=r • scalarGradient z i) (r : ℝ) (z : SourceCoordinateSlice) :
    scalarSpatial (flow r z)=r^2*scalarSpatial z := by
  simp only [scalarSpatial,hv,hi,hg]
  rw [metric_smul (inverseSpatial z) (scalarGradient z) r]
  ring

theorem original_signed_spatial_phi : deltaPhi scalarSpatialAction=(2 : ℂ) • scalarSpatialAction :=
  phi_real_degree _ _ 2 (spatial_homogeneous phiScale (fun _ _ => rfl) (fun _ _ _ _ => rfl) phi_gradient)
theorem original_signed_spatial_gauge : deltaGauge scalarSpatialAction=(2 : ℂ) • scalarSpatialAction :=
  gauge_real_degree _ _ 2 (spatial_homogeneous gaugeScale (fun _ _ => rfl) (fun _ _ _ _ => rfl) gauge_gradient)
theorem original_magnetic_phi : deltaPhi magneticAction=0 := phi_real _ _ (fun _ _ => rfl)
theorem original_magnetic_gauge : deltaGauge magneticAction=(4 : ℂ) • magneticAction := by
  apply gauge_real_degree _ _ 4
  intro r z
  simp only [magneticPotential,gauge_magnetic]
  change volume z/(2*sourceSigma*sourceTime 0)*
    (∑ i : Fin 3,∑ j : Fin 3,inverseSpatial z i j*inner ℝ (r^2 • magneticField z i) (r^2 • magneticField z j))=_
  rw [metric_smul (inverseSpatial z) (magneticField z) (r^2)]
  ring

private def centeredPotential (z : SourceCoordinateSlice) : ℝ := sourceTime 0*volume z*‖scalarField z‖^2
private def vacuumLinear (z : SourceCoordinateSlice) : ℝ := sourceTime 0*volume z*inner ℝ vacuum (scalarField z)
private def vacuumConstant (z : SourceCoordinateSlice) : ℝ := sourceTime 0*volume z*‖vacuum‖^2
private theorem centered_smooth (z : physicalChart) : ContDiffAt ℝ ∞ centeredPotential z.val :=
  (contDiffAt_const.mul volume_smooth.contDiffAt).mul (scalarField_smooth.norm_sq ℝ).contDiffAt
private theorem vacuum_linear_smooth (z : physicalChart) : ContDiffAt ℝ ∞ vacuumLinear z.val :=
  (contDiffAt_const.mul volume_smooth.contDiffAt).mul (contDiff_const.inner ℝ scalarField_smooth).contDiffAt
private theorem vacuum_constant_smooth (z : physicalChart) : ContDiffAt ℝ ∞ vacuumConstant z.val :=
  (contDiffAt_const.mul volume_smooth.contDiffAt).mul contDiffAt_const

def centeredAction : End := multiply centeredPotential centered_smooth
def vacuumLinearAction : End := multiply vacuumLinear vacuum_linear_smooth
def vacuumConstantAction : End := multiply vacuumConstant vacuum_constant_smooth

private theorem centered_phi : deltaPhi centeredAction=(2 : ℂ) • centeredAction := by
  apply phi_real_degree _ _ 2
  intro r z
  simp only [centeredPotential,phi_field,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  change sourceTime 0*volume z*(r^2*‖scalarField z‖^2)=_
  ring
private theorem vacuum_linear_phi : deltaPhi vacuumLinearAction=vacuumLinearAction := by
  have h := phi_real_degree vacuumLinear vacuum_linear_smooth 1 (by
    intro r z
    simp only [vacuumLinear,phi_field,real_inner_smul_right,pow_one]
    change sourceTime 0*volume z*(r*inner ℝ vacuum (scalarField z))=_
    ring)
  simpa only [Nat.cast_one,one_smul] using! h
private theorem vacuum_constant_phi : deltaPhi vacuumConstantAction=0 := phi_real _ _ (fun _ _ => rfl)
private theorem centered_gauge : deltaGauge centeredAction=0 := gauge_real _ _ (fun _ _ => rfl)
private theorem vacuum_linear_gauge : deltaGauge vacuumLinearAction=0 := gauge_real _ _ (fun _ _ => rfl)
private theorem vacuum_constant_gauge : deltaGauge vacuumConstantAction=0 := gauge_real _ _ (fun _ _ => rfl)

private def matterTerm (i b : Fin 3) : End :=
  GaussQuantumMultiplier.action (GaussMatterCore.localMatrix i b) (GaussMatterCore.local_smooth i b)
private def matterFiber (i b : Fin 3) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (GaussMatterCore.coefficient i b z : ℂ) • GaussMatterCore.quantumTerm b (connectionField z i)
private theorem matter_term_apply (i b : Fin 3) (f : QuantumTest) (z : SourceCoordinateSlice) :
    matterTerm i b f z=matterFiber i b z (f z) := by
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (map_smul GaussQuantumMultiplier.quantizer (GaussMatterCore.coefficient i b z : ℂ)
      (GaussMatterCore.matrixTerm b (connectionField z i)))

theorem original_matter_phi : deltaPhi GaussMatterCore.matterAction=0 := by
  have h (i b : Fin 3) : deltaPhi (matterTerm i b)=0 :=
    phi_multiplier _ (matterFiber i b) (matter_term_apply i b) (fun _ _ => rfl)
  change deltaPhi (∑ i : Fin 3,∑ b : Fin 3,matterTerm i b)=0
  simp only [map_sum,h,Finset.sum_const_zero]

theorem original_matter_gauge : deltaGauge GaussMatterCore.matterAction=GaussMatterCore.matterAction := by
  have h (i b : Fin 3) : deltaGauge (matterTerm i b)=matterTerm i b := by
    have hh := gauge_homogeneous (matterTerm i b) (matterFiber i b) 1 (matter_term_apply i b) (by
      intro r z
      change (GaussMatterCore.coefficient i b z : ℂ) • GaussMatterCore.quantumTerm b (connectionField (gaugeScale r z) i)=
        ((r^1 : ℝ) : ℂ) • ((GaussMatterCore.coefficient i b z : ℂ) • GaussMatterCore.quantumTerm b (connectionField z i))
      rw [gauge_connection,map_smul,pow_one,smul_comm (GaussMatterCore.coefficient i b z : ℂ) r]
      apply ContinuousLinearMap.ext
      intro f
      exact real_fock_smul r _)
    simpa only [Nat.cast_one,one_smul] using! hh
  change deltaGauge (∑ i : Fin 3,∑ b : Fin 3,matterTerm i b)=∑ i : Fin 3,∑ b : Fin 3,matterTerm i b
  simp only [map_sum,h]

private theorem potential_decompose (z : SourceCoordinateSlice) :
    potential z=centeredPotential z-2*vacuumLinear z+vacuumConstant z+scalarSpatial z+magneticPotential z := by
  have hsub : scalarField z-vacuum=(z.2.1 : Scalar) := by unfold scalarField; abel
  have hn := norm_sub_sq_real (scalarField z) vacuum
  rw [hsub,real_inner_comm vacuum (scalarField z)] at hn
  unfold potential scalarPotential centeredPotential vacuumLinear vacuumConstant scalarSpatial
  rw [real_inner_self_eq_norm_sq,hn]
  ring

private theorem potential_action_decompose :
    multiply potential potential_smooth=centeredAction-(2 : ℂ) • vacuumLinearAction+
      vacuumConstantAction+scalarSpatialAction+magneticAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (potential z : ℂ) • f z=(centeredPotential z : ℂ) • f z-
    (2 : ℂ) • ((vacuumLinear z : ℂ) • f z)+(vacuumConstant z : ℂ) • f z+
    (scalarSpatial z : ℂ) • f z+(magneticPotential z : ℂ) • f z
  rw [potential_decompose]
  push_cast
  simp only [add_smul,sub_smul,mul_smul]

private theorem original_complete_split :
    diagonalAction=scalarKinetic+gaugeKinetic+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction+
      centeredAction-(2 : ℂ) • vacuumLinearAction+vacuumConstantAction+scalarSpatialAction+magneticAction := by
  unfold diagonalAction nativeAction
  rw [potential_action_decompose]
  abel

/-- The negative scalar-spatial potential cancels between two actual source derivations, with vacuum terms retained. -/
theorem original_scalar_gauge_current :
    deltaPhi diagonalAction-deltaGauge diagonalAction=
      (-2 : ℂ) • scalarKinetic+(2 : ℂ) • gaugeKinetic+(2 : ℂ) • centeredAction-
      (2 : ℂ) • vacuumLinearAction-(4 : ℂ) • magneticAction-GaussMatterCore.matterAction := by
  rw [original_complete_split]
  simp only [map_add,map_sub,map_smul,original_scalar_kinetic_phi,original_scalar_kinetic_gauge,
    original_gauge_kinetic_phi,original_gauge_kinetic_gauge,original_coframe_phi,original_coframe_gauge,
    original_matter_phi,original_matter_gauge,centered_phi,centered_gauge,
    vacuum_linear_phi,vacuum_linear_gauge,vacuum_constant_phi,vacuum_constant_gauge,
    original_signed_spatial_phi,original_signed_spatial_gauge,original_magnetic_phi,original_magnetic_gauge]
  module

def filteredBulk : End :=
  let J := deltaPhi diagonalAction-deltaGauge diagonalAction
  deltaGauge (deltaGauge J)-(5 : ℂ) • deltaGauge J+(4 : ℂ) • J

/-- The complete third-order source current removes the true matter/magnetic weights and retains the native70 positive kinetic sign. -/
theorem original_filtered_bulk :
    filteredBulk=(-8 : ℂ) • scalarKinetic+(36 : ℂ) • gaugeKinetic+
      (8 : ℂ) • centeredAction-(8 : ℂ) • vacuumLinearAction := by
  unfold filteredBulk
  rw [original_scalar_gauge_current]
  simp only [map_add,map_sub,map_smul,original_scalar_kinetic_gauge,original_gauge_kinetic_gauge,
    centered_gauge,vacuum_linear_gauge,original_magnetic_gauge,original_matter_gauge,map_zero]
  module

private theorem half_shift_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x v : E) : ‖x-(1/2 : ℝ) • v‖^2=‖x‖^2-inner ℝ v x+(1/4 : ℝ)*‖v‖^2 := by
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,real_inner_comm v x]
  norm_num
  ring

def shiftedPotential (z : SourceCoordinateSlice) : ℝ :=
  sourceTime 0*volume z*‖scalarField z-(1/2 : ℝ) • vacuum‖^2
private theorem shifted_smooth (z : physicalChart) : ContDiffAt ℝ ∞ shiftedPotential z.val :=
  (contDiffAt_const.mul volume_smooth.contDiffAt).mul
    ((scalarField_smooth.sub contDiff_const).norm_sq ℝ).contDiffAt

def shiftedAction : End := multiply shiftedPotential shifted_smooth
def positiveBulk : End := filteredBulk+(2 : ℂ) • vacuumConstantAction

private theorem original_vacuum_completion :
    (8 : ℂ) • centeredAction-(8 : ℂ) • vacuumLinearAction+(2 : ℂ) • vacuumConstantAction=
      (8 : ℂ) • shiftedAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hc : 8*centeredPotential z-8*vacuumLinear z+2*vacuumConstant z=8*shiftedPotential z := by
    unfold centeredPotential vacuumLinear vacuumConstant shiftedPotential
    rw [half_shift_norm]
    ring
  have hh := congrArg (fun r : ℝ => (r : ℂ) • f z) hc
  push_cast at hh
  simpa only [add_smul,sub_smul,mul_smul] using! hh

/-- The full original source generates a positive kinetic/shifted-scalar current after its exact vacuum compensation. -/
theorem original_positive_bulk :
    positiveBulk=(-8 : ℂ) • scalarKinetic+(36 : ℂ) • gaugeKinetic+(8 : ℂ) • shiftedAction := by
  have h := original_vacuum_completion
  rw [positiveBulk,original_filtered_bulk]
  linear_combination (norm := module) h

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem scalar_multiplier_sign (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sign : ℝ)
    (hs : ∀ z : physicalChart,0 ≤ sign*c z.val) (f : QuantumTest) :
    0 ≤ sign*(sourcePair f (multiply c hc f)).re := by
  rw [sourcePair_integral]
  have hr : (∫ z, densityPair f (multiply c hc f) z ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫ z, (densityPair f (multiply c hc f) z).re ∂GaussHistoryHilbert.configurationMeasure := by
    simpa only using! (integral_re (densityPair_integrable f (multiply c hc f))).symm
  rw [hr,←MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_nonneg
  intro z
  change 0 ≤ sign*(densityPair f (multiply c hc f) z).re
  have he : densityPair f (multiply c hc f) z=(c z : ℂ)*densityPair f f z := inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  by_cases hz : z∈physicalChart
  · have hp : 0 ≤ (densityPair f f z).re := by
      change 0 ≤ (inner ℂ (GaussFockWeights.weight (fun N => (GaussDensityCore.density N z : ℂ)) (f z)) (f z)).re
      have hw := GaussBoundedMultiplier.weighted_square (fun N => GaussDensityCore.density N z)
        (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
      have hp := (sq_nonneg ‖GaussBoundedMultiplier.halfWeight (fun N => GaussDensityCore.density N z) (f z)‖).trans_eq hw.symm
      simpa only using! hp
    simpa only [mul_assoc] using mul_nonneg (hs ⟨z,hz⟩) hp
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,mul_zero]
    exact le_refl _

/-- The sign uses all seventy native momenta with the original negative source coefficient. -/
theorem original_scalar_kinetic_nonpositive (f : QuantumTest) : (sourcePair f (scalarKinetic f)).re ≤ 0 := by
  have h (i : ScalarIndex) :
      (sourcePair f (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth f)).re ≤ 0 := by
    change (sourcePair f (GaussMomentumAdjoint.adjoint (scalarDirection i)
      (multiply scalarWeight scalarWeight_smooth (covariantMomentum (scalarDirection i) f)))).re ≤ 0
    rw [adjoint_pair]
    have hp := scalar_multiplier_sign scalarWeight scalarWeight_smooth (-1) (by
      intro z
      rw [scalarWeight]
      have he : (-1 : ℝ)*(-sourceTime 0/volume z.val)=sourceTime 0/volume z.val := by ring
      rw [he]
      exact div_nonneg lapse_pos.le (volume_pos z).le) (covariantMomentum (scalarDirection i) f)
    linarith
  have he : (sourcePair f (scalarKinetic f)).re=
      (1/2 : ℝ)*∑ i : ScalarIndex,
        (sourcePair f (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth f)).re := by
    simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,
      inner_smul_right,inner_sum]
    have hc (x : ℂ) : ((1/2 : ℂ)*x).re=(1/2 : ℝ)*x.re := by norm_num [Complex.mul_re]
    rw [hc,Complex.re_sum]
  rw [he]
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (Finset.sum_nonpos (fun i _ => h i))

theorem original_gauge_kinetic_nonnegative (f : QuantumTest) : 0 ≤ (sourcePair f (gaugeKinetic f)).re := by
  have h := SourceElectricCompletedSquare.gauge_pair_nonneg
    (fun a i => SourceElectricColumns.column i a f)
  rw [SourceElectricCompletedSquare.gauge_kinetic_columns] at h
  have hc (x : ℂ) : ((2 : ℂ)*x).re=2*x.re := by norm_num [Complex.mul_re]
  rw [hc] at h
  linarith

theorem original_shifted_nonnegative (f : QuantumTest) : 0 ≤ (sourcePair f (shiftedAction f)).re := by
  have h := scalar_multiplier_sign shiftedPotential shifted_smooth 1 (by
    intro z
    rw [one_mul,shiftedPotential]
    exact mul_nonneg (mul_nonneg lapse_pos.le (volume_pos z).le) (sq_nonneg _)) f
  simpa only [one_mul] using! h

/-- This positivity is derived for the filtered source current; no positivity of H0 is assumed. -/
theorem original_bulk_nonnegative (f : QuantumTest) : 0 ≤ (sourcePair f (positiveBulk f)).re := by
  have hK := original_scalar_kinetic_nonpositive f
  have hE := original_gauge_kinetic_nonnegative f
  have hL := original_shifted_nonnegative f
  rw [original_positive_bulk]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,inner_add_right,inner_smul_right]
  norm_num only [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.re_ofNat,Complex.im_ofNat,mul_zero,sub_zero]
  simp only [zero_mul,sub_zero]
  change 0 ≤ -8*(sourcePair f (scalarKinetic f)).re+36*(sourcePair f (gaugeKinetic f)).re+
    8*(sourcePair f (shiftedAction f)).re
  nlinarith

/-- All p/q source crosses can enter the same nonnegative bulk, including the original localized cutoff. -/
theorem actual_localized_joint_bulk_nonnegative (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) (a b : ℂ) :
    0 ≤ (sourcePair (SourceScalarVirialIMS.thetaAction m ell (SourceScalarRetardedGram.jointState F z hz g k a b))
      (positiveBulk (SourceScalarVirialIMS.thetaAction m ell (SourceScalarRetardedGram.jointState F z hz g k a b)))).re :=
  original_bulk_nonnegative _

private def volumePotentialAction : End := multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth
private theorem local_affine_split :
    localAction=centeredAction-(2 : ℂ) • vacuumLinearAction+vacuumConstantAction+volumePotentialAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hp := potential_split z
  change potential z+GaussCoframeForm.volumePotential z=
    localPotential z+(scalarSpatial z+magneticPotential z) at hp
  rw [potential_decompose] at hp
  have hc : localPotential z=centeredPotential z-2*vacuumLinear z+vacuumConstant z+GaussCoframeForm.volumePotential z := by
    linarith
  change (localPotential z : ℂ) • f z=(centeredPotential z : ℂ) • f z-
    (2 : ℂ) • ((vacuumLinear z : ℂ) • f z)+(vacuumConstant z : ℂ) • f z+
    (GaussCoframeForm.volumePotential z : ℂ) • f z
  rw [hc]
  push_cast
  simp only [add_smul,sub_smul,mul_smul]

private theorem local_phi_second :
    deltaPhi (deltaPhi localAction)-(3 : ℂ) • deltaPhi localAction+(2 : ℂ) • localAction=
      (2 : ℂ) • vacuumConstantAction+(2 : ℂ) • volumePotentialAction := by
  have hv : deltaPhi volumePotentialAction=0 := phi_real _ _ (fun _ _ => rfl)
  rw [local_affine_split]
  simp only [map_add,map_sub,map_smul,centered_phi,vacuum_linear_phi,vacuum_constant_phi,hv,map_zero]
  module

private def coframeLocalJet : End :=
  SourceHamiltonianScaleJet.scaleDerivative (SourceHamiltonianScaleJet.scaleDerivative
    (SourceHamiltonianScaleJet.scaleDerivative diagonalAction))+
  (3 : ℂ) • SourceHamiltonianScaleJet.scaleDerivative (SourceHamiltonianScaleJet.scaleDerivative diagonalAction)-
  SourceHamiltonianScaleJet.scaleDerivative diagonalAction-(3 : ℂ) • diagonalAction

def vacuumJet : End :=
  deltaPhi (deltaPhi coframeLocalJet)-(3 : ℂ) • deltaPhi coframeLocalJet+(2 : ℂ) • coframeLocalJet

def vacuumJetCoefficient : ℝ := ‖vacuum‖^2/(48*(‖vacuum‖^2+3))

/-- The original (coframe3, affine2) source jet generates the entire constant vacuum/volume term. -/
theorem original_vacuum_jet :
    vacuumJet=(96*(sourceTime 0 : ℂ)*((‖vacuum‖^2+3 : ℝ) : ℂ)) • volumeAction := by
  have hc : coframeLocalJet=(48 : ℂ) • localAction := SourceHamiltonianScaleJet.source_local_from_scale_jet
  have h := congrArg (fun A : End => (48 : ℂ) • A) local_phi_second
  have he : vacuumJet=(96 : ℂ) • vacuumConstantAction+(96 : ℂ) • volumePotentialAction := by
    simp only [vacuumJet,hc,map_smul]
    linear_combination (norm := module) h
  rw [he]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (96 : ℂ) • ((vacuumConstant z : ℂ) • f z)+
    (96 : ℂ) • ((GaussCoframeForm.volumePotential z : ℂ) • f z)=
    (96*(sourceTime 0 : ℂ)*((‖vacuum‖^2+3 : ℝ) : ℂ)) • ((volume z : ℂ) • f z)
  rw [smul_smul,smul_smul,smul_smul,←add_smul]
  apply congrArg (fun r : ℂ => r • f z)
  unfold vacuumConstant GaussCoframeForm.volumePotential
  push_cast
  ring

/-- Vacuum compensation is paid by the same source H0 jets, not an extra state-moment budget. -/
theorem original_vacuum_compensation :
    (vacuumJetCoefficient : ℂ) • vacuumJet=(2 : ℂ) • vacuumConstantAction := by
  rw [original_vacuum_jet,smul_smul]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((vacuumJetCoefficient : ℂ)*(96*(sourceTime 0 : ℂ)*((‖vacuum‖^2+3 : ℝ) : ℂ))) •
      ((volume z : ℂ) • f z)=(2 : ℂ) • ((vacuumConstant z : ℂ) • f z)
  rw [smul_smul,smul_smul]
  apply congrArg (fun r : ℂ => r • f z)
  have hn : (‖vacuum‖^2+3 : ℝ)≠0 := ne_of_gt (by positivity)
  have he : vacuumJetCoefficient*(96*sourceTime 0*(‖vacuum‖^2+3))*volume z=2*vacuumConstant z := by
    unfold vacuumJetCoefficient vacuumConstant
    field_simp [hn]
    ring
  exact_mod_cast he

/-- The positive bulk is wholly generated from the original Hamiltonian by actual ordered source derivations. -/
theorem original_positive_bulk_source_jet :
    filteredBulk+(vacuumJetCoefficient : ℂ) • vacuumJet=positiveBulk := by
  rw [original_vacuum_compensation]
  rfl

end LowEnergy.SourceScalarVirialBulk
