import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaSpinJointForce
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaSpinNativeAbsorption
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaCoframeRotationRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaJointCoframeForce
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open GaussRadialDomain GaussLiveMomentum SourceScalarPairedTransport
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent
open SourcePhysicalKineticSquare SourceClockReflectedForm SourceClockYukawaSpinClosure SourceClockYukawaSpinJointForce
open SourceClockYukawaSpinRelativeForm SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter SourceRelativePowerTail
open scoped ContDiff InnerProductSpace Matrix Topology
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber
attribute [local irreducible] fullAction jointState jointForcing spinWord

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (SourceMixedNativeReturn.fullAction sharp) := by
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z : ℂ) (f z)).symm

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.fullAction sharp g)=
      sourcePair (SourceMixedNativeReturn.fullAction (!sharp) f) g := by
  unfold SourceMixedNativeReturn.fullAction
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

private theorem full_at (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    SourceMixedNativeReturn.fullAction sharp f z=branchMap sharp (scalarField z) (f z) := by
  unfold SourceMixedNativeReturn.fullAction
  cases sharp <;> rfl


private theorem invariant_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (f h : E → V) (γ : ℝ → E) (z e : E)
    (hg : HasDerivAt γ e 0) (hz : γ 0=z)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (law : ∀ r,h (γ r)=A (f (γ r))) :
    fderiv ℝ h z e=A (fderiv ℝ f z e) := by
  have hf0 := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hg hz.symm
  have hh0 := hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hg hz.symm
  have hp := A.hasFDerivAt.comp_hasDerivAt 0 hf0
  have he : h ∘ γ=A ∘ (f ∘ γ) := funext law
  rw [he] at hh0
  exact hh0.unique hp

private theorem coframe_derivative_full (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let e := GaussCoframeCore.coframeDirection i
  let A := (branchMap sharp (scalarField z)).restrictScalars ℝ
  have hg : HasDerivAt (fun r : ℝ => z+r • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have he := invariant_derivative A f (SourceMixedNativeReturn.fullAction sharp f) (fun r : ℝ => z+r • e) z e hg
    (by simp) ((f.contDiff.differentiable (by simp)) z)
    (((SourceMixedNativeReturn.fullAction sharp f).contDiff.differentiable (by simp)) z) (fun r => by
      rw [full_at]
      simp only [A,e,GaussCoframeCore.coframeDirection,scalarField,Prod.smul_mk,Prod.snd_add,
        smul_zero,add_zero,ContinuousLinearMap.coe_restrictScalars'])
  change GaussCoframeCore.derivative e (SourceMixedNativeReturn.fullAction sharp f) z=
    SourceMixedNativeReturn.fullAction sharp (GaussCoframeCore.derivative e f) z
  rw [GaussCoframeCore.derivative_apply,full_at,GaussCoframeCore.derivative_apply]
  exact he

private theorem coframe_full (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.momentum i) (SourceMixedNativeReturn.fullAction sharp) :=
  (coframe_derivative_full i sharp).smul_left (-Complex.I)

private theorem coframe_full_adjoint (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.adjoint i) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have he := LinearMap.congr_fun (coframe_full i (!sharp)).eq f
  change sourcePair f (GaussCoframeCore.adjoint i (SourceMixedNativeReturn.fullAction sharp g))=
    sourcePair f (SourceMixedNativeReturn.fullAction sharp (GaussCoframeCore.adjoint i g))
  rw [GaussCoframeKinetic.adjoint_pair,full_pair,full_pair,GaussCoframeKinetic.adjoint_pair]
  exact congrArg (fun q => sourcePair q g) he.symm


private theorem coframe_spin (i : Fin 6) (j : Fin 7) :
    Commute (GaussCoframeCore.momentum i) (GaussCoframeSpin.current j) := by
  have hd : Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i))
      (GaussCoframeSpin.current j) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    let e := GaussCoframeCore.coframeDirection i
    let A := (quantized (GaussCoframeSpin.full j)).restrictScalars ℝ
    have hg : HasDerivAt (fun r : ℝ => z+r • e) e 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add z
    have h := invariant_derivative A f (GaussCoframeSpin.current j f) (fun r : ℝ => z+r • e) z e hg
      (by simp) ((f.contDiff.differentiable (by simp)) z)
      (((GaussCoframeSpin.current j f).contDiff.differentiable (by simp)) z) (fun _ => rfl)
    change GaussCoframeCore.derivative e (GaussCoframeSpin.current j f) z=
      GaussCoframeSpin.current j (GaussCoframeCore.derivative e f) z
    simp only [GaussCoframeCore.derivative_apply]
    exact h
  exact hd.smul_left (-Complex.I)

private theorem coframe_spin_adjoint (i : Fin 6) (j : Fin 7) :
    Commute (GaussCoframeCore.adjoint i) (GaussCoframeSpin.current j) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have he := LinearMap.congr_fun (coframe_spin i j).eq f
  change sourcePair f (GaussCoframeCore.adjoint i (GaussCoframeSpin.current j g))=
    sourcePair f (GaussCoframeSpin.current j (GaussCoframeCore.adjoint i g))
  rw [GaussCoframeKinetic.adjoint_pair,GaussCoframeSpin.current_pair,GaussCoframeSpin.current_pair,
    GaussCoframeKinetic.adjoint_pair]
  exact congrArg (fun q => sourcePair q g) he.symm

private theorem closure_commute (sharp : Bool) (A : End)
    (hJ : ∀ j : Fin 4,Commute A (activeSpin j)) (hY : Commute A (fullAction sharp)) (mu : Fin 8) :
    Commute A (spinClosureCoefficient sharp mu) := by
  have hb (X Y : End) (hx : Commute A X) (hy : Commute A Y) : Commute A (bracket X Y) :=
    (hx.mul_right hy).sub_right (hy.mul_right hx)
  unfold spinClosureCoefficient spinCoefficient
  split
  · exact hY
  · split
    · exact hb _ _ (hJ _) hY
    · exact hb _ _ (hJ _) (hb _ _ (hJ 3) hY)

private theorem coframe_coefficient (i : Fin 6) (sharp : Bool) (mu : Fin 8) :
    Commute (GaussCoframeCore.momentum i) (spinClosureCoefficient sharp mu) :=
  closure_commute sharp _ (fun j => coframe_spin i (activeIndex j)) (coframe_full i sharp) mu

private theorem coframe_adjoint_coefficient (i : Fin 6) (sharp : Bool) (mu : Fin 8) :
    Commute (GaussCoframeCore.adjoint i) (spinClosureCoefficient sharp mu) :=
  closure_commute sharp _ (fun j => coframe_spin_adjoint i (activeIndex j)) (coframe_full_adjoint i sharp) mu

private theorem real_spin (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (j : Fin 4) : Commute (multiply c hc) (activeSpin j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (quantized (GaussCoframeSpin.full (activeIndex j))) (c z:ℂ) (f z)).symm

private theorem real_coefficient (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (mu : Fin 8) :
    Commute (multiply c hc) (spinClosureCoefficient sharp mu) :=
  closure_commute sharp _ (real_spin c hc) (real_full c hc sharp) mu

private theorem coframe_kinetic_coefficient (sharp : Bool) (mu : Fin 8) :
    Commute GaussCoframeKinetic.kinetic (spinClosureCoefficient sharp mu) := by
  unfold GaussCoframeKinetic.kinetic
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  unfold GaussCoframeKinetic.term
  exact (coframe_adjoint_coefficient i sharp mu).mul_left
    ((real_coefficient _ _ sharp mu).mul_left (coframe_coefficient j sharp mu))

abbrev rotationIndex (b : Fin 3) : Fin 7 := ⟨3+b.val,by omega⟩
abbrev coframeMatrix (b : Fin 3) : Matrix (Fin 8) (Fin 8) ℂ := jointMatrix (rotationIndex b)
private def C (j : Fin 4) : Matrix (Fin 8) (Fin 8) ℂ := closureMatrix j
private def cycleA : Fin 3 → Fin 4 := ![1,2,0]
private def cycleB : Fin 3 → Fin 4 := ![2,0,1]

private theorem coframe_matrix_source (b : Fin 3) : coframeMatrix b=
    Complex.I • (C (cycleB b)*C (cycleA b)-C (cycleA b)*C (cycleB b)) := by
  fin_cases b <;> rfl

private theorem C_hermitian (j : Fin 4) : (C j).conjTranspose=C j := by
  ext mu nu
  change star (closureMatrix j nu mu)=closureMatrix j mu nu
  rw [original_closure_matrix_symmetric j nu mu]
  unfold closureMatrix
  split_ifs <;> simp

private theorem coframe_hermitian (b : Fin 3) : (coframeMatrix b).conjTranspose=coframeMatrix b := by
  rw [coframe_matrix_source]
  simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,
    C_hermitian,Complex.star_def,Complex.conj_I,smul_sub]
  module

private theorem coframe_adjoint_entry (b : Fin 3) (mu nu : Fin 8) :
    star (coframeMatrix b nu mu)=coframeMatrix b mu nu :=
  congrArg (fun A : Matrix (Fin 8) (Fin 8) ℂ => A mu nu) (coframe_hermitian b)


open SourceClockYukawaCoframeRotationRows SourceCoframeVolumeCurrent

def coframeRow (mu nu : Fin 8) : End := (sourceTime 0:ℂ) •
  ∑ b : Fin 3,coframeMatrix b mu nu • (inverseVolumeAction*bareRow b)

def jointCoframeOperator (q : Column) (mu : Fin 8) : QuantumTest :=
  ∑ nu : Fin 8,coframeRow mu nu (q nu)

private theorem bare_row_coefficient (b : Fin 3) (sharp : Bool) (mu : Fin 8) :
    Commute (bareRow b) (spinClosureCoefficient sharp mu) := by
  have hM (i : Fin 6) : Commute (coordinateAction i) (spinClosureCoefficient sharp mu) :=
    real_coefficient _ _ sharp mu
  fin_cases b
  · exact ((hM 1).mul_left (coframe_coefficient 3 sharp mu)).add_left
      ((hM 2).mul_left (coframe_coefficient 4 sharp mu))
  · exact ((hM 0).mul_left (coframe_coefficient 3 sharp mu)).neg_left
  · exact (hM 0).mul_left (coframe_coefficient 1 sharp mu)

private theorem inverse_coefficient (sharp : Bool) (mu : Fin 8) :
    Commute inverseVolumeAction (spinClosureCoefficient sharp mu) := real_coefficient _ _ sharp mu

private theorem inverse_pair (p q : QuantumTest) :
    sourcePair p (inverseVolumeAction q)=sourcePair (inverseVolumeAction p) q := by
  unfold inverseVolumeAction
  exact multiply_pair _ _ _ _

private theorem weighted_row_pair (b : Fin 3) (p q : QuantumTest) :
    sourcePair p ((inverseVolumeAction*bareRow b) q)=sourcePair ((inverseVolumeAction*bareRow b) p) q := by
  change sourcePair p (inverseVolumeAction (bareRow b q))=_
  rw [inverse_pair,original_bare_row_pair]
  exact congrArg (fun f => sourcePair f q) (LinearMap.congr_fun (original_bare_row_inverse b).eq p)

private theorem coframe_row_pair (mu nu : Fin 8) (p q : QuantumTest) :
    sourcePair p (coframeRow mu nu q)=sourcePair (coframeRow nu mu p) q := by
  have hD (b : Fin 3) : (starRingEnd ℂ) (coframeMatrix b nu mu)=coframeMatrix b mu nu :=
    coframe_adjoint_entry b mu nu
  simp only [coframeRow,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,
    inner_sum,sum_inner,inner_smul_right,inner_smul_left,Complex.conj_ofReal,hD]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  change coframeMatrix b mu nu*sourcePair p ((inverseVolumeAction*bareRow b) q)=
    coframeMatrix b mu nu*sourcePair ((inverseVolumeAction*bareRow b) p) q
  rw [weighted_row_pair]

private theorem joint_pair (p q : Column) :
    (∑ mu,sourcePair (p mu) (jointCoframeOperator q mu))=
      ∑ mu,sourcePair (jointCoframeOperator p mu) (q mu) := by
  simp only [jointCoframeOperator,sourcePair,map_sum,inner_sum,sum_inner]
  change (∑ mu,∑ nu,sourcePair (p mu) (coframeRow mu nu (q nu)))=
    ∑ mu,∑ nu,sourcePair (coframeRow mu nu (p nu)) (q mu)
  simp_rw [coframe_row_pair]
  exact Finset.sum_comm

/-- The original mixed coframe current is Hermitian on the same eight source coefficients. -/
theorem original_joint_coframe_imaginary_zero (q : Column) :
    (∑ mu,sourcePair (q mu) (jointCoframeOperator q mu)).im=0 := by
  have h := congrArg Complex.im (joint_pair q q)
  simp only [Complex.im_sum] at h
  have hc (mu : Fin 8) := congrArg Complex.im
    (GaussNativeForm.pair_conjugate (q mu) (jointCoframeOperator q mu))
  simp only [Complex.conj_im] at hc
  have hs := congrArg (fun x : Fin 8 → ℝ => ∑ mu,x mu) (funext hc)
  simp only [Finset.sum_neg_distrib] at hs
  simp only [Complex.im_sum]
  linarith only [h,hs]

private theorem bracket_product (X Y A : End) : bracket (X*Y) A=X*bracket Y A+bracket X A*Y := by
  unfold bracket
  noncomm_ring
private theorem bracket_smul (c : ℂ) (X A : End) : bracket (c • X) A=c • bracket X A := by
  simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem bracket_sum {ι : Type*} [Fintype ι] (X : ι → End) (A : End) :
    bracket (∑ i,X i) A=∑ i,bracket (X i) A := by
  simp only [bracket,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
private theorem bracket_commute {X A : End} (h : Commute X A) : bracket X A=0 := sub_eq_zero.mpr h.eq

private theorem current_row_source (sharp : Bool) (mu : Fin 8) (b : Fin 3) :
    bracket (GaussCoframeSpin.current (rotationIndex b)*bareRow b) (spinClosureCoefficient sharp mu)=
      ∑ nu : Fin 8,coframeMatrix b mu nu • (bareRow b*spinClosureCoefficient sharp nu) := by
  rw [bracket_product,bracket_commute (bare_row_coefficient b sharp mu),mul_zero,zero_add,
    original_joint_spin_closure]
  simp only [Finset.sum_mul,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro nu _
  change coframeMatrix b mu nu • (spinClosureCoefficient sharp nu*bareRow b)=_
  rw [(bare_row_coefficient b sharp nu).eq]

/-- The complete four source mixed terms generate the actual eight-component current, with no closure premise. -/
theorem original_joint_coframe_source (sharp : Bool) (u : QuantumTest) (mu : Fin 8) :
    bracket GaussCoframeForm.currentAction (spinClosureCoefficient sharp mu) u=
      jointCoframeOperator (fun nu => spinClosureCoefficient sharp nu u) mu := by
  have hU := inverse_coefficient sharp mu
  rw [original_mixed_current_source,bracket_smul,bracket_product,bracket_commute hU,zero_mul,add_zero,bracket_sum]
  simp_rw [current_row_source]
  simp only [Finset.mul_sum,Finset.smul_sum,mul_smul_comm,LinearMap.smul_apply,LinearMap.sum_apply,
    Module.End.mul_apply,jointCoframeOperator,coframeRow]
  exact Finset.sum_comm

private theorem joint_add (q e : Column) (mu : Fin 8) :
    jointCoframeOperator (q+e) mu=jointCoframeOperator q mu+jointCoframeOperator e mu := by
  simp only [jointCoframeOperator,Pi.add_apply,map_add,Finset.sum_add_distrib]

private theorem coherent_imaginary (sharp : Bool) (u : QuantumTest) (e : Column) :
    (∑ mu,sourcePair (coherentColumn sharp u e mu)
      (bracket GaussCoframeForm.currentAction (spinClosureCoefficient sharp mu) u)).im=
    (∑ mu,sourcePair (coherentColumn sharp u e mu) (jointCoframeOperator e mu)).im := by
  simp_rw [original_joint_coframe_source]
  have he : (fun mu => spinClosureCoefficient sharp mu u)=coherentColumn sharp u e+e := by
    funext mu
    simp only [coherentColumn,Pi.add_apply,sub_add_cancel]
  rw [he]
  simp_rw [joint_add]
  simp only [sourcePair,map_add,inner_add_right,Finset.sum_add_distrib,Complex.add_im]
  change (∑ mu,sourcePair (coherentColumn sharp u e mu) (jointCoframeOperator (coherentColumn sharp u e) mu)).im+_=_
  rw [original_joint_coframe_imaginary_zero,zero_add]


private abbrev Tag := Fin 8×Fin 8×Fin 3
private def matrixPrice : ℝ := ∑ t : Tag,‖coframeMatrix t.2.2 t.1 t.2.1‖^2

def coframePrice : ℝ := matrixPrice*rotationPrice/4

private theorem rotation_price_nonnegative : 0 ≤ rotationPrice := by
  unfold rotationPrice
  exact add_nonneg (by norm_num) (div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by norm_num))
private theorem matrix_price_nonnegative : 0 ≤ matrixPrice := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
private theorem coframe_price_nonnegative : 0 ≤ coframePrice :=
  div_nonneg (mul_nonneg matrix_price_nonnegative rotation_price_nonnegative) (by norm_num)

private theorem row_pair_form (mu nu : Fin 8) (p e : QuantumTest) :
    sourcePair p (coframeRow mu nu e)=(sourceTime 0:ℂ)*∑ b : Fin 3,
      coframeMatrix b mu nu*sourcePair (bareRow b (inverseVolumeAction p)) e := by
  simp only [coframeRow,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,
    inner_smul_right,inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  change coframeMatrix b mu nu*sourcePair p (inverseVolumeAction (bareRow b e))=
    coframeMatrix b mu nu*sourcePair (bareRow b (inverseVolumeAction p)) e
  rw [inverse_pair,original_bare_row_pair]

private theorem joint_pair_form (q e : Column) :
    (∑ mu,sourcePair (q mu) (jointCoframeOperator e mu))=
      (sourceTime 0:ℂ)*∑ t : Tag,coframeMatrix t.2.2 t.1 t.2.1*
        sourcePair (bareRow t.2.2 (inverseVolumeAction (q t.1))) (e t.2.1) := by
  have h (mu : Fin 8) : sourcePair (q mu) (jointCoframeOperator e mu)=
      ∑ nu : Fin 8,sourcePair (q mu) (coframeRow mu nu (e nu)) := by
    simp only [jointCoframeOperator,sourcePair,map_sum,inner_sum]
  simp only [h,row_pair_form,←Finset.mul_sum,Fintype.sum_prod_type]

private def rowEnergy (q : Column) : ℝ :=
  ∑ mu : Fin 8,∑ b : Fin 3,‖embed (bareRow b (inverseVolumeAction (q mu)))‖^2

private theorem row_energy_bound (q : Column) : rowEnergy q≤rotationPrice*jointCoframe q := by
  rw [rowEnergy,jointCoframe,Finset.mul_sum]
  exact Finset.sum_le_sum (fun mu _ => original_bare_row_coframe_price (inverseVolumeAction (q mu)))

private theorem joint_square_price (q e : Column) :
    ‖∑ mu,sourcePair (q mu) (jointCoframeOperator e mu)‖^2 ≤
      (sourceTime 0)^2*matrixPrice*rotationPrice*jointCoframe q*columnNorm e := by
  let X : Fin 8 → Fin 3 → ℝ := fun mu b => ‖embed (bareRow b (inverseVolumeAction (q mu)))‖
  let Y : Fin 8 → ℝ := fun nu => ‖embed (e nu)‖
  let D : Tag → ℝ := fun t => ‖coframeMatrix t.2.2 t.1 t.2.1‖
  have hs : ‖∑ t : Tag,coframeMatrix t.2.2 t.1 t.2.1*
      sourcePair (bareRow t.2.2 (inverseVolumeAction (q t.1))) (e t.2.1)‖ ≤
      ∑ t : Tag,D t*(X t.1 t.2.2*Y t.2.1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro t _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℂ) _ _) (norm_nonneg _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ D
    (fun t : Tag => X t.1 t.2.2*Y t.2.1)
  have hxy : (∑ t : Tag,(X t.1 t.2.2*Y t.2.1)^2)=rowEnergy q*columnNorm e := by
    calc
      _ = ∑ mu : Fin 8,∑ nu : Fin 8,(∑ b : Fin 3,(X mu b)^2)*(Y nu)^2 := by
        simp only [Fintype.sum_prod_type,mul_pow,Finset.sum_mul]
      _ = ∑ mu : Fin 8,(∑ b : Fin 3,(X mu b)^2)*(∑ nu : Fin 8,(Y nu)^2) := by
        simp only [Finset.mul_sum]
      _ = (∑ mu : Fin 8,∑ b : Fin 3,(X mu b)^2)*(∑ nu : Fin 8,(Y nu)^2) := by
        rw [Finset.sum_mul]
      _ = _ := rfl
  rw [hxy] at hc
  have hn : ‖∑ t : Tag,coframeMatrix t.2.2 t.1 t.2.1*
      sourcePair (bareRow t.2.2 (inverseVolumeAction (q t.1))) (e t.2.1)‖^2 ≤
        matrixPrice*(rowEnergy q*columnNorm e) :=
    (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans hc
  rw [joint_pair_form,norm_mul,mul_pow]
  have htime : ‖(sourceTime 0:ℂ)‖^2=(sourceTime 0)^2 := by
    simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [htime]
  have h0 : 0 ≤ columnNorm e := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (row_energy_bound q) h0)
    (mul_nonneg (sq_nonneg (sourceTime 0)) matrix_price_nonnegative)
  calc
    _ ≤ (sourceTime 0)^2*(matrixPrice*(rowEnergy q*columnNorm e)) :=
      mul_le_mul_of_nonneg_left hn (sq_nonneg (sourceTime 0))
    _ = ((sourceTime 0)^2*matrixPrice)*(rowEnergy q*columnNorm e) := by ring
    _ ≤ ((sourceTime 0)^2*matrixPrice)*((rotationPrice*jointCoframe q)*columnNorm e) := hm
    _ = _ := by ring

private theorem joint_coframe_nonnegative (q : Column) : 0 ≤ jointCoframe q :=
  Finset.sum_nonneg (fun mu _ => original_coframe_gram_nonnegative (inverseVolumeAction (q mu)))

private theorem young_square (a p e η : ℝ) (hp : 0 ≤ p) (he : 0 ≤ e) (hη : 0<η)
    (hs : a^2≤p*e) : a≤η*p+e/(4*η) := by
  have hi : 4*(η*p)*(e/(4*η))=p*e := by field_simp [hη.ne']
  have hr : 0 ≤ η*p+e/(4*η) := add_nonneg (mul_nonneg hη.le hp) (div_nonneg he (by positivity))
  nlinarith only [hs,hi,hr,sq_nonneg (η*p-e/(4*η))]

/-- The original three angular rows pay the full mixed current after the joint principal expectation cancels. -/
theorem original_joint_coframe_pair_price (sharp : Bool) (u : QuantumTest) (e : Column) (η : ℝ) (hη : 0<η) :
    |(∑ mu,sourcePair (coherentColumn sharp u e mu)
      (bracket GaussCoframeForm.currentAction (spinClosureCoefficient sharp mu) u)).im| ≤
      η*(sourceTime 0)^2*jointCoframe (coherentColumn sharp u e)+coframePrice/η*columnNorm e := by
  rw [coherent_imaginary]
  let q := coherentColumn sharp u e
  have hp : 0 ≤ (sourceTime 0)^2*jointCoframe q := mul_nonneg (sq_nonneg _) (joint_coframe_nonnegative q)
  have he : 0 ≤ matrixPrice*rotationPrice*columnNorm e :=
    mul_nonneg (mul_nonneg matrix_price_nonnegative rotation_price_nonnegative)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hs := (pow_le_pow_left₀ (abs_nonneg _)
    (Complex.abs_im_le_norm (∑ mu,sourcePair (q mu) (jointCoframeOperator e mu))) 2).trans (joint_square_price q e)
  have hh : |(∑ mu,sourcePair (q mu) (jointCoframeOperator e mu)).im|^2 ≤
      ((sourceTime 0)^2*jointCoframe q)*(matrixPrice*rotationPrice*columnNorm e) := hs.trans_eq (by ring)
  have h := young_square _ _ _ η hp he hη hh
  exact h.trans_eq (by dsimp only [q,coframePrice];ring)

def coframeWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  bracket GaussCoframeForm.currentAction (spinClosureCoefficient sharp mu) (windowState m ell F z hz g)


open SourceClockYukawaCubicCurrent SourceClockYukawaTail

private theorem line_nonreal (μ : ℝ) (hμ : 0<μ) (w : ℝ) : (line μ w).im≠0 := by
  simpa only [line_im] using hμ.ne'

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem error_embed (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (mu : Fin 8) :
    embed (errorColumn sharp m ell F z hz g mu)=
      inverseRadius (finiteResolvent F z (relativeTail m ell (embed (spinClosureCoefficient sharp mu (inputCore g)))))-
      finiteResolvent F z (inverseRadius (relativeTail m ell (embed (spinClosureCoefficient sharp mu (inputCore g))))) := by
  simp only [errorColumn,radialMap,LinearMap.sub_apply,Module.End.mul_apply,map_sub,
    ←inverse_core,resolvent_embed,←SourceMixedNativeReturn.theta_core]

private theorem error_energy_measurable (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) : Measurable (fun w : ℝ => ENNReal.ofReal
      (columnNorm (errorColumn sharp m ell F (line μ w) (line_nonreal μ hμ w) g))) := by
  have hc : Continuous (fun w : ℝ => columnNorm (errorColumn sharp m ell F (line μ w) (line_nonreal μ hμ w) g)) := by
    unfold columnNorm
    apply continuous_finsetSum
    intro mu _
    simp_rw [error_embed]
    have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
    exact (((inverseRadius.continuous.comp (hr.clm_apply continuous_const)).sub
      (hr.clm_apply continuous_const)).norm.pow 2)
  exact hc.measurable.ennreal_ofReal

/-- The same fixed-source error pays the full mixed coframe forcing at one common cutoff. -/
theorem actual_joint_coframe_common_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,∀ sharp : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal |(∑ mu : Fin 8,sourcePair
        (jointState sharp m ell F (line μ w) (line_nonreal μ hμ w) g mu)
        (coframeWord sharp m ell F (line μ w) (line_nonreal μ hμ w) g mu)).im|) ≤
          ENNReal.ofReal ε+ENNReal.ofReal η*jointBudget sharp m ell F μ hμ g := by
  intro ε hε
  have hP : 0 ≤ coframePrice/η := div_nonneg coframe_price_nonnegative hη.le
  let δ := ε/(coframePrice/η+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  obtain ⟨N,hN⟩ := actual_joint_error_common_tail μ hμ g δ hδ
  refine ⟨N,fun m hm ell hml F sharp => ?_⟩
  let e := fun w : ℝ => errorColumn sharp m ell F (line μ w) (line_nonreal μ hμ w) g
  let q := fun w : ℝ => jointState sharp m ell F (line μ w) (line_nonreal μ hμ w) g
  have me : Measurable (fun w : ℝ => ENNReal.ofReal (columnNorm (e w))) :=
    error_energy_measurable sharp m ell F μ hμ g
  have mp : Measurable (fun w : ℝ => ENNReal.ofReal (coframePrice/η)*ENNReal.ofReal (columnNorm (e w))) :=
    measurable_const.mul me
  have hb : (∫⁻ w : ℝ,ENNReal.ofReal (columnNorm (e w))) ≤ ENNReal.ofReal δ := hN m hm ell hml F sharp
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal η*ENNReal.ofReal ((sourceTime 0)^2*jointCoframe (q w))+
        ENNReal.ofReal (coframePrice/η)*ENNReal.ofReal (columnNorm (e w)) := by
      apply lintegral_mono
      intro w
      have h := original_joint_coframe_pair_price sharp (windowState m ell F (line μ w)
        (line_nonreal μ hμ w) g) (e w) η hη
      have hq : coherentColumn sharp (windowState m ell F (line μ w)
          (line_nonreal μ hμ w) g) (e w)=q w := by unfold q jointState;rfl
      rw [hq] at h
      simp only [coframeWord]
      apply (ENNReal.ofReal_le_ofReal h).trans
      change ENNReal.ofReal (η*(sourceTime 0)^2*jointCoframe (q w)+coframePrice/η*columnNorm (e w)) ≤ _
      have he0 : 0 ≤ columnNorm (e w) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      rw [mul_assoc,ENNReal.ofReal_add
        (mul_nonneg hη.le (mul_nonneg (sq_nonneg _) (joint_coframe_nonnegative _)))
        (mul_nonneg hP he0),
        ENNReal.ofReal_mul (q := (sourceTime 0)^2*jointCoframe (q w)) hη.le,
        ENNReal.ofReal_mul (q := columnNorm (e w)) hP]
    _ = ENNReal.ofReal η*jointBudget sharp m ell F μ hμ g+
        ENNReal.ofReal (coframePrice/η)*(∫⁻ w : ℝ,ENNReal.ofReal (columnNorm (e w))) := by
      rw [lintegral_add_right _ mp,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ ENNReal.ofReal η*jointBudget sharp m ell F μ hμ g+ENNReal.ofReal ε := by
      apply add_le_add (le_refl _)
      apply (mul_le_mul le_rfl hb zero_le zero_le).trans
      rw [←ENNReal.ofReal_mul hP]
      apply ENNReal.ofReal_le_ofReal
      have hd : δ*(coframePrice/η+1)=ε := div_mul_cancel₀ _ (by linarith)
      nlinarith only [hd,hδ]
    _ = _ := add_comm _ _


open SourceClockYukawaSpinNativeJet SourceClockYukawaSpinNativeDivergence SourceClockYukawaRadialCoefficient

private theorem gauge_spin (j : Fin 4) : Commute gaugeKinetic (activeSpin j) := by
  unfold gaugeKinetic
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro k _
  unfold sandwich
  exact (original_spin_adjoint_native_commute (activeIndex j) _).symm.mul_left
    ((real_spin _ _ j).mul_left (original_spin_native_commute (activeIndex j) _).symm)

private theorem gauge_coefficient (sharp : Bool) (mu : Fin 8) :
    Commute gaugeKinetic (spinClosureCoefficient sharp mu) :=
  closure_commute sharp _ gauge_spin (SourceScalarGaugeForce.original_electric_full sharp) mu

private theorem current_inverse : Commute GaussCoframeForm.currentAction GaussRadialDomain.inverseAction := by
  unfold GaussCoframeForm.currentAction
  exact (((GaussRadialHamiltonian.coframe_mixed _ _ _ _).add_left
    (GaussRadialHamiltonian.coframe_mixed _ _ _ _)).add_left
      (GaussRadialHamiltonian.coframe_mixed _ _ _ _)).add_left
        (GaussRadialHamiltonian.coframe_mixed _ _ _ _)

private theorem rest_return : diagonalAction-scalarKinetic-spinPotential=
    gaugeKinetic+multiply potential potential_smooth+GaussCoframeKinetic.kinetic+
      GaussCoframeForm.currentAction+multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth+
      GaussMatterCore.matterAction := by
  unfold diagonalAction nativeAction GaussCoframeForm.coframeAction spinPotential
  abel

private theorem rest_inverse : Commute (diagonalAction-scalarKinetic-spinPotential) GaussRadialDomain.inverseAction := by
  rw [rest_return]
  exact ((((GaussRadialHamiltonian.gauge_commutes.add_left (GaussRadialHamiltonian.real_commutes _ _)).add_left
    GaussRadialHamiltonian.coframe_kinetic).add_left current_inverse).add_left
      (GaussRadialHamiltonian.real_commutes _ _)).add_left GaussRadialHamiltonian.matter_commutes

private theorem bracket_add (X Y K : End) : bracket (X+Y) K=bracket X K+bracket Y K := by
  unfold bracket
  noncomm_ring

private theorem rest_coefficient (sharp : Bool) (mu : Fin 8) :
    bracket (diagonalAction-scalarKinetic-spinPotential) (spinClosureCoefficient sharp mu)=
      bracket GaussCoframeForm.currentAction (spinClosureCoefficient sharp mu)+
        bracket GaussMatterCore.matterAction (spinClosureCoefficient sharp mu) := by
  rw [rest_return]
  simp only [bracket_add,bracket_commute (gauge_coefficient sharp mu),
    bracket_commute (real_coefficient _ _ sharp mu),bracket_commute (coframe_kinetic_coefficient sharp mu),
    zero_add,add_zero]

private theorem rest_cutoff (sharp : Bool) (mu : Fin 8) (m ell : ℕ) :
    SourceClockYukawaSpinNativeAbsorption.nonScalarCurrent sharp mu m ell=
      (bracket GaussCoframeForm.currentAction (spinClosureCoefficient sharp mu)+
        bracket GaussMatterCore.matterAction (spinClosureCoefficient sharp mu))*SourceMixedNativeReturn.thetaAction m ell := by
  have ht : Commute (diagonalAction-scalarKinetic-spinPotential) (SourceMixedNativeReturn.thetaAction m ell) :=
    (((Commute.one_right _).sub_right rest_inverse).pow_right _).sub_right
      (((Commute.one_right _).sub_right rest_inverse).pow_right _)
  have hp (X Y K : End) : bracket X (Y*K)=bracket X Y*K+Y*bracket X K := by
    unfold bracket
    noncomm_ring
  unfold SourceClockYukawaSpinNativeAbsorption.nonScalarCurrent cutoffCore
  rw [hp,bracket_commute ht,mul_zero,add_zero,rest_coefficient]

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (SourceScalarPositiveBulkWard.state F z hz g)=finiteResolvent F z (g:H) := by
  unfold SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_embed (F : Index) (q : QuantumTest) :
    embed (SourceScalarPairedTransport.compressionCore F q)=GaussGradedCompression.compression F (embed q) := by
  unfold SourceScalarPairedTransport.compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem radial_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (radialCore F z hz g)=SourceRadiusResponseDecay.response F z (g:H) := by
  rw [radialCore,state_embed]
  change finiteResolvent F z (embed (SourceRadiusResponseDecay.radialCurrent F (SourceScalarPositiveBulkWard.state F z hz g)))=_
  rw [SourceRadiusResponseDecay.original_radial_current]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,compression_embed,←GaussRadialDomain.inverse_core,state_embed]
  simp only [SourceRadiusResponseDecay.response,mul_apply_eq_comp,sub_apply,map_sub]

private theorem radial_map_return (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    radialMap F z hz (inputCore g)=radialCore F z hz (SourceClockYukawaRadialMixedBudget.radiusSource g) := by
  have hg : embed (inputCore g)=(SourceClockYukawaRadialMixedBudget.radiusSource g:H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  apply embed_injective
  rw [radial_embed,SourceRadiusResponseDecay.actual_response_difference F z hz]
  simp only [radialMap,Module.End.mul_apply,LinearMap.sub_apply,map_sub,←GaussRadialDomain.inverse_core,resolvent_embed,hg]

def matterWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  bracket GaussMatterCore.matterAction (spinClosureCoefficient sharp mu) (windowState m ell F z hz g)

def coframeRemainingWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  let h := SourceClockYukawaRadialMixedBudget.radiusSource g
  let rS := radialCore F z hz h
  let rA := SourceClockYukawaSpinNativeBudget.cutoffResponseCore sharp mu m ell F z hz h
  let q := SourceScalarPositiveBulkWard.state F z hz h
  scalarZeroOrderWord sharp mu m ell rS rA q+matterWord sharp m ell F z hz g mu-
    bracket (SourceScalarPairedTransport.defectAction F) (cutoffCore sharp m ell mu) rS-
    bracket (SourceScalarPairedTransport.defectAction F) GaussRadialDomain.inverseAction rA+
    bracket (bracket (SourceScalarPairedTransport.defectAction F) GaussRadialDomain.inverseAction) (cutoffCore sharp m ell mu) q

/-- The actual Gamma remainder exits all coframe, gauge and real-potential departments;
the genuine scalar zero-order, matter and three compression-defect words remain signed. -/
theorem actual_joint_coframe_forcing_source (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) (mu : Fin 8) :
    SourceClockYukawaSpinNativeAbsorption.remainingWord sharp m ell F z hz g mu=
      coframeWord sharp m ell F z hz g mu+coframeRemainingWord sharp m ell F z hz g mu := by
  have he := rest_cutoff sharp mu m ell
  unfold SourceClockYukawaSpinNativeAbsorption.remainingWord
  rw [he]
  simp only [Module.End.mul_apply,LinearMap.add_apply]
  unfold coframeRemainingWord coframeWord matterWord windowState
  rw [radial_map_return]
  unfold SourceClockYukawaSpinNativeAbsorption.inputSource
  have hswap (a b c d e f : QuantumTest) : a+(b+c)-d-e+f=b+(a+c-d-e+f) := by abel
  exact hswap _ _ _ _ _ _

end LowEnergy.SourceClockYukawaJointCoframeForce
