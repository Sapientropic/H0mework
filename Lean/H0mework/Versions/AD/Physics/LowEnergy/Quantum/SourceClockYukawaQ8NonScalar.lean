import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaSpinNativeJet
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaJointCoframeForce

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaQ8NonScalar
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open GaussLiveMomentum GaussMatterCore SourceScalarPairedTransport
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent
open SourcePhysicalKineticSquare SourceClockReflectedForm SourceClockYukawaSpinClosure SourceClockYukawaSpinRelativeForm
open SaturationMonoid.PhysicsCore DiracExteriorMatterAction DiracCliffordRepresentation
open SU7ExteriorBreakingYukawa
open scoped ContDiff InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber
attribute [local irreducible] SourceMixedNativeReturn.fullAction

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

private abbrev boost (j : Fin 3) : Fin 4 := ⟨j.val,by omega⟩
private abbrev S (j : Fin 4) : Matrix Mode Mode ℂ := GaussCoframeSpin.full (activeIndex j)

private theorem coefficient_tuple (sharp : Bool) : spinClosureCoefficient sharp=
    ![fullAction sharp,spinVariation sharp 0,spinVariation sharp 1,spinVariation sharp 2,
      spinVariation sharp 3,bracket (activeSpin 0) (spinVariation sharp 3),
      bracket (activeSpin 1) (spinVariation sharp 3),bracket (activeSpin 2) (spinVariation sharp 3)] := by
  funext mu
  fin_cases mu <;> rfl

private theorem paired_symm {A B : End} (h : GaussCoframeForm.Paired A B) : GaussCoframeForm.Paired B A := by
  intro p q
  have h' := congrArg (starRingEnd ℂ) (h q p)
  simpa only [sourcePair,inner_conj_symm] using h'.symm
private theorem bracket_paired (J A B : End) (hJ : GaussCoframeForm.Paired J J)
    (hA : GaussCoframeForm.Paired A B) : GaussCoframeForm.Paired (bracket J A) (-bracket J B) := by
  intro p q
  calc
    _=sourcePair p (J (A q))-sourcePair p (A (J q)) := by
      simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right]
    _=sourcePair (B (J p)) q-sourcePair (J (B p)) q := by rw [hJ,hA,hA,hJ]
    _=_ := by
      simp only [bracket,LinearMap.neg_apply,LinearMap.sub_apply,Module.End.mul_apply,
        sourcePair,map_neg,map_sub,inner_neg_left,inner_sub_left]
      module

private theorem active_paired (j : Fin 4) : GaussCoframeForm.Paired (activeSpin j) (activeSpin j) := by
  unfold activeSpin
  exact GaussCoframeSpin.current_pair (activeIndex j)
private theorem variation_pair (j : Fin 4) (sharp : Bool) :
    GaussCoframeForm.Paired (spinVariation sharp j) (-spinVariation (!sharp) j) := by
  unfold spinVariation
  exact bracket_paired (activeSpin j) (fullAction sharp) (fullAction (!sharp)) (active_paired j) (fun p q => full_pair sharp p q)
private theorem double_pair (j : Fin 3) (sharp : Bool) :
    GaussCoframeForm.Paired (bracket (activeSpin (boost j)) (spinVariation sharp 3))
      (bracket (activeSpin (boost j)) (spinVariation (!sharp) 3)) := by
  have h := bracket_paired (activeSpin (boost j)) (spinVariation sharp 3) (-spinVariation (!sharp) 3) (active_paired (boost j)) (variation_pair 3 sharp)
  have he : -bracket (activeSpin (boost j)) (-spinVariation (!sharp) 3)=
      bracket (activeSpin (boost j)) (spinVariation (!sharp) 3) := by unfold bracket;noncomm_ring
  rw [he] at h
  exact h

theorem original_spin_coefficient_pair (sharp : Bool) (mu : Fin 8) :
    GaussCoframeForm.Paired (spinClosureCoefficient sharp mu) (daggerCoefficient sharp mu) := by
  unfold daggerCoefficient
  rw [coefficient_tuple,coefficient_tuple]
  fin_cases mu
  · change GaussCoframeForm.Paired (fullAction sharp) ((1:ℂ) • fullAction (!sharp))
    rw [one_smul]
    exact fun p q => full_pair sharp p q
  · change GaussCoframeForm.Paired (spinVariation sharp 0) ((-1:ℂ) • spinVariation (!sharp) 0)
    rw [neg_one_smul]
    exact variation_pair 0 sharp
  · change GaussCoframeForm.Paired (spinVariation sharp 1) ((-1:ℂ) • spinVariation (!sharp) 1)
    rw [neg_one_smul]
    exact variation_pair 1 sharp
  · change GaussCoframeForm.Paired (spinVariation sharp 2) ((-1:ℂ) • spinVariation (!sharp) 2)
    rw [neg_one_smul]
    exact variation_pair 2 sharp
  · change GaussCoframeForm.Paired (spinVariation sharp 3) ((-1:ℂ) • spinVariation (!sharp) 3)
    rw [neg_one_smul]
    exact variation_pair 3 sharp
  · change GaussCoframeForm.Paired (bracket (activeSpin 0) (spinVariation sharp 3))
      ((1:ℂ) • bracket (activeSpin 0) (spinVariation (!sharp) 3))
    rw [one_smul]
    exact double_pair 0 sharp
  · change GaussCoframeForm.Paired (bracket (activeSpin 1) (spinVariation sharp 3))
      ((1:ℂ) • bracket (activeSpin 1) (spinVariation (!sharp) 3))
    rw [one_smul]
    exact double_pair 1 sharp
  · change GaussCoframeForm.Paired (bracket (activeSpin 2) (spinVariation sharp 3))
      ((1:ℂ) • bracket (activeSpin 2) (spinVariation (!sharp) 3))
    rw [one_smul]
    exact double_pair 2 sharp

private def diracMap : DiracMatrix →ₗ[ℂ] Module.End ℂ DiracExteriorMatterCarrier where
  toFun := diracMatrixMatterAction
  map_add' A B := by
    apply LinearMap.ext
    intro f
    funext i
    change (∑ j,(A i j+B i j) • f j)=(∑ j,A i j • f j)+(∑ j,B i j • f j)
    simp only [add_smul,Finset.sum_add_distrib]
  map_smul' c A := by
    apply LinearMap.ext
    intro f
    funext i
    change (∑ j,(c*A i j) • f j)=c • (∑ j,A i j • f j)
    simp only [mul_smul,Finset.smul_sum]

private theorem dirac_map_mul (A B : DiracMatrix) : diracMap (A*B)=diracMap A*diracMap B :=
  diracMatrixMatterAction_mul A B

private theorem lift_mul (A B : DiracMatrix) : GaussCoframeSpin.spinLift (A*B)=
    GaussCoframeSpin.spinLift A*GaussCoframeSpin.spinLift B := by
  have h := congrArg LowEnergy.Quantum.operatorMatrix (dirac_map_mul A B)
  have he (X : DiracMatrix) : LowEnergy.Quantum.operatorMatrix (diracMap X)=GaussCoframeSpin.spinLift X :=
    GaussCoframeSpin.spinLift_source X
  simpa only [map_mul,he] using h


private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    bracket (quantized A) (quantized B)=quantized (bracket A B) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [bracket,quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

set_option backward.isDefEq.respectTransparency false

private theorem boost_bracket {R : Type*} [Ring R] (A B C : R)
    (ha : A*A= -1) (hB : A*B+B*A=0) (hC : A*C+C*A=0) :
    bracket (A*B) (A*C)=B*C-C*B := by
  unfold bracket
  linear_combination (norm := noncomm_ring) A*hB*C-A*hC*B-ha*(B*C-C*B)
private theorem rotation {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (A B C : R) (ha : A*A= -1) (hB : A*B+B*A=0) (hC : A*C+C*A=0) (hBC : B*C+C*B=0) :
    (Complex.I/2:ℂ) • (B*C)=Complex.I • bracket ((1/2:ℂ) • (A*B)) ((1/2:ℂ) • (A*C)) := by
  have hb := boost_bracket A B C ha hB hC
  have hCB : C*B=-(B*C) := by linear_combination (norm := module) hBC
  simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_smul,←smul_sub]
  change _=(Complex.I*((1/2:ℂ)*(1/2:ℂ))) • bracket (A*B) (A*C)
  rw [hb,hCB]
  module
private abbrev spatialIndex (j : Fin 3) : Fin 7 := ⟨j.val+3,by omega⟩
private def rotA (j : Fin 3) : Fin 3 := ![1,2,0] j
private def rotB (j : Fin 3) : Fin 3 := ![2,0,1] j
private theorem source_rotation (j : Fin 3) : GaussCoframeSpin.sourceSpin (spatialIndex j)=
    Complex.I • bracket (GaussCoframeSpin.sourceSpin (activeIndex (boost (rotA j))))
      (GaussCoframeSpin.sourceSpin (activeIndex (boost (rotB j)))) := by
  fin_cases j
  · exact rotation _ _ _ diracGammaZero_sq diracGammaZeroTwo_anticommute diracGammaZeroThree_anticommute diracGammaTwoThree_anticommute
  · exact rotation _ _ _ diracGammaZero_sq diracGammaZeroThree_anticommute diracGammaZeroOne_anticommute
      ((add_comm _ _).trans diracGammaOneThree_anticommute)
  · exact rotation _ _ _ diracGammaZero_sq diracGammaZeroOne_anticommute diracGammaZeroTwo_anticommute diracGammaOneTwo_anticommute
private theorem lift_scalar (A : DiracMatrix) (c : ℂ) : GaussCoframeSpin.spinLift (c • A)=c • GaussCoframeSpin.spinLift A := by
  ext i j
  by_cases h : i.2=j.2 <;> simp [GaussCoframeSpin.spinLift,h]
private theorem lift_sub (A B : DiracMatrix) : GaussCoframeSpin.spinLift (A-B)=GaussCoframeSpin.spinLift A-GaussCoframeSpin.spinLift B := by
  ext i j
  by_cases h : i.2=j.2 <;> simp [GaussCoframeSpin.spinLift,h]
private theorem primal_rotation (j : Fin 3) : GaussCoframeSpin.primal (spatialIndex j)=
    Complex.I • bracket (GaussCoframeSpin.primal (activeIndex (boost (rotA j))))
      (GaussCoframeSpin.primal (activeIndex (boost (rotB j)))) := by
  simp only [GaussCoframeSpin.primal,source_rotation,bracket,lift_scalar,lift_sub,lift_mul]
private theorem conjugate_scalar {ι : Type*} (A : Matrix ι ι ℂ) (c : ℂ) :
    (c • A).map (starRingEnd ℂ)=(starRingEnd ℂ c) • A.map (starRingEnd ℂ) := by
  ext i j
  change (starRingEnd ℂ) (c*A i j)=(starRingEnd ℂ c)*(starRingEnd ℂ (A i j))
  exact map_mul (starRingEnd ℂ) _ _
private theorem conjugate_bracket {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    (bracket A B).map (starRingEnd ℂ)=bracket (A.map (starRingEnd ℂ)) (B.map (starRingEnd ℂ)) := by
  ext i j
  simp only [bracket,Matrix.map_apply,Matrix.sub_apply,map_sub,Matrix.mul_apply,map_sum,map_mul]
private theorem block_bracket {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C D : Matrix ι ι ℂ) :
    bracket (Matrix.fromBlocks A 0 0 C) (Matrix.fromBlocks B 0 0 D)=
      Matrix.fromBlocks (bracket A B) 0 0 (bracket C D) := by
  simp only [bracket,sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add,neg_zero,add_zero,
    Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,zero_add]
private theorem full_rotation (j : Fin 3) : GaussCoframeSpin.full (spatialIndex j)=
    Complex.I • bracket (S (boost (rotA j))) (S (boost (rotB j))) := by
  have ha : (activeIndex (boost (rotA j))).val<3 := by simp [activeIndex,(rotA j).isLt]
  have hb : (activeIndex (boost (rotB j))).val<3 := by simp [activeIndex,(rotB j).isLt]
  have hs : ¬(spatialIndex j).val<3 := by
    change ¬j.val+3<3
    omega
  have hp := primal_rotation j
  have hdual : -(GaussCoframeSpin.primal (spatialIndex j)).map (starRingEnd ℂ)=Complex.I •
      bracket ((GaussCoframeSpin.primal (activeIndex (boost (rotA j)))).map (starRingEnd ℂ))
        ((GaussCoframeSpin.primal (activeIndex (boost (rotB j)))).map (starRingEnd ℂ)) := by
    rw [hp,conjugate_scalar,conjugate_bracket,show starRingEnd ℂ Complex.I= -Complex.I by simp,
      neg_smul,neg_neg]
  simp only [S,GaussCoframeSpin.full,ha,hb,hs,ite_true,ite_false]
  simp only [bracket,sub_eq_add_neg,Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,
    Matrix.fromBlocks_neg,Matrix.fromBlocks_add,neg_zero,zero_add,add_zero]
  rw [Matrix.fromBlocks_smul]
  simp only [smul_zero]
  simp only [bracket,sub_eq_add_neg] at hp hdual
  rw [hdual,hp]

set_option backward.isDefEq.respectTransparency true

private theorem spatial_core (j : Fin 3) : GaussCoframeSpin.current (spatialIndex j)=
    Complex.I • bracket (activeSpin (boost (rotA j))) (activeSpin (boost (rotB j))) := by
  have h : quantized (GaussCoframeSpin.full (spatialIndex j))=
      Complex.I • bracket (quantized (S (boost (rotA j)))) (quantized (S (boost (rotB j)))) := by
    change quantizer (GaussCoframeSpin.full (spatialIndex j))=_
    rw [full_rotation,map_smul]
    change Complex.I • quantized (bracket (S (boost (rotA j))) (S (boost (rotB j))))=_
    rw [←quantized_bracket]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hc (g : QuantumTest) : GaussCoframeSpin.current (spatialIndex j) g z=quantized (GaussCoframeSpin.full (spatialIndex j)) (g z) := rfl
  simp only [LinearMap.smul_apply,bracket,LinearMap.sub_apply,Module.End.mul_apply,hc]
  unfold activeSpin
  change quantized (GaussCoframeSpin.full (spatialIndex j)) (f z)=Complex.I •
    (quantized (S (boost (rotA j))) (quantized (S (boost (rotB j))) (f z))-
      quantized (S (boost (rotB j))) (quantized (S (boost (rotA j))) (f z)))
  simpa only [bracket,smul_apply,sub_apply,mul_apply_eq_comp] using congrArg (fun A : FiberEnd => A (f z)) h
set_option backward.isDefEq.respectTransparency true

private theorem spatial_Q8 (j : Fin 3) (sharp : Bool) : Commute (GaussCoframeSpin.current (spatialIndex j)) (Q8 sharp) := by
  rw [spatial_core]
  have ha := original_Q8_active_commute (boost (rotA j)) sharp
  have hb := original_Q8_active_commute (boost (rotB j)) sharp
  exact ((ha.mul_left hb).sub_left (hb.mul_left ha)).smul_left Complex.I

open SourceClockYukawaSpinNativeJet

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

private theorem square_commute {A : End} (sharp : Bool)
    (hK : ∀ s : Bool,∀ mu : Fin 8,Commute A (spinClosureCoefficient s mu)) :
    Commute A (Q8 sharp) := by
  have hD (mu : Fin 8) : Commute A (daggerCoefficient sharp mu) :=
    (hK (!sharp) mu).smul_right _
  unfold Q8
  apply Commute.sum_right
  intro mu _
  exact ((hD mu).mul_right (hK sharp mu)).add_right ((hK sharp mu).mul_right (hD mu))

private theorem real_Q8 (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (Q8 sharp) := square_commute sharp (real_coefficient c hc)

private theorem coframe_Q8 (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.momentum i) (Q8 sharp) :=
  square_commute sharp (coframe_coefficient i)

private theorem coframe_adjoint_Q8 (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.adjoint i) (Q8 sharp) :=
  square_commute sharp (coframe_adjoint_coefficient i)

private theorem coframe_kinetic_Q8 (sharp : Bool) : Commute GaussCoframeKinetic.kinetic (Q8 sharp) := by
  unfold GaussCoframeKinetic.kinetic
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  unfold GaussCoframeKinetic.term
  exact (coframe_adjoint_Q8 i sharp).mul_left ((real_Q8 _ _ sharp).mul_left (coframe_Q8 j sharp))

private theorem gauge_Q8 (sharp : Bool) : Commute gaugeKinetic (Q8 sharp) :=
  square_commute sharp gauge_coefficient

private theorem all_spin_Q8 (j : Fin 7) (sharp : Bool) : Commute (GaussCoframeSpin.current j) (Q8 sharp) := by
  fin_cases j
  · simpa [activeSpin,activeIndex] using original_Q8_active_commute 0 sharp
  · simpa [activeSpin,activeIndex] using original_Q8_active_commute 1 sharp
  · simpa [activeSpin,activeIndex] using original_Q8_active_commute 2 sharp
  · exact spatial_Q8 0 sharp
  · exact spatial_Q8 1 sharp
  · exact spatial_Q8 2 sharp
  · simpa [activeSpin,activeIndex] using original_Q8_active_commute 3 sharp

private theorem mixed_Q8 (i : Fin 6) (j : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (GaussCoframeForm.mixed i j c hc) (Q8 sharp) := by
  unfold GaussCoframeForm.mixed
  simp only [←Module.End.mul_eq_comp]
  exact (((all_spin_Q8 j sharp).mul_left ((real_Q8 c hc sharp).mul_left (coframe_Q8 i sharp))).add_left
    ((coframe_adjoint_Q8 i sharp).mul_left ((real_Q8 c hc sharp).mul_left (all_spin_Q8 j sharp)))).smul_left _

private theorem current_Q8 (sharp : Bool) : Commute GaussCoframeForm.currentAction (Q8 sharp) := by
  unfold GaussCoframeForm.currentAction
  exact (((mixed_Q8 _ _ _ _ sharp).add_left (mixed_Q8 _ _ _ _ sharp)).add_left
    (mixed_Q8 _ _ _ _ sharp)).add_left (mixed_Q8 _ _ _ _ sharp)

private theorem non_scalar_return : diagonalAction-scalarKinetic-GaussMatterCore.matterAction=
    gaugeKinetic+multiply potential potential_smooth+GaussCoframeKinetic.kinetic+
      GaussCoframeForm.currentAction+spinPotential+
      multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth := by
  unfold diagonalAction nativeAction GaussCoframeForm.coframeAction spinPotential
  abel

/-- The actual gauge, complete coframe, seven signed spin, Number and real potentials exit Q8. -/
theorem original_Q8_non_scalar_commute (sharp : Bool) :
    Commute (diagonalAction-scalarKinetic-GaussMatterCore.matterAction) (Q8 sharp) := by
  rw [non_scalar_return]
  exact (((((gauge_Q8 sharp).add_left (real_Q8 _ _ sharp)).add_left
    (coframe_kinetic_Q8 sharp)).add_left (current_Q8 sharp)).add_left
      (original_Q8_spin_commute sharp)).add_left (real_Q8 _ _ sharp)

/-- The original Hamiltonian square current retains its literal scalar and matter departments. -/
theorem original_Q8_hamiltonian_current (sharp : Bool) :
    bracket diagonalAction (Q8 sharp)=bracket scalarKinetic (Q8 sharp)+
      bracket GaussMatterCore.matterAction (Q8 sharp) := by
  have h := (original_Q8_non_scalar_commute sharp).eq
  unfold bracket
  linear_combination (norm := noncomm_ring) h

end LowEnergy.SourceClockYukawaQ8NonScalar
