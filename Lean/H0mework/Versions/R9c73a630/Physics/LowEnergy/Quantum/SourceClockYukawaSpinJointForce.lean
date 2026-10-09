import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaSpinClosure
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialMixedClock
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeAbsorption

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaSpinJointForce
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceInverseNeutralScalarCurrent
open SourceInverseMagneticForceCancellation SourceInverseCoframeNeutralSplice
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolumeCurrent GaussYukawaCoefficient
open SaturationMonoid.PhysicsCore DiracExteriorMatterAction DiracCliffordRepresentation
open SU7ExteriorBreakingYukawa StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
open SourceInverseHamiltonianForceReduction SourceScalarPairedTransport SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceScalarForceBudget SourceJointScaleBudget
open scoped ContDiff InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.InternalIndex := Classical.decEq _
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber
open SourceInverseNeutralSpinCurrent SourceClockYukawaSpinRelativeForm SourcePhysicalKineticSquare SourceClockReflectedForm
attribute [local irreducible] SourceMixedNativeReturn.fullAction


open SourceClockYukawaSpinClosure
abbrev Column := Fin 8 → QuantumTest
private abbrev boost (j : Fin 3) : Fin 4 := ⟨j.val,by omega⟩
private abbrev S (j : Fin 4) : Matrix Mode Mode ℂ := GaussCoframeSpin.full (activeIndex j)

private theorem lift_mul (A B : DiracMatrix) : GaussCoframeSpin.spinLift (A*B)=
    GaussCoframeSpin.spinLift A*GaussCoframeSpin.spinLift B := by
  have hm : diracMatrixMatterAction (A*B)=diracMatrixMatterAction A*diracMatrixMatterAction B := by
    apply LinearMap.ext
    intro f
    exact (diracMatrixMatterAction_apply_apply A B f).symm
  have h := congrArg LowEnergy.Quantum.operatorMatrix hm
  have he (X : DiracMatrix) : LowEnergy.Quantum.operatorMatrix (diracMatrixMatterAction X)=GaussCoframeSpin.spinLift X :=
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


private def C (j : Fin 4) : Matrix (Fin 8) (Fin 8) ℂ := closureMatrix j

private def rotationMatrix (j : Fin 3) : Matrix (Fin 8) (Fin 8) ℂ :=
  Complex.I • (C (boost (rotB j))*C (boost (rotA j))-
    C (boost (rotA j))*C (boost (rotB j)))

/-- The row convention is fixed by the actual source coefficient equation. -/
def jointMatrix (j : Fin 7) : Matrix (Fin 8) (Fin 8) ℂ :=
  if h : j.val<3 then C ⟨j.val,by omega⟩ else
  if h : j.val<6 then rotationMatrix ⟨j.val-3,by omega⟩ else C 3

private theorem closure_hermitian (j : Fin 4) : (C j).conjTranspose=C j := by
  ext mu nu
  change star (closureMatrix j nu mu)=closureMatrix j mu nu
  rw [original_closure_matrix_symmetric j nu mu]
  unfold closureMatrix
  split_ifs <;> simp

private theorem rotation_hermitian (j : Fin 3) : (rotationMatrix j).conjTranspose=rotationMatrix j := by
  simp only [rotationMatrix,Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,
    closure_hermitian,Complex.star_def,Complex.conj_I,smul_sub]
  module

private theorem joint_hermitian (j : Fin 7) : (jointMatrix j).conjTranspose=jointMatrix j := by
  unfold jointMatrix
  split_ifs
  · exact closure_hermitian _
  · exact rotation_hermitian _
  · exact closure_hermitian _

private theorem ad_sum (J : End) (C : Fin 8 → ℂ) (K : Fin 8 → End) :
    bracket J (∑ mu,C mu • K mu)=∑ mu,C mu • bracket J (K mu) := by
  simp only [bracket,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    ←Finset.sum_sub_distrib,smul_sub]

private theorem ad_jacobi (X Y K : End) : bracket (bracket X Y) K=
    bracket X (bracket Y K)-bracket Y (bracket X K) := by
  unfold bracket
  noncomm_ring

private theorem ad_matrix (X Y : End) (A B : Matrix (Fin 8) (Fin 8) ℂ) (K : Fin 8 → End)
    (hX : ∀ mu,bracket X (K mu)=∑ nu,A mu nu • K nu)
    (hY : ∀ mu,bracket Y (K mu)=∑ nu,B mu nu • K nu) (mu : Fin 8) :
    bracket (bracket X Y) (K mu)=∑ nu,(B*A-A*B) mu nu • K nu := by
  rw [ad_jacobi,hY,hX,ad_sum,ad_sum]
  simp_rw [hX,hY]
  simp only [Finset.smul_sum,smul_smul,Matrix.sub_apply,Matrix.mul_apply,sub_smul,
    Finset.sum_smul,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun nu xi => (B mu nu*A nu xi) • K xi),
    Finset.sum_comm (f := fun nu xi => (A mu nu*B nu xi) • K xi)]

private theorem spatial_closure (j : Fin 3) (sharp : Bool) (mu : Fin 8) :
    bracket (GaussCoframeSpin.current (spatialIndex j)) (spinClosureCoefficient sharp mu)=
      ∑ nu,rotationMatrix j mu nu • spinClosureCoefficient sharp nu := by
  rw [spatial_core]
  have h := ad_matrix (activeSpin (boost (rotA j))) (activeSpin (boost (rotB j)))
    (C (boost (rotA j))) (C (boost (rotB j)))
    (spinClosureCoefficient sharp) (fun nu => original_spin_closure _ sharp nu)
      (fun nu => original_spin_closure _ sharp nu) mu
  have hs (A B : End) : bracket (Complex.I • A) B=Complex.I • bracket A B := by
    simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
  rw [hs,h]
  simp only [rotationMatrix,Matrix.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul]

/-- All seven literal spin rows act on the same eight coefficients. -/
theorem original_joint_spin_closure (j : Fin 7) (sharp : Bool) (mu : Fin 8) :
    bracket (GaussCoframeSpin.current j) (spinClosureCoefficient sharp mu)=
      ∑ nu,jointMatrix j mu nu • spinClosureCoefficient sharp nu := by
  fin_cases j
  · simpa [jointMatrix,C,activeSpin,activeIndex] using original_spin_closure 0 sharp mu
  · simpa [jointMatrix,C,activeSpin,activeIndex] using original_spin_closure 1 sharp mu
  · simpa [jointMatrix,C,activeSpin,activeIndex] using original_spin_closure 2 sharp mu
  · simpa [jointMatrix,spatialIndex] using spatial_closure 0 sharp mu
  · simpa [jointMatrix,spatialIndex] using spatial_closure 1 sharp mu
  · simpa [jointMatrix,spatialIndex] using spatial_closure 2 sharp mu
  · simpa [jointMatrix,C,activeSpin,activeIndex] using original_spin_closure 3 sharp mu

private def volumeCore : End := multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth

def jointRow (mu nu : Fin 8) : End := ∑ j : Fin 7,(GaussCoframeForm.spinWeight j:ℂ) •
  ((2*jointMatrix j mu nu) • (volumeCore*GaussCoframeSpin.current j)-
    (jointMatrix j*jointMatrix j) mu nu • volumeCore)

def jointSpin (q : Column) (mu : Fin 8) : QuantumTest := ∑ nu,jointRow mu nu (q nu)

private theorem volume_current (j : Fin 7) : Commute volumeCore (GaussCoframeSpin.current j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (GaussCoframeForm.inverseVolume z:ℂ) • quantized (GaussCoframeSpin.full j) (f z)=
    quantized (GaussCoframeSpin.full j) ((GaussCoframeForm.inverseVolume z:ℂ) • f z)
  exact (map_smul _ _ _).symm

private theorem volume_pair (p q : QuantumTest) : sourcePair p (volumeCore q)=sourcePair (volumeCore p) q :=
  multiply_pair _ _ _ _

private theorem current_volume_pair (j : Fin 7) (p q : QuantumTest) :
    sourcePair p ((volumeCore*GaussCoframeSpin.current j) q)=
      sourcePair ((volumeCore*GaussCoframeSpin.current j) p) q := by
  change sourcePair p (volumeCore (GaussCoframeSpin.current j q))=_
  rw [volume_pair,GaussCoframeSpin.current_pair]
  exact congrArg (fun f => sourcePair f q) (LinearMap.congr_fun (volume_current j).eq p).symm

private theorem row_pair (mu nu : Fin 8) (p q : QuantumTest) :
    sourcePair p (jointRow mu nu q)=sourcePair (jointRow nu mu p) q := by
  have hD (j : Fin 7) : (starRingEnd ℂ) (jointMatrix j nu mu)=jointMatrix j mu nu := by
    exact congrArg (fun A : Matrix (Fin 8) (Fin 8) ℂ => A mu nu) (joint_hermitian j)
  have hD2 (j : Fin 7) : (starRingEnd ℂ) ((jointMatrix j*jointMatrix j) nu mu)=(jointMatrix j*jointMatrix j) mu nu := by
    have he : (jointMatrix j*jointMatrix j).conjTranspose=jointMatrix j*jointMatrix j := by
      rw [Matrix.conjTranspose_mul,joint_hermitian]
    exact congrArg (fun A : Matrix (Fin 8) (Fin 8) ℂ => A mu nu) he
  simp only [jointRow,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.sub_apply,sourcePair,map_sum,
    map_smul,map_sub,inner_sum,sum_inner,inner_smul_right,inner_smul_left,inner_sub_right,inner_sub_left,
    map_mul,map_ofNat,Complex.conj_ofReal,hD,hD2]
  apply Finset.sum_congr rfl
  intro j _
  change _*(2*jointMatrix j mu nu*sourcePair p ((volumeCore*GaussCoframeSpin.current j) q)-
      (jointMatrix j*jointMatrix j) mu nu*sourcePair p (volumeCore q))=
    _*(2*jointMatrix j mu nu*sourcePair ((volumeCore*GaussCoframeSpin.current j) p) q-
      (jointMatrix j*jointMatrix j) mu nu*sourcePair (volumeCore p) q)
  rw [current_volume_pair,volume_pair]

private theorem joint_pair (p q : Column) :
    (∑ mu,sourcePair (p mu) (jointSpin q mu))=∑ mu,sourcePair (jointSpin p mu) (q mu) := by
  simp only [jointSpin,sourcePair,map_sum,inner_sum,sum_inner]
  change (∑ mu,∑ nu,sourcePair (p mu) (jointRow mu nu (q nu)))=
    ∑ mu,∑ nu,sourcePair (jointRow mu nu (p nu)) (q mu)
  simp_rw [row_pair]
  exact Finset.sum_comm

/-- Signed boosts, rotations and the axial row have a real complete joint expectation. -/
theorem original_joint_spin_imaginary_zero (q : Column) :
    (∑ mu,sourcePair (q mu) (jointSpin q mu)).im=0 := by
  have h := congrArg Complex.im (joint_pair q q)
  simp only [Complex.im_sum] at h
  have hc (mu : Fin 8) := congrArg Complex.im (GaussNativeForm.pair_conjugate (q mu) (jointSpin q mu))
  simp only [Complex.conj_im] at hc
  have hs := congrArg (fun x : Fin 8 → ℝ => ∑ mu,x mu) (funext hc)
  simp only [Finset.sum_neg_distrib] at hs
  simp only [Complex.im_sum]
  linarith only [h,hs]

private theorem full_at (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    fullAction sharp f z=branchMap sharp (scalarField z) (f z) := by
  unfold SourceMixedNativeReturn.fullAction
  cases sharp <;> rfl
private theorem spin_at (j : Fin 4) (f : QuantumTest) (z : SourceCoordinateSlice) : activeSpin j f z=quantized (S j) (f z) := rfl


private theorem coefficient_tuple (sharp : Bool) : spinClosureCoefficient sharp=
    ![fullAction sharp,spinVariation sharp 0,spinVariation sharp 1,spinVariation sharp 2,
      spinVariation sharp 3,bracket (activeSpin 0) (spinVariation sharp 3),
      bracket (activeSpin 1) (spinVariation sharp 3),bracket (activeSpin 2) (spinVariation sharp 3)] := by
  funext mu
  fin_cases mu <;> rfl


private theorem number_spin (j : Fin 7) : Commute GaussCoframeForm.number (GaussCoframeSpin.current j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hn (g : QuantumTest) : GaussCoframeForm.number g z=fiberNumber (g z) := by
    apply PiLp.ext
    intro word
    exact (GaussCoframeForm.number_apply g z word).trans (fiberNumber_apply (g z) word).symm
  change GaussCoframeForm.number (GaussCoframeSpin.current j f) z=GaussCoframeSpin.current j (GaussCoframeForm.number f) z
  have hs (g : QuantumTest) : GaussCoframeSpin.current j g z=quantized (GaussCoframeSpin.full j) (g z) := rfl
  simp only [hn,hs]
  exact congrArg (fun A : FiberEnd => A (f z)) (number_commute (GaussCoframeSpin.full j)).eq
private theorem real_spin (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (j : Fin 4) :
    Commute (multiply c hc) (activeSpin j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change multiply c hc (activeSpin j f) z=activeSpin j (multiply c hc f) z
  rw [multiply_apply,spin_at,spin_at,multiply_apply]
  exact (map_smul (quantized (S j)) _ _).symm
private theorem real_full (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (fullAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change multiply c hc (fullAction sharp f) z=fullAction sharp (multiply c hc f) z
  rw [multiply_apply,full_at,full_at,multiply_apply]
  exact (map_smul (branchMap sharp (scalarField z)) _ _).symm
private theorem coefficient_commute {A : End} (sharp : Bool)
    (hJ : ∀ j : Fin 4,Commute A (activeSpin j)) (hY : Commute A (fullAction sharp)) (mu : Fin 8) :
    Commute A (spinClosureCoefficient sharp mu) := by
  have hK (j : Fin 4) : Commute A (spinVariation sharp j) := by
    unfold spinVariation
    exact ((hJ j).mul_right hY).sub_right (hY.mul_right (hJ j))
  have hD (j : Fin 3) : Commute A (bracket (activeSpin (boost j)) (spinVariation sharp 3)) :=
    ((hJ (boost j)).mul_right (hK 3)).sub_right ((hK 3).mul_right (hJ (boost j)))
  rw [coefficient_tuple]
  fin_cases mu
  · exact hY
  · exact hK 0
  · exact hK 1
  · exact hK 2
  · exact hK 3
  · exact hD 0
  · exact hD 1
  · exact hD 2

private theorem coefficient_real (sharp : Bool) (mu : Fin 8)
    (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (multiply c hc) (spinClosureCoefficient sharp mu) :=
  coefficient_commute sharp (real_spin c hc) (real_full c hc sharp) mu

private theorem coefficient_number (sharp : Bool) (mu : Fin 8) :
    Commute GaussCoframeForm.number (spinClosureCoefficient sharp mu) := by
  have hJ (j : Fin 4) : Commute GaussCoframeForm.number (activeSpin j) := number_spin (activeIndex j)
  exact coefficient_commute sharp hJ (original_number_full sharp) mu

private theorem coefficient_number_shift (sharp : Bool) (mu : Fin 8) :
    Commute GaussCoframeForm.numberShift (spinClosureCoefficient sharp mu) := by
  unfold GaussCoframeForm.numberShift
  simp only [←Module.End.mul_eq_comp]
  have hN := coefficient_number sharp mu
  have hC := coefficient_real sharp mu GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth
  exact ((hN.mul_left hC).add_left (hC.mul_left hN)).smul_left (1/2:ℂ)

private theorem square_closure (j : Fin 7) (sharp : Bool) (mu : Fin 8) :
    bracket (GaussCoframeSpin.current j*GaussCoframeSpin.current j) (spinClosureCoefficient sharp mu)=
      ∑ nu,((2*jointMatrix j mu nu) • (GaussCoframeSpin.current j*spinClosureCoefficient sharp nu)-
        (jointMatrix j*jointMatrix j) mu nu • spinClosureCoefficient sharp nu) := by
  let J := GaussCoframeSpin.current j
  let K := spinClosureCoefficient sharp
  have h : bracket (J*J) (K mu)=2 • (J*bracket J (K mu))-bracket J (bracket J (K mu)) := by
    unfold bracket
    noncomm_ring
  rw [h]
  change 2 • (GaussCoframeSpin.current j*bracket (GaussCoframeSpin.current j) (spinClosureCoefficient sharp mu))-
    bracket (GaussCoframeSpin.current j) (bracket (GaussCoframeSpin.current j) (spinClosureCoefficient sharp mu))=_
  rw [original_joint_spin_closure j sharp mu]
  rw [ad_sum (GaussCoframeSpin.current j) (fun nu => jointMatrix j mu nu) (spinClosureCoefficient sharp)]
  simp_rw [original_joint_spin_closure j sharp]
  simp only [Finset.mul_sum,mul_smul_comm,Finset.smul_sum,smul_smul,Matrix.mul_apply,Finset.sum_smul,
    Finset.sum_sub_distrib]
  have h2 (c : ℂ) (A : End) : (2:ℕ) • (c • A)=(2*c) • A := by module
  simp_rw [h2]
  rw [Finset.sum_comm (f := fun nu xi =>
    (jointMatrix j mu nu*jointMatrix j nu xi) • spinClosureCoefficient sharp xi)]

private theorem spin_square_closure (j : Fin 7) (sharp : Bool) (mu : Fin 8) :
    bracket (GaussCoframeForm.spinSquare j) (spinClosureCoefficient sharp mu)=
      ∑ nu,(GaussCoframeForm.spinWeight j:ℂ) •
        ((2*jointMatrix j mu nu) • (volumeCore*GaussCoframeSpin.current j)-
          (jointMatrix j*jointMatrix j) mu nu • volumeCore)*spinClosureCoefficient sharp nu := by
  have hV := (coefficient_real sharp mu GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth).eq
  change volumeCore*spinClosureCoefficient sharp mu=spinClosureCoefficient sharp mu*volumeCore at hV
  have hJ := (volume_current j).eq
  have hs : GaussCoframeForm.spinSquare j=(GaussCoframeForm.spinWeight j:ℂ) •
      (volumeCore*(GaussCoframeSpin.current j*GaussCoframeSpin.current j)) := by
    unfold GaussCoframeForm.spinSquare
    simp only [←Module.End.mul_eq_comp]
    change (GaussCoframeForm.spinWeight j:ℂ) •
      (GaussCoframeSpin.current j*(volumeCore*GaussCoframeSpin.current j))=_
    linear_combination (norm := noncomm_ring) (GaussCoframeForm.spinWeight j:ℂ) •
      (-hJ*GaussCoframeSpin.current j)
  rw [hs]
  have hp : bracket (volumeCore*(GaussCoframeSpin.current j*GaussCoframeSpin.current j))
      (spinClosureCoefficient sharp mu)=volumeCore*
        bracket (GaussCoframeSpin.current j*GaussCoframeSpin.current j) (spinClosureCoefficient sharp mu) := by
    unfold bracket
    linear_combination (norm := noncomm_ring) hV*(GaussCoframeSpin.current j*GaussCoframeSpin.current j)
  have hc (a : ℂ) (A B : End) : bracket (a • A) B=a • bracket A B := by
    simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
  rw [hc,hp,square_closure]
  simp only [Finset.mul_sum,Finset.smul_sum,mul_sub,mul_smul_comm,smul_sub,sub_mul,smul_mul_assoc,mul_assoc]

/-- The complete original spin force is the Hermitian eight-component operator on the original coefficients. -/
theorem original_joint_spin_source (sharp : Bool) (u : QuantumTest) (mu : Fin 8) :
    bracket spinPotential (spinClosureCoefficient sharp mu) u=
      jointSpin (fun nu => spinClosureCoefficient sharp nu u) mu := by
  have hN : bracket GaussCoframeForm.numberShift (spinClosureCoefficient sharp mu)=0 := by
    unfold bracket
    exact sub_eq_zero.mpr (coefficient_number_shift sharp mu).eq
  have he : bracket spinPotential (spinClosureCoefficient sharp mu)=
      ∑ j : Fin 7,bracket (GaussCoframeForm.spinSquare j) (spinClosureCoefficient sharp mu) := by
    have hadd (A B K : End) : bracket (A+B) K=bracket A K+bracket B K := by
      unfold bracket
      noncomm_ring
    have hsum (A : Fin 7 → End) (K : End) : bracket (∑ j,A j) K=∑ j,bracket (A j) K := by
      simp only [bracket,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
    rw [spinPotential,hadd,hsum,hN,add_zero]
  rw [he]
  simp_rw [spin_square_closure]
  simp only [LinearMap.sum_apply,Module.End.mul_apply,jointSpin,jointRow]
  exact Finset.sum_comm

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem source_volume : volumeCore=(sourceTime 0:ℂ) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (GaussCoframeForm.inverseVolume z:ℂ) • f z=
    (sourceTime 0:ℂ) • ((reciprocalVolume z:ℂ) • f z)
  simp only [GaussCoframeForm.inverseVolume,reciprocalVolume,Complex.ofReal_mul,
    Complex.ofReal_inv,div_eq_mul_inv,smul_smul]

private theorem current_norm (j : Fin 7) (f : QuantumTest) :
    ‖embed (GaussCoframeSpin.current j f)‖ ≤ ‖quantized (GaussCoframeSpin.full j)‖*‖embed f‖ :=
  GaussBoundedMultiplier.action_bound (fun _ => quantized (GaussCoframeSpin.full j))
    (fun _ => contDiffAt_const) (fun _ w => weight_commute w _)
      ‖quantized (GaussCoframeSpin.full j)‖ (norm_nonneg _) (fun _ v => ContinuousLinearMap.le_opNorm _ v) f

private def rowPrice (mu nu : Fin 8) : ℝ := ∑ j : Fin 7,|GaussCoframeForm.spinWeight j| *
  (2*‖jointMatrix j mu nu‖*‖quantized (GaussCoframeSpin.full j)‖+
    ‖(jointMatrix j*jointMatrix j) mu nu‖)

private theorem row_price_nonneg (mu nu : Fin 8) : 0 ≤ rowPrice mu nu := by
  unfold rowPrice
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _)
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)))

private theorem row_pair_price (mu nu : Fin 8) (p q : QuantumTest) :
    ‖sourcePair p (jointRow mu nu q)‖ ≤
      sourceTime 0*rowPrice mu nu*‖embed (inverseVolumeAction p)‖*‖embed q‖ := by
  have hv : sourcePair p (inverseVolumeAction q)=sourcePair (inverseVolumeAction p) q := multiply_pair _ _ _ _
  have hJ (j : Fin 7) : sourcePair p ((volumeCore*GaussCoframeSpin.current j) q)=
      (sourceTime 0:ℂ)*sourcePair (GaussCoframeSpin.current j (inverseVolumeAction p)) q := by
    rw [source_volume]
    simp only [smul_mul_assoc,LinearMap.smul_apply,Module.End.mul_apply]
    have hU : sourcePair p (inverseVolumeAction (GaussCoframeSpin.current j q))=
      sourcePair (inverseVolumeAction p) (GaussCoframeSpin.current j q) := multiply_pair _ _ _ _
    simp only [sourcePair,map_smul,inner_smul_right]
    change (sourceTime 0:ℂ)*sourcePair p (inverseVolumeAction (GaussCoframeSpin.current j q))=_
    rw [hU,GaussCoframeSpin.current_pair]
    rfl
  have hV : sourcePair p (volumeCore q)=(sourceTime 0:ℂ)*sourcePair (inverseVolumeAction p) q := by
    rw [source_volume]
    simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right]
    exact congrArg ((sourceTime 0:ℂ)*·) hv
  have he : sourcePair p (jointRow mu nu q)=∑ j : Fin 7,(GaussCoframeForm.spinWeight j:ℂ)*
      ((2*jointMatrix j mu nu)*sourcePair p ((volumeCore*GaussCoframeSpin.current j) q)-
        (jointMatrix j*jointMatrix j) mu nu*sourcePair p (volumeCore q)) := by
    simp only [jointRow,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.sub_apply,
      sourcePair,map_sum,map_smul,map_sub,inner_sum,inner_smul_right,inner_sub_right]
  rw [he]
  apply (norm_sum_le _ _).trans
  have hn : ‖(sourceTime 0:ℂ)‖=sourceTime 0 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos lapse_pos]
  have hw (j : Fin 7) : ‖(GaussCoframeForm.spinWeight j:ℂ)‖=|GaussCoframeForm.spinWeight j| := by
    rw [Complex.norm_real,Real.norm_eq_abs]
  have hj (j : Fin 7) : ‖sourcePair (GaussCoframeSpin.current j (inverseVolumeAction p)) q‖ ≤
      ‖quantized (GaussCoframeSpin.full j)‖*‖embed (inverseVolumeAction p)‖*‖embed q‖ :=
    (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
      (mul_le_mul_of_nonneg_right (current_norm j _) (norm_nonneg _))
  have hi : ‖sourcePair (inverseVolumeAction p) q‖ ≤ ‖embed (inverseVolumeAction p)‖*‖embed q‖ :=
    norm_inner_le_norm (𝕜 := ℂ) _ _
  calc
    _ ≤ ∑ j : Fin 7,|GaussCoframeForm.spinWeight j| *
      (2*‖jointMatrix j mu nu‖*(sourceTime 0*(‖quantized (GaussCoframeSpin.full j)‖*
        ‖embed (inverseVolumeAction p)‖*‖embed q‖))+
       ‖(jointMatrix j*jointMatrix j) mu nu‖*(sourceTime 0*(‖embed (inverseVolumeAction p)‖*‖embed q‖))) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul,hw]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply (norm_sub_le _ _).trans
        rw [norm_mul,norm_mul,norm_mul,hJ,hV,norm_mul,norm_mul,hn]
        norm_num only [Complex.norm_ofNat]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hj j) lapse_pos.le)
            (mul_nonneg (by norm_num : (0:ℝ)≤2) (norm_nonneg (jointMatrix j mu nu))))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi lapse_pos.le) (norm_nonneg _))
    _ = _ := by simp only [rowPrice,Finset.mul_sum,Finset.sum_mul];apply Finset.sum_congr rfl;intro j _;ring

def jointCoframe (q : Column) : ℝ := ∑ mu,coframeGram (inverseVolumeAction (q mu))
def columnNorm (q : Column) : ℝ := ∑ mu,‖embed (q mu)‖^2
def jointPrice : ℝ := (∑ mu : Fin 8,∑ nu : Fin 8,(rowPrice mu nu)^2)/100

def coherentColumn (sharp : Bool) (u : QuantumTest) (e : Column) : Column :=
  fun mu => spinClosureCoefficient sharp mu u-e mu

private theorem joint_add (p q : Column) (mu : Fin 8) :
    jointSpin (fun nu => p nu+q nu) mu=jointSpin p mu+jointSpin q mu := by
  simp only [jointSpin,map_add,Finset.sum_add_distrib]

private theorem coherent_imaginary (sharp : Bool) (u : QuantumTest) (e : Column) :
    (∑ mu,sourcePair (coherentColumn sharp u e mu) (bracket spinPotential (spinClosureCoefficient sharp mu) u)).im=
      (∑ mu,sourcePair (coherentColumn sharp u e mu) (jointSpin e mu)).im := by
  have hv : (fun mu => spinClosureCoefficient sharp mu u)=
      (fun mu => coherentColumn sharp u e mu+e mu) := by funext mu;simp only [coherentColumn,sub_add_cancel]
  simp_rw [original_joint_spin_source]
  rw [hv]
  simp_rw [joint_add]
  simp only [sourcePair,map_add,inner_add_right,Finset.sum_add_distrib,Complex.add_im]
  change (∑ mu,sourcePair (coherentColumn sharp u e mu) (jointSpin (coherentColumn sharp u e) mu)).im+_= _
  rw [original_joint_spin_imaginary_zero,zero_add]

private theorem joint_coframe_nonneg (q : Column) : 0 ≤ jointCoframe q :=
  Finset.sum_nonneg (fun mu _ => (SourceClockSourceTail.original_inverse_coframe_floor (inverseVolumeAction (q mu))).trans'
    (mul_nonneg (by norm_num) (sq_nonneg _)))

/-- The complete signed spin force leaves only the error column, with its source coframe payment. -/
theorem original_joint_spin_pair_price (sharp : Bool) (u : QuantumTest) (e : Column) (δ : ℝ) (hδ : 0<δ) :
    |(∑ mu,sourcePair (coherentColumn sharp u e mu)
      (bracket spinPotential (spinClosureCoefficient sharp mu) u)).im| ≤
      δ*(sourceTime 0)^2*jointCoframe (coherentColumn sharp u e)+jointPrice/δ*columnNorm e := by
  rw [coherent_imaginary]
  let q := coherentColumn sharp u e
  let X : Fin 8 → ℝ := fun mu => ‖embed (inverseVolumeAction (q mu))‖
  let Y : Fin 8 → ℝ := fun nu => ‖embed (e nu)‖
  let K := ∑ mu : Fin 8,∑ nu : Fin 8,(rowPrice mu nu)^2
  have hk : 0 ≤ K := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hx : 0 ≤ ∑ mu,(X mu)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hy : 0 ≤ ∑ nu,(Y nu)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : |(∑ mu,sourcePair (q mu) (jointSpin e mu)).im| ≤
      sourceTime 0*∑ mu,∑ nu,rowPrice mu nu*X mu*Y nu := by
    apply (Complex.abs_im_le_norm _).trans
    apply (norm_sum_le _ _).trans
    simp only [jointSpin,sourcePair,map_sum,inner_sum]
    calc
      _ ≤ ∑ mu,∑ nu,‖sourcePair (q mu) (jointRow mu nu (e nu))‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
      _ ≤ ∑ mu,∑ nu,sourceTime 0*rowPrice mu nu*X mu*Y nu :=
        Finset.sum_le_sum (fun mu _ => Finset.sum_le_sum (fun nu _ => row_pair_price mu nu _ _))
      _ = _ := by simp only [Finset.mul_sum];congr 1;funext mu;congr 1;funext nu;ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun t : Fin 8 × Fin 8 => rowPrice t.1 t.2) (fun t : Fin 8 × Fin 8 => X t.1*Y t.2)
  simp only [Fintype.sum_prod_type,mul_pow] at hc
  have hxy : (∑ mu : Fin 8,∑ nu : Fin 8,(X mu)^2*(Y nu)^2)=(∑ mu,(X mu)^2)*(∑ nu,(Y nu)^2) := by
    calc
      _ = ∑ mu : Fin 8,(X mu)^2*(∑ nu : Fin 8,(Y nu)^2) := by simp only [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  rw [hxy] at hc
  have hm : (∑ mu : Fin 8,∑ nu : Fin 8,rowPrice mu nu*(X mu*Y nu))=
      ∑ mu : Fin 8,∑ nu : Fin 8,rowPrice mu nu*X mu*Y nu := by
    apply Finset.sum_congr rfl
    intro mu _
    apply Finset.sum_congr rfl
    intro nu _
    ring
  rw [hm] at hc
  change _ ≤ K*((∑ mu,(X mu)^2)*∑ nu,(Y nu)^2) at hc
  have hf : 25*(∑ mu,(X mu)^2) ≤ jointCoframe q := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun mu _ => SourceClockSourceTail.original_inverse_coframe_floor (inverseVolumeAction (q mu)))
  have ht := lapse_pos
  have hnn : 0 ≤ sourceTime 0*∑ mu,∑ nu,rowPrice mu nu*X mu*Y nu :=
    mul_nonneg ht.le (Finset.sum_nonneg (fun mu _ => Finset.sum_nonneg (fun nu _ =>
      mul_nonneg (mul_nonneg (row_price_nonneg _ _) (norm_nonneg _)) (norm_nonneg _))))
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hsum 2
  simp only [mul_pow] at hsq
  have hcs := mul_le_mul_of_nonneg_left hc (sq_nonneg (sourceTime 0))
  have hfloor := mul_le_mul_of_nonneg_right hf (mul_nonneg ((mul_nonneg (sq_nonneg (sourceTime 0)) hk)) hy)
  let A := δ*(sourceTime 0)^2*jointCoframe q
  let B := jointPrice/δ*columnNorm e
  have hab : 100*δ*B=K*∑ nu,(Y nu)^2 := by dsimp [B,jointPrice,columnNorm,K,Y];field_simp
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hδ.le (sq_nonneg _)) (joint_coframe_nonneg q)
  have hB : 0 ≤ B := by unfold B jointPrice;exact mul_nonneg (div_nonneg (div_nonneg hk (by norm_num)) hδ.le) hy
  have hb : |(∑ mu,sourcePair (q mu) (jointSpin e mu)).im|^2 ≤
      (sourceTime 0)^2*K*(∑ mu,(X mu)^2)*(∑ nu,(Y nu)^2) := by
    exact (hsq.trans hcs).trans_eq (by ring)
  have h25 := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤25)
  have hpaid : 25*|(∑ mu,sourcePair (q mu) (jointSpin e mu)).im|^2 ≤
      (sourceTime 0)^2*K*jointCoframe q*(∑ nu,(Y nu)^2) := by nlinarith only [h25,hfloor]
  have hprod : 100*A*B=(sourceTime 0)^2*K*jointCoframe q*(∑ nu,(Y nu)^2) := by
    calc
      _ = (sourceTime 0)^2*jointCoframe q*(100*δ*B) := by dsimp [A];ring
      _ = _ := by rw [hab];ring
  change |(∑ mu,sourcePair (q mu) (jointSpin e mu)).im| ≤ A+B
  nlinarith only [hpaid,hprod,hA,hB,sq_nonneg (A-B)]

open SourceClockYukawaCubicCurrent (resolventCore)
open SourceClockYukawaRadialMixedBudget (radiusSource)
open GaussRadialDomain SourceRelativePowerTail SourceResolventBandLimit
open SourceHardyRetardedTail MeasureTheory Filter

def radialMap (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  inverseAction*resolventCore F z hz-resolventCore F z hz*inverseAction

def inputCore (g : diagonal.domain) : QuantumTest := coreEquiv.symm (radiusSource g)

def windowState (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  thetaAction m ell (radialMap F z hz (inputCore g))

def errorColumn (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  radialMap F z hz (thetaAction m ell (spinClosureCoefficient sharp mu (inputCore g)))

def jointState (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column :=
  coherentColumn sharp (windowState m ell F z hz g) (errorColumn sharp m ell F z hz g)

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem theta_inverse (m ell : ℕ) : Commute inverseAction (thetaAction m ell) := by
  unfold thetaAction
  have h : Commute inverseAction (1-inverseAction) :=
    (Commute.one_right inverseAction).sub_right (Commute.refl inverseAction)
  exact (h.pow_right _).sub_right (h.pow_right _)

private theorem error_embed (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (mu : Fin 8) :
    embed (errorColumn sharp m ell F z hz g mu)=
      inverseRadius (finiteResolvent F z (relativeTail m ell (embed (spinClosureCoefficient sharp mu (inputCore g)))))-
      finiteResolvent F z (relativeTail m ell (embed (inverseAction (spinClosureCoefficient sharp mu (inputCore g))))) := by
  have hi := LinearMap.congr_fun (theta_inverse m ell).eq (spinClosureCoefficient sharp mu (inputCore g))
  change inverseAction (thetaAction m ell (spinClosureCoefficient sharp mu (inputCore g)))=
    thetaAction m ell (inverseAction (spinClosureCoefficient sharp mu (inputCore g))) at hi
  simp only [errorColumn,radialMap,LinearMap.sub_apply,Module.End.mul_apply,map_sub,
    ←inverse_core,resolvent_embed,hi,←theta_core]

private theorem line_nonreal (μ : ℝ) (hμ : 0<μ) (w : ℝ) : (line μ w).im≠0 := by
  simpa only [line_im] using hμ.ne'

private theorem error_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (mu : Fin 8) :
    Continuous (fun w : ℝ => embed (errorColumn sharp m ell F (line μ w) (line_nonreal μ hμ w) g mu)) := by
  simp_rw [error_embed]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  exact (inverseRadius.continuous.comp (hr.clm_apply continuous_const)).sub (hr.clm_apply continuous_const)

private theorem error_measurable (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (mu : Fin 8) :
    Measurable (fun w : ℝ => ENNReal.ofReal (‖embed
      (errorColumn sharp m ell F (line μ w) (line_nonreal μ hμ w) g mu)‖^2)) :=
  (error_continuous sharp m ell F μ hμ g mu).norm.pow 2 |>.measurable.ennreal_ofReal

private theorem error_tail (sharp : Bool) (mu : Fin 8) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖embed (errorColumn sharp m ell F (line μ w)
        (line_nonreal μ hμ w) g mu)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let h := embed (spinClosureCoefficient sharp mu (inputCore g))
  let sh := embed (inverseAction (spinClosureCoefficient sharp mu (inputCore g)))
  let P := 2*‖inverseRadius‖^2
  have hP : 0 ≤ P := mul_nonneg (by norm_num) (sq_nonneg _)
  let δ := ε/(P+3)
  have hδ : 0<δ := div_pos hε (by linarith)
  obtain ⟨N1,h1⟩ := fixed_forcing_uniform_energy_tail μ hμ (1:H →L[ℂ] H) h δ hδ
  obtain ⟨N2,h2⟩ := fixed_forcing_uniform_energy_tail μ hμ (1:H →L[ℂ] H) sh δ hδ
  refine ⟨max N1 N2,fun m hm ell hml F => ?_⟩
  let x := fun w : ℝ => finiteResolvent F (line μ w) (relativeTail m ell h)
  let y := fun w : ℝ => finiteResolvent F (line μ w) (relativeTail m ell sh)
  have hx := h1 m (by omega) ell hml F
  have hy := h2 m (by omega) ell hml F
  simp only [one_apply_eq_self] at hx hy
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have mx : Measurable (fun w : ℝ => ENNReal.ofReal (‖x w‖^2)) :=
    (hr.clm_apply continuous_const).norm.pow 2 |>.measurable.ennreal_ofReal
  have mP : Measurable (fun w : ℝ => ENNReal.ofReal P*ENNReal.ofReal (‖x w‖^2)) := measurable_const.mul mx
  have he (w : ℝ) : ‖embed (errorColumn sharp m ell F (line μ w) (line_nonreal μ hμ w) g mu)‖^2 ≤
      P*‖x w‖^2+2*‖y w‖^2 := by
    rw [error_embed]
    change ‖inverseRadius (x w)-y w‖^2 ≤ _
    have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (inverseRadius (x w)) (y w)) 2
    have hs := pow_le_pow_left₀ (norm_nonneg _) (inverseRadius.le_opNorm (x w)) 2
    dsimp [P]
    nlinarith only [ht,hs,sq_nonneg (‖inverseRadius (x w)‖-‖y w‖)]
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal P*ENNReal.ofReal (‖x w‖^2)+
        ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖y w‖^2) := by
      apply lintegral_mono
      intro w
      apply (ENNReal.ofReal_le_ofReal (he w)).trans
      rw [ENNReal.ofReal_add (mul_nonneg hP (sq_nonneg _)) (mul_nonneg (by norm_num) (sq_nonneg _)),
        ENNReal.ofReal_mul (q := ‖x w‖^2) hP,
        ENNReal.ofReal_mul (q := ‖y w‖^2) (by norm_num : (0:ℝ)≤2)]
    _ = ENNReal.ofReal P*(∫⁻ w : ℝ,ENNReal.ofReal (‖x w‖^2))+
        ENNReal.ofReal (2:ℝ)*(∫⁻ w : ℝ,ENNReal.ofReal (‖y w‖^2)) := by
      rw [lintegral_add_left mP,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal P*ENNReal.ofReal δ+ENNReal.ofReal (2:ℝ)*ENNReal.ofReal δ :=
      add_le_add (mul_le_mul le_rfl hx zero_le zero_le) (mul_le_mul le_rfl hy zero_le zero_le)
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
        ←ENNReal.ofReal_add (mul_nonneg hP hδ.le) (mul_nonneg (by norm_num) hδ.le)]
      apply ENNReal.ofReal_le_ofReal
      have hd : δ*(P+3)=ε := by dsimp [δ];field_simp
      nlinarith only [hd,hδ]

/-- All error columns are generated from finitely many fixed source jets before F is chosen. -/
theorem actual_joint_error_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,∀ sharp : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (columnNorm (errorColumn sharp m ell F (line μ w)
        (line_nonreal μ hμ w) g))) ≤ ENNReal.ofReal ε := by
  intro ε hε
  choose Ns hs using (fun t : Bool × Fin 8 => error_tail t.1 t.2 μ hμ g (ε/8) (by positivity))
  refine ⟨Finset.univ.sup Ns,fun m hm ell hml F sharp => ?_⟩
  have he (w : ℝ) : ENNReal.ofReal (columnNorm (errorColumn sharp m ell F (line μ w)
      (line_nonreal μ hμ w) g))=∑ mu : Fin 8,ENNReal.ofReal (‖embed (errorColumn sharp m ell F
        (line μ w) (line_nonreal μ hμ w) g mu)‖^2) :=
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
  simp_rw [he]
  rw [lintegral_finsetSum Finset.univ (fun mu _ => error_measurable sharp m ell F μ hμ g mu)]
  calc
    _ ≤ ∑ mu : Fin 8,ENNReal.ofReal (ε/8) := by
      apply Finset.sum_le_sum
      intro mu _
      exact hs (sharp,mu) m ((Finset.le_sup (f := Ns) (Finset.mem_univ (sharp,mu))).trans hm) ell hml F
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => (div_pos hε (by norm_num)).le)]
      congr 1
      simp
      ring

def cutoffCore (sharp : Bool) (m ell : ℕ) (mu : Fin 8) : End :=
  spinClosureCoefficient sharp mu*thetaAction m ell

def currentCore (sharp : Bool) (m ell : ℕ) (F : Index) (mu : Fin 8) : End :=
  bracket diagonalAction (cutoffCore sharp m ell mu)-bracket (defectAction F) (cutoffCore sharp m ell mu)

def curvatureCore (sharp : Bool) (m ell : ℕ) (F : Index) (mu : Fin 8) : End :=
  bracket GaussRadialHamiltonian.radialAction (cutoffCore sharp m ell mu)-
    bracket (bracket (defectAction F) inverseAction) (cutoffCore sharp m ell mu)

def jointForcing (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  let R := resolventCore F z hz
  let K := SourceRadiusResponseDecay.radialCurrent F
  let J := currentCore sharp m ell F mu
  J (R (K (R (inputCore g))))+K (R (J (R (inputCore g))))-
    curvatureCore sharp m ell F mu (R (inputCore g))

def spinWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  bracket spinPotential (spinClosureCoefficient sharp mu) (windowState m ell F z hz g)

private theorem current_compression (sharp : Bool) (m ell : ℕ) (F : Index) (mu : Fin 8) :
    currentCore sharp m ell F mu=bracket (compressionCore F) (cutoffCore sharp m ell mu) := by
  unfold currentCore defectAction bracket
  noncomm_ring

private theorem curvature_compression (sharp : Bool) (m ell : ℕ) (F : Index) (mu : Fin 8) :
    curvatureCore sharp m ell F mu=bracket (SourceRadiusResponseDecay.radialCurrent F) (cutoffCore sharp m ell mu) := by
  unfold curvatureCore SourceRadiusResponseDecay.radialCurrent bracket
  noncomm_ring

private theorem coefficient_theta (sharp : Bool) (m ell : ℕ) (mu : Fin 8) :
    Commute (thetaAction m ell) (spinClosureCoefficient sharp mu) := by
  have hS : Commute inverseAction (spinClosureCoefficient sharp mu) := by
    simpa only [show inverseAction=multiply reciprocal (fun _ => reciprocal_smooth.contDiffAt) by rfl] using
      coefficient_real sharp mu reciprocal (fun _ => reciprocal_smooth.contDiffAt)
  have hQ := (Commute.one_left (spinClosureCoefficient sharp mu)).sub_left hS
  exact (hQ.pow_left _).sub_left (hQ.pow_left _)

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem core_inverses (F : Index) (z : ℂ) (hz : z.im≠0) :
    (compressionCore F-z • (1:End))*resolventCore F z hz=1 ∧
      resolventCore F z hz*(compressionCore F-z • (1:End))=1 := by
  constructor
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      map_sub,map_smul,compression_embed,resolvent_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self] using h
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      resolvent_embed,map_sub,map_smul,compression_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_left (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul] using h

private theorem inverse_mixed (L R S A : End) (hL : L*R=1) (hR : R*L=1) :
    R*bracket L A*R*bracket L S*R+R*bracket L S*R*bracket L A*R-R*bracket (bracket L S) A*R=
      A*(S*R-R*S)-(S*R-R*S)*A := by
  have hrx (a : End) : R*(L*a)=a := by rw [←mul_assoc,hR,one_mul]
  have hlx (a : End) : L*(R*a)=a := by rw [←mul_assoc,hL,one_mul]
  unfold bracket
  noncomm_ring [hrx,hlx,hL]

attribute [local irreducible] resolventCore compressionCore diagonalAction defectAction inverseAction
  currentCore curvatureCore cutoffCore jointState jointForcing SourceRadiusResponseDecay.radialCurrent

private theorem response_source (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (mu : Fin 8) :
    jointState sharp m ell F z hz g mu=resolventCore F z hz (jointForcing sharp m ell F z hz g mu) := by
  let L : End := compressionCore F-z • 1
  let R : End := resolventCore F z hz
  let A : End := cutoffCore sharp m ell mu
  have hi := core_inverses F z hz
  have hm := inverse_mixed L R inverseAction A hi.1 hi.2
  have hJ : bracket L A=currentCore sharp m ell F mu := by
    rw [current_compression]
    dsimp [L,A]
    simp only [bracket,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
    module
  have hK : bracket L inverseAction=SourceRadiusResponseDecay.radialCurrent F := by
    rw [SourceRadiusResponseDecay.original_radial_current]
    dsimp [L]
    simp only [bracket,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
    module
  rw [hJ,hK,←curvature_compression sharp m ell F mu] at hm
  have ht := LinearMap.congr_fun (coefficient_theta sharp m ell mu).eq (inputCore g)
  simp only [Module.End.mul_apply] at ht
  have hs : jointState sharp m ell F z hz g mu=
      (A*(inverseAction*R-R*inverseAction)-(inverseAction*R-R*inverseAction)*A) (inputCore g) := by
    simp only [jointState,coherentColumn,windowState,errorColumn,radialMap,A,cutoffCore,
      LinearMap.sub_apply,Module.End.mul_apply,ht]
    rfl
  rw [hs,←hm]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,jointForcing,map_add,map_sub]
  rfl

/-- The eight actual coherent states keep the same complete compression defect. -/
theorem actual_joint_source_equation (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (mu : Fin 8) :
    diagonalAction (jointState sharp m ell F z hz g mu)=jointForcing sharp m ell F z hz g mu+
      z • jointState sharp m ell F z hz g mu+defectAction F (jointState sharp m ell F z hz g mu) := by
  have h := LinearMap.congr_fun (core_inverses F z hz).1 (jointForcing sharp m ell F z hz g mu)
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply] at h
  rw [←response_source] at h
  unfold defectAction
  simp only [LinearMap.sub_apply]
  linear_combination (norm := module) h

private theorem cutoff_zero (sharp : Bool) (m ell : ℕ) :
    cutoffCore sharp m ell 0=SourceCutoffDilationWard.literalIncrementAction sharp m ell := by
  rw [SourceMixedNativeReturn.literal_full_return]
  unfold cutoffCore
  rfl

private theorem cutoff_source (sharp : Bool) (m ell : ℕ) :
    bracket diagonalAction (cutoffCore sharp m ell 0)=
      SourceClockYukawaRadialMixedCore.sourceCutoffCurrent sharp m ell := by
  have hp (X Y Z : End) : bracket X (Y*Z)=bracket X Y*Z+Y*bracket X Z := by
    unfold bracket
    noncomm_ring
  have hθ : bracket diagonalAction (thetaAction m ell)=SourceInverseNeutralScalarCurrent.radialCurrent m ell :=
    SourceScalarRadialContact.original_hamiltonian_radial_contact m ell
  rw [cutoff_zero,SourceMixedNativeReturn.literal_full_return,hp,
    SourceClockYukawaHamiltonianCurrent.original_hamiltonian_yukawa_current,hθ]
  have h := PositiveScalarWeakBudget.original_scalar_two_leg_join sharp m ell
  change scalarCurrent sharp*thetaAction m ell+
    fullAction sharp*SourceInverseNeutralScalarCurrent.radialCurrent m ell=
      SourceClockYukawaRadialMixedCore.nativeCutoffCurrent sharp m ell at h
  unfold SourceClockYukawaRadialMixedCore.sourceCutoffCurrent
    SourceClockYukawaHamiltonianCurrent.originalCurrent
  simp only [add_mul]
  linear_combination (norm := module) h

private theorem current_zero (sharp : Bool) (m ell : ℕ) (F : Index) :
    currentCore sharp m ell F 0=SourceClockYukawaRadialMixedCore.correctedCutoffCore sharp m ell F := by
  unfold currentCore SourceClockYukawaRadialMixedCore.correctedCutoffCore
  rw [cutoff_source,cutoff_zero]

private theorem curvature_zero (sharp : Bool) (m ell : ℕ) (F : Index) :
    curvatureCore sharp m ell F 0=SourceClockYukawaRadialMixedCore.correctedJoinedCore sharp m ell F := by
  rw [curvature_compression,cutoff_zero,SourceMixedNativeReturn.literal_full_return,
    SourceClockYukawaRadialJoinedCross.actual_corrected_radial_joined_yukawa_cross]
  rw [SourceClockYukawaRadialMixedCore.correctedJoinedCore,SourceMixedNativeReturn.literal_full_return]

/-- Component zero is the original mixed response at the same source and compression. -/
theorem actual_joint_zero_state (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : jointState sharp m ell F z hz g 0=
      SourceClockYukawaRadialMixedClock.mixedState sharp m ell F z hz g := by
  rw [response_source]
  simp only [jointForcing,current_zero,curvature_zero,inputCore,
    SourceClockYukawaRadialMixedClock.mixedState,SourceClockYukawaRadialMixedCore.sourceMixedResponse,
    LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,map_add,map_sub]

def jointBudget (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal ((sourceTime 0)^2*jointCoframe
    (jointState sharp m ell F (line μ w) (line_nonreal μ hμ w) g))

/-- The fixed-source error pays the full seven-spin joint imaginary forcing at one common cutoff. -/
theorem actual_joint_spin_common_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,∀ sharp : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal |(∑ mu : Fin 8,sourcePair
        (jointState sharp m ell F (line μ w) (line_nonreal μ hμ w) g mu)
        (spinWord sharp m ell F (line μ w) (line_nonreal μ hμ w) g mu)).im|) ≤
          ENNReal.ofReal ε+ENNReal.ofReal η*jointBudget sharp m ell F μ hμ g := by
  intro ε hε
  have hP : 0 ≤ jointPrice/η := div_nonneg
    (div_nonneg (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by norm_num)) hη.le
  let δ := ε/(jointPrice/η+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  obtain ⟨N,hN⟩ := actual_joint_error_common_tail μ hμ g δ hδ
  refine ⟨N,fun m hm ell hml F sharp => ?_⟩
  let e := fun w : ℝ => errorColumn sharp m ell F (line μ w) (line_nonreal μ hμ w) g
  let q := fun w : ℝ => jointState sharp m ell F (line μ w) (line_nonreal μ hμ w) g
  have me : Measurable (fun w : ℝ => ENNReal.ofReal (columnNorm (e w))) := by
    have he : (fun w : ℝ => ENNReal.ofReal (columnNorm (e w)))=
        (fun w => ∑ mu : Fin 8,ENNReal.ofReal (‖embed (e w mu)‖^2)) := by
      funext w
      exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
    rw [he]
    exact Finset.measurable_sum Finset.univ (fun mu _ => error_measurable sharp m ell F μ hμ g mu)
  have mp : Measurable (fun w : ℝ => ENNReal.ofReal (jointPrice/η)*ENNReal.ofReal (columnNorm (e w))) :=
    measurable_const.mul me
  have hb : (∫⁻ w : ℝ,ENNReal.ofReal (columnNorm (e w))) ≤ ENNReal.ofReal δ := hN m hm ell hml F sharp
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal η*ENNReal.ofReal ((sourceTime 0)^2*jointCoframe (q w))+
        ENNReal.ofReal (jointPrice/η)*ENNReal.ofReal (columnNorm (e w)) := by
      apply lintegral_mono
      intro w
      have h := original_joint_spin_pair_price sharp (windowState m ell F (line μ w)
        (line_nonreal μ hμ w) g) (e w) η hη
      have hq : coherentColumn sharp (windowState m ell F (line μ w)
          (line_nonreal μ hμ w) g) (e w)=q w := by unfold q jointState;rfl
      rw [hq] at h
      simp only [spinWord]
      apply (ENNReal.ofReal_le_ofReal h).trans
      change ENNReal.ofReal (η*(sourceTime 0)^2*jointCoframe (q w)+jointPrice/η*columnNorm (e w)) ≤ _
      have he0 : 0 ≤ columnNorm (e w) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      rw [mul_assoc,ENNReal.ofReal_add
        (mul_nonneg hη.le (mul_nonneg (sq_nonneg _) (joint_coframe_nonneg _)))
        (mul_nonneg hP he0),
        ENNReal.ofReal_mul (q := (sourceTime 0)^2*jointCoframe (q w)) hη.le,
        ENNReal.ofReal_mul (q := columnNorm (e w)) hP]
    _ = ENNReal.ofReal η*jointBudget sharp m ell F μ hμ g+
        ENNReal.ofReal (jointPrice/η)*(∫⁻ w : ℝ,ENNReal.ofReal (columnNorm (e w))) := by
      rw [lintegral_add_right _ mp,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ ENNReal.ofReal η*jointBudget sharp m ell F μ hμ g+ENNReal.ofReal ε := by
      apply add_le_add (le_refl _)
      apply (mul_le_mul le_rfl hb zero_le zero_le).trans
      rw [←ENNReal.ofReal_mul hP]
      apply ENNReal.ofReal_le_ofReal
      have hd : δ*(jointPrice/η+1)=ε := div_mul_cancel₀ _ (by linarith)
      nlinarith only [hd,hδ]
    _ = _ := add_comm _ _

end LowEnergy.SourceClockYukawaSpinJointForce
