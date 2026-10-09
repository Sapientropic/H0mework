import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaSpinJointForce
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialJoinedHessian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaGammaPrincipal
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussQuantumMultiplier GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceInverseNeutralSpinCurrent SourceClockYukawaSpinClosure
open SourceClockYukawaSpinJointForce SourceClockYukawaRadialNativeHessian
open SourceClockYukawaRadialJoinedHessian SourceNativeCoframeCompatibility SourceNativeDensityTrace
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open scoped InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber

private def adMatrix (j : Fin 4) (A : Matrix Mode Mode ℂ) : Matrix Mode Mode ℂ :=
  bracket (GaussCoframeSpin.full (activeIndex j)) A

def coefficientMatrix (sharp : Bool) (mu : Fin 8) (phi : Scalar) : Matrix Mode Mode ℂ :=
  if h0 : mu.val=0 then branchMatrix sharp phi else
  if h1 : mu.val<5 then adMatrix ⟨mu.val-1,by omega⟩ (branchMatrix sharp phi) else
    adMatrix ⟨mu.val-5,by omega⟩ (adMatrix 3 (branchMatrix sharp phi))

def fiberCoefficient (sharp : Bool) (mu : Fin 8) (phi : Scalar) : FiberEnd :=
  quantized (coefficientMatrix sharp mu phi)

/-- The joint two-branch anti-Hermitian part is a single actual CAR matrix current. -/
def principalMatrix (phi psi : Scalar) : Matrix Mode Mode ℂ := ∑ mu : Fin 8,
  (bracket (coefficientMatrix false mu phi).conjTranspose (coefficientMatrix false mu psi)+
    bracket (coefficientMatrix false mu phi) (coefficientMatrix false mu psi).conjTranspose)

private def daggerSign (mu : Fin 8) : ℂ := if 0 < mu.val ∧ mu.val < 5 then -1 else 1

private theorem ad_dagger (j : Fin 4) (A : Matrix Mode Mode ℂ) :
    (adMatrix j A).conjTranspose=-adMatrix j A.conjTranspose := by
  unfold adMatrix bracket
  rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
    GaussCoframeSpin.full_hermitian]
  noncomm_ring

private theorem ad_neg (j : Fin 4) (A : Matrix Mode Mode ℂ) : adMatrix j (-A)=-adMatrix j A := by
  unfold adMatrix bracket
  noncomm_ring

private theorem matrix_dagger (mu : Fin 8) (phi : Scalar) :
    coefficientMatrix true mu phi=daggerSign mu • (coefficientMatrix false mu phi).conjTranspose := by
  unfold coefficientMatrix
  split_ifs with h0 h1
  · have hs : daggerSign mu=1 := by simp [daggerSign,h0]
    rw [hs,one_smul]
    rfl
  · have hp : 0 < mu.val := Nat.pos_of_ne_zero h0
    simp only [daggerSign,hp,h1,and_self,ite_true,neg_one_smul,branchMatrix,
      Bool.false_eq_true,ite_false,ad_dagger,neg_neg]
  · have hs : ¬(0 < mu.val ∧ mu.val < 5) := by omega
    simp only [daggerSign,hs,ite_false,one_smul,branchMatrix,Bool.false_eq_true,
      ite_true,ad_dagger,ad_neg,neg_neg]

private theorem quantized_adjoint (A : Matrix Mode Mode ℂ) :
    (quantized A).adjoint=quantized A.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact SourceQuantumFockGauge.quantizedFiber_adjoint A g f

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    bracket (quantized A) (quantized B)=quantized (bracket A B) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [bracket,quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

private theorem fiber_dagger (mu : Fin 8) (phi : Scalar) :
    fiberCoefficient true mu phi=daggerSign mu • (fiberCoefficient false mu phi).adjoint := by
  unfold fiberCoefficient
  rw [matrix_dagger,quantized_adjoint]
  exact map_smul quantizer _ _

private theorem true_pair (mu : Fin 8) (phi psi : Scalar) (u : FockFiber) :
    inner ℂ (fiberCoefficient true mu phi u) (fiberCoefficient true mu psi u)=
      inner ℂ ((fiberCoefficient false mu phi).adjoint u) ((fiberCoefficient false mu psi).adjoint u) := by
  rw [fiber_dagger,fiber_dagger]
  by_cases h : 0 < mu.val ∧ mu.val < 5
  · have hs : daggerSign mu=-1 := by unfold daggerSign;rw [if_pos h]
    simp only [hs,neg_one_smul,neg_apply,inner_neg_left,inner_neg_right,neg_neg]
  · have hs : daggerSign mu=1 := by unfold daggerSign;rw [if_neg h]
    simp only [hs,one_smul]

private theorem row_pair (A B : FiberEnd) (u : FockFiber) :
    (inner ℂ u ((bracket A.adjoint B+bracket A B.adjoint) u)).im=
      2*(inner ℂ (A u) (B u)+inner ℂ (A.adjoint u) (B.adjoint u)).im := by
  have h1 := ContinuousLinearMap.adjoint_inner_right A u (B u)
  have h2 := ContinuousLinearMap.adjoint_inner_right B.adjoint u (A.adjoint u)
  have h3 := ContinuousLinearMap.adjoint_inner_right A.adjoint u (B.adjoint u)
  have h4 := ContinuousLinearMap.adjoint_inner_right B u (A u)
  simp only [ContinuousLinearMap.adjoint_adjoint] at h2 h3
  change (inner ℂ u ((A.adjoint (B u)-B (A.adjoint u))+
    (A (B.adjoint u)-B.adjoint (A u)))).im=_
  rw [inner_add_right,inner_sub_right,inner_sub_right,h1,h2,h3,h4]
  have hc (p q : FockFiber) : (inner ℂ p q).im=-(inner ℂ q p).im := by
    simpa only [Complex.conj_im] using (congrArg Complex.im (inner_conj_symm p q)).symm
  simp only [Complex.add_im,Complex.sub_im]
  rw [hc (B.adjoint u) (A.adjoint u),hc (B u) (A u)]
  ring

private theorem principal_quantized (phi psi : Scalar) : quantized (principalMatrix phi psi)=
    ∑ mu : Fin 8,(bracket (fiberCoefficient false mu phi).adjoint (fiberCoefficient false mu psi)+
      bracket (fiberCoefficient false mu phi) (fiberCoefficient false mu psi).adjoint) := by
  unfold principalMatrix
  change quantizer (∑ mu : Fin 8,_)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [map_add]
  change quantized (bracket (coefficientMatrix false mu phi).conjTranspose (coefficientMatrix false mu psi))+
    quantized (bracket (coefficientMatrix false mu phi) (coefficientMatrix false mu psi).conjTranspose)=_
  rw [←quantized_bracket,←quantized_bracket,←quantized_adjoint,←quantized_adjoint]
  rfl

/-- Both actual sharp branches cancel their quartic anti-Hermitian part before any positive-part readout. -/
theorem original_gamma_principal_pair (phi psi : Scalar) (u : FockFiber) :
    2*(∑ mu : Fin 8,(inner ℂ (fiberCoefficient false mu phi u) (fiberCoefficient false mu psi u)+
      inner ℂ (fiberCoefficient true mu phi u) (fiberCoefficient true mu psi u))).im=
      (inner ℂ u (quantized (principalMatrix phi psi) u)).im := by
  rw [principal_quantized]
  simp only [sum_apply,inner_sum,Complex.im_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [true_pair]
  exact (row_pair _ _ u).symm

theorem original_gamma_principal_skew (phi psi : Scalar) :
    (principalMatrix phi psi).conjTranspose=-principalMatrix phi psi := by
  simp only [principalMatrix,Matrix.conjTranspose_sum,Matrix.conjTranspose_add,bracket,
    Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
    ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro mu _
  noncomm_ring

private theorem full_at (sharp : Bool) (f : QuantumTest) (x : SourceCoordinateSlice) :
    fullAction sharp f x=quantized (branchMatrix sharp (scalarField x)) (f x) := by
  cases sharp
  · rfl
  · change (quantized (GaussYukawaCoefficient.fullMatrix (scalarField x))).adjoint (f x)=
      quantized (GaussYukawaCoefficient.fullMatrix (scalarField x)).conjTranspose (f x)
    exact congrArg (fun A : FiberEnd => A (f x))
      (quantized_adjoint (GaussYukawaCoefficient.fullMatrix (scalarField x)))

private theorem active_at (j : Fin 4) (f : QuantumTest) (x : SourceCoordinateSlice) :
    activeSpin j f x=quantized (GaussCoframeSpin.full (activeIndex j)) (f x) := rfl

private theorem core_coefficient_at (sharp : Bool) (mu : Fin 8) (f : QuantumTest)
    (x : SourceCoordinateSlice) :
    spinClosureCoefficient sharp mu f x=fiberCoefficient sharp mu (scalarField x) (f x) := by
  unfold spinClosureCoefficient SourceClockYukawaSpinRelativeForm.spinCoefficient fiberCoefficient coefficientMatrix
  split_ifs with h0 h1
  · exact full_at sharp f x
  · simp only [spinVariation,bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,active_at,full_at]
    change (bracket (quantized (GaussCoframeSpin.full (activeIndex ⟨mu.val-1,by omega⟩)))
      (quantized (branchMatrix sharp (scalarField x)))) (f x)=_
    rw [quantized_bracket]
    rfl
  · simp only [spinVariation,bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,active_at,full_at]
    change (bracket (quantized (GaussCoframeSpin.full (activeIndex ⟨mu.val-5,by omega⟩)))
      (bracket (quantized (GaussCoframeSpin.full (activeIndex 3)))
        (quantized (branchMatrix sharp (scalarField x))))) (f x)=_
    rw [quantized_bracket,quantized_bracket]
    rfl

/-- The actual two sharp coherent columns return their gamma main term to the same one-body source;
the gamma-weighted fixed error is kept explicitly. -/
theorem actual_joint_gamma_principal (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (x : physicalChart) :
    (∑ mu : Fin 8,(inner ℂ (jointState false m ell F z hz g mu x.val)
        (fiberCoefficient false mu (gammaGradient x.val) (windowState m ell F z hz g x.val))+
      inner ℂ (jointState true m ell F z hz g mu x.val)
        (fiberCoefficient true mu (gammaGradient x.val) (windowState m ell F z hz g x.val)))).im=
      (1/2:ℝ)*(inner ℂ (windowState m ell F z hz g x.val)
        (quantized (principalMatrix (scalarField x.val) (gammaGradient x.val))
          (windowState m ell F z hz g x.val))).im-
      (∑ mu : Fin 8,(inner ℂ (errorColumn false m ell F z hz g mu x.val)
          (fiberCoefficient false mu (gammaGradient x.val) (windowState m ell F z hz g x.val))+
        inner ℂ (errorColumn true m ell F z hz g mu x.val)
          (fiberCoefficient true mu (gammaGradient x.val) (windowState m ell F z hz g x.val)))).im := by
  have hq (sharp : Bool) (mu : Fin 8) : jointState sharp m ell F z hz g mu x.val=
      fiberCoefficient sharp mu (scalarField x.val) (windowState m ell F z hz g x.val)-
        errorColumn sharp m ell F z hz g mu x.val := by
    change spinClosureCoefficient sharp mu (windowState m ell F z hz g) x.val-
      errorColumn sharp m ell F z hz g mu x.val=_
    rw [core_coefficient_at]
  have hp := original_gamma_principal_pair (scalarField x.val) (gammaGradient x.val)
    (windowState m ell F z hz g x.val)
  simp_rw [hq]
  simp only [inner_sub_left,Finset.sum_add_distrib,Finset.sum_sub_distrib,Complex.add_im,Complex.sub_im] at *
  linarith only [hp]

end LowEnergy.SourceClockYukawaGammaPrincipal
