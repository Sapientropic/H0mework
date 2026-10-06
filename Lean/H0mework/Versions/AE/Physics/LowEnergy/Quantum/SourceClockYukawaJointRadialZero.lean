import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaJointCoframeForce
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaGammaPrincipal
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaRadialHessianBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaJointRadialZero
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussQuantumMultiplier
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open PositiveScalarWeakBudget PositiveScalarCoefficientDecay SourceLocalizedInverseFormPayment
open SourceClockYukawaSpinClosure SourceClockYukawaSpinNativeJet SourceInverseNeutralSpinCurrent
open SourceClockYukawaSpinNativeBudget SourceClockYukawaRadialNativeBudget
open SourceScalarGaugeForce SourceYukawaCoefficientCommutator
open SourceClockYukawaRadialJoinedHessian SourceClockYukawaRadialHessianBudget
open SourceClockYukawaSpinJointForce SourceClockYukawaJointCoframeForce
open SourceClockYukawaSpinNativeDivergence SourceClockYukawaRadialCoefficient
open SourceClockYukawaGammaPrincipal SourceClockYukawaRadialNativeHessian
open SourceClockYukawaCubicCurrent FullYSourceResolventGraphSplice SourceClockYukawaTail
open scoped ContDiff InnerProductSpace BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] fullAction compressionCore defectAction

private def ad (J : End) : End →ₗ[ℂ] End where
  toFun A := bracket J A
  map_add' A B := by unfold bracket;noncomm_ring
  map_smul' c A := by simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private def recipe (mu : Fin 8) : End →ₗ[ℂ] End :=
  if h0 : mu.val=0 then LinearMap.id else
  if h1 : mu.val<5 then ad (activeSpin ⟨mu.val-1,by omega⟩) else
    (ad (activeSpin ⟨mu.val-5,by omega⟩)).comp (ad (activeSpin 3))

private theorem ad_bimodule (J L A R : End) (hL : Commute J L) (hR : Commute J R) :
    bracket J (L*A*R)=L*bracket J A*R := by
  unfold bracket
  linear_combination (norm := noncomm_ring) hL.eq*A*R+L*A*hR.eq

private theorem recipe_bimodule (mu : Fin 8) (L A R : End)
    (hL : ∀ j : Fin 4,Commute (activeSpin j) L)
    (hR : ∀ j : Fin 4,Commute (activeSpin j) R) :
    recipe mu (L*A*R)=L*recipe mu A*R := by
  unfold recipe
  split_ifs with h0 h1
  · rfl
  · exact ad_bimodule _ _ _ _ (hL _) (hR _)
  · change bracket _ (bracket _ (L*A*R))=L*bracket _ (bracket _ A)*R
    rw [ad_bimodule _ _ _ _ (hL 3) (hR 3),ad_bimodule _ _ _ _ (hL _) (hR _)]

private theorem recipe_left (mu : Fin 8) (L A : End) (hL : ∀ j : Fin 4,Commute (activeSpin j) L) :
    recipe mu (L*A)=L*recipe mu A := by
  simpa only [mul_one] using recipe_bimodule mu L A 1 hL (fun _ => Commute.one_right _)
private theorem recipe_right (mu : Fin 8) (A R : End) (hR : ∀ j : Fin 4,Commute (activeSpin j) R) :
    recipe mu (A*R)=recipe mu A*R := by
  simpa only [one_mul] using recipe_bimodule mu 1 A R (fun _ => Commute.one_right _) hR
private theorem recipe_bracket (mu : Fin 8) (P A : End) (hP : ∀ j : Fin 4,Commute (activeSpin j) P) :
    bracket P (recipe mu A)=recipe mu (bracket P A) := by
  simp only [bracket,map_sub,recipe_left mu P A hP,recipe_right mu A P hP]

private theorem recipe_commute (mu : Fin 8) (A B : End)
    (hB : ∀ j : Fin 4,Commute (activeSpin j) B) (hA : Commute B A) : Commute B (recipe mu A) := by
  apply sub_eq_zero.mp
  change bracket B (recipe mu A)=0
  rw [recipe_bracket mu B A hB,show bracket B A=0 from sub_eq_zero.mpr hA.eq,map_zero]

private theorem real_spin (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (j : Fin 4) :
    Commute (activeSpin j) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (GaussCoframeSpin.full (activeIndex j))) (c z:ℂ) (f z)

/-- The gamma action uses exactly the same eight source-spin coefficients as the coherent column. -/
def gammaCore (sharp : Bool) (mu : Fin 8) : End := recipe mu (gammaAction sharp)
def radialHessian (sharp : Bool) (mu : Fin 8) (m ell : ℕ) : End :=
  recipe mu (radialHessianCore sharp m ell)

def paidVector (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (rS rA q : QuantumTest) : QuantumTest :=
  (-1/2:ℂ) • radialHessian sharp mu m ell rS+
  (1/8:ℂ) • weightCore rA-
  ∑ a : ScalarIndex,inverseDerivativeCore a (jointCoefficient sharp mu a m ell q)

private theorem inverse_gamma (sharp : Bool) : Commute inverseAction (gammaAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  exact (map_smul (branchMap sharp (gammaGradient x)) (reciprocal x:ℂ) (f x)).symm

private theorem theta_gamma (sharp : Bool) (mu : Fin 8) (m ell : ℕ) :
    Commute (thetaAction m ell) (gammaCore sharp mu) := by
  have hi : Commute inverseAction (gammaCore sharp mu) :=
    recipe_commute mu _ _ (real_spin _ _) (inverse_gamma sharp)
  unfold thetaAction
  exact (((Commute.one_left _).sub_left hi).pow_left _).sub_left
    (((Commute.one_left _).sub_left hi).pow_left _)

private theorem joined_sum (sharp : Bool) (mu : Fin 8) (m ell : ℕ) :
    (∑ a : ScalarIndex,jointZeroCore sharp mu a m ell)=
      Complex.I • (multiply scalarWeight scalarWeight_smooth*
        (radialHessian sharp mu m ell-thetaAction m ell*gammaCore sharp mu)) := by
  have he (a : ScalarIndex) : jointZeroCore sharp mu a m ell=
      recipe mu (SourceClockYukawaRadialNativeDivergence.joinedZeroCore sharp a m ell) := rfl
  simp only [he,←map_sum,SourceClockYukawaRadialJoinedHessian.original_joined_hessian_source,
    joinedHessianCore,map_smul]
  rw [recipe_left mu _ _ (real_spin _ _),map_sub,recipe_left]
  · rfl
  · intro j
    rw [thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
    exact real_spin _ _ j

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold inverseVolumeAction
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

/-- The full eight-component native Hessian has only its exact radial and gamma source parts. -/
theorem original_joint_scalar_zero_source (sharp : Bool) (mu : Fin 8) (m ell : ℕ)
    (rS rA q : QuantumTest) :
    scalarZeroOrderWord sharp mu m ell rS rA q=
      (sourceTime 0:ℂ) • inverseVolumeAction (paidVector sharp mu m ell rS rA q)+
      ((sourceTime 0:ℂ)/2) • inverseVolumeAction (gammaCore sharp mu (thetaAction m ell rS)) := by
  have hZ := LinearMap.congr_fun (joined_sum sharp mu m ell) rS
  have hd := LinearMap.congr_fun SourceClockYukawaRadialNativeHessian.original_inverse_hessian_source rA
  have hi : (-Complex.I/2)*Complex.I=(1/2:ℂ) := by
    calc _= -(Complex.I*Complex.I)/2 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  have hn : (-Complex.I/2)*(Complex.I*(sourceTime 0:ℂ)/4)=(sourceTime 0:ℂ)/8 := by
    calc _= -(Complex.I*Complex.I)*(sourceTime 0:ℂ)/8 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  have ht := LinearMap.congr_fun (theta_gamma sharp mu m ell).eq rS
  change thetaAction m ell (gammaCore sharp mu rS)=gammaCore sharp mu (thetaAction m ell rS) at ht
  simp only [scalarZeroOrderWord,Finset.sum_add_distrib,←LinearMap.sum_apply,hZ,hd,
    LinearMap.smul_apply,smul_add,smul_smul,hi,hn,Module.End.mul_apply,LinearMap.sub_apply,
    map_sub,ht,weight_inverse,paidVector,weightCore,map_add,map_smul,map_sum]
  rw [←Finset.smul_sum]
  module

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    bracket (quantized A) (quantized B)=quantized (bracket A B) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [bracket,quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

private theorem active_at (j : Fin 4) (f : QuantumTest) (x : SourceCoordinateSlice) :
    activeSpin j f x=quantized (GaussCoframeSpin.full (activeIndex j)) (f x) := rfl

/-- This global gamma core is the actual fiber carrier of the joint two-branch CAR principal. -/
theorem original_gamma_core_point (sharp : Bool) (mu : Fin 8) (f : QuantumTest)
    (x : SourceCoordinateSlice) :
    gammaCore sharp mu f x=fiberCoefficient sharp mu (gammaGradient x) (f x) := by
  have hb : branchMap sharp (gammaGradient x)=quantized (branchMatrix sharp (gammaGradient x)) := by
    cases sharp
    · rfl
    · change (quantized (GaussYukawaCoefficient.fullMatrix (gammaGradient x))).adjoint=_
      apply ContinuousLinearMap.ext
      intro u
      apply ext_inner_left ℂ
      intro v
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact SourceQuantumFockGauge.quantizedFiber_adjoint _ v u
  have hg (q : QuantumTest) : gammaAction sharp q x=quantized (branchMatrix sharp (gammaGradient x)) (q x) :=
    congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (q x)) hb
  unfold gammaCore recipe fiberCoefficient coefficientMatrix
  split_ifs with h0 h1
  · exact hg f
  · change bracket (activeSpin ⟨mu.val-1,by omega⟩) (gammaAction sharp) f x=_
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,active_at,hg]
    change (bracket (quantized (GaussCoframeSpin.full (activeIndex ⟨mu.val-1,by omega⟩)))
      (quantized (branchMatrix sharp (gammaGradient x)))) (f x)=_
    rw [quantized_bracket]
    rfl
  · change bracket (activeSpin ⟨mu.val-5,by omega⟩) (bracket (activeSpin 3) (gammaAction sharp)) f x=_
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,active_at,hg]
    change (bracket (quantized (GaussCoframeSpin.full (activeIndex ⟨mu.val-5,by omega⟩)))
      (bracket (quantized (GaussCoframeSpin.full (activeIndex 3)))
        (quantized (branchMatrix sharp (gammaGradient x))))) (f x)=_
    rw [quantized_bracket,quantized_bracket]
    rfl

def paidRadialWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  let h := SourceClockYukawaRadialMixedBudget.radiusSource g
  (sourceTime 0:ℂ) • inverseVolumeAction (paidVector sharp mu m ell
    (radialCore F z hz h) (cutoffResponseCore sharp mu m ell F z hz h)
    (SourceScalarPositiveBulkWard.state F z hz h))

def gammaWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  ((sourceTime 0:ℂ)/2) • inverseVolumeAction (gammaCore sharp mu (windowState m ell F z hz g))

def fieldRemainingWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  let h := SourceClockYukawaRadialMixedBudget.radiusSource g
  let rS := radialCore F z hz h
  let rA := cutoffResponseCore sharp mu m ell F z hz h
  let q := SourceScalarPositiveBulkWard.state F z hz h
  gammaWord sharp m ell F z hz g mu+matterWord sharp m ell F z hz g mu-
    bracket (defectAction F) (cutoffCore sharp m ell mu) rS-
    bracket (defectAction F) inverseAction rA+
    bracket (bracket (defectAction F) inverseAction) (cutoffCore sharp m ell mu) q

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

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

/-- The actual Gamma field remainder retains only gamma, matter and all three full compression defects after the radial payment word is extracted. -/
theorem actual_joint_radial_zero_source (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) (mu : Fin 8) :
    coframeRemainingWord sharp m ell F z hz g mu=
      paidRadialWord sharp m ell F z hz g mu+fieldRemainingWord sharp m ell F z hz g mu := by
  unfold coframeRemainingWord paidRadialWord fieldRemainingWord gammaWord windowState
  dsimp only
  rw [radial_map_return,original_joint_scalar_zero_source]
  have hswap (a b c d e f : QuantumTest) : (a+b)+c-d-e+f=a+(b+c-d-e+f) := by abel
  exact hswap _ _ _ _ _ _

end LowEnergy.SourceClockYukawaJointRadialZero
