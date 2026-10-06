import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourcePhysicalHamiltonianSquare
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussYukawaCoefficient

/-! A source scale polynomial extracts the actual scalar radius from the full signed action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceHamiltonianScaleJet
open GaussCoreHilbert GaussCoreDifferential GaussNativeForm GaussNativeEnergy GaussCoframeForm
open GaussHistoryHilbert GaussMatterCore GaussDiagonalHistory GaussFockPair
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceKineticTranspose
open SourceDilationKinetic SourceDilationRemainder SourcePhysicalKineticSquare
open SourceCoframeDilation SourceEscapeCurrent SourceMinimalGraphParticular
open FullYSourceResolventGraphSplice SourcePhysicalHamiltonianSquare
open GaussUnitaryHistory (Index)
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open scoped InnerProductSpace RealInnerProductSpace

def scaleDerivative : CoreEnd →ₗ[ℂ] CoreEnd where
  toFun A := (3*Complex.I/2) • (dilation*A-A*dilation)
  map_add' A B := by
    simp only [mul_add,add_mul]
    module
  map_smul' c A := by
    change (3*Complex.I/2) • (dilation*(c • A)-(c • A)*dilation)=
      c • ((3*Complex.I/2) • (dilation*A-A*dilation))
    simp only [mul_smul_comm,smul_mul_assoc,←smul_sub]
    module

private theorem derivative_of_current (A : CoreEnd) (a : ℂ)
    (h : dilation*A-A*dilation=a • A) :
    scaleDerivative A=((3*Complex.I/2)*a) • A := by
  change (3*Complex.I/2) • (dilation*A-A*dilation)=_
  rw [h,smul_smul]

theorem scale_kinetic : scaleDerivative kineticAction=(-3 : ℂ) • kineticAction+(4 : ℂ) • gaugeKinetic := by
  change (3*Complex.I/2) • (dilation*kineticAction-kineticAction*dilation)=_
  rw [kinetic_scale_current,smul_sub,smul_smul,smul_smul]
  have h1 : (3*Complex.I/2)*(2*Complex.I)=(-3 : ℂ) := by
    calc _ = 3*(Complex.I*Complex.I) := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  have h2 : (3*Complex.I/2)*(8*Complex.I/3)=(-4 : ℂ) := by
    calc _ = 4*(Complex.I*Complex.I) := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  rw [h1,h2]
  module

theorem scale_electric : scaleDerivative gaugeKinetic=gaugeKinetic := by
  rw [derivative_of_current _ _ gauge_kinetic_current]
  have h : (3*Complex.I/2)*(-2*Complex.I/3)=(1 : ℂ) := by
    calc _ = -(Complex.I*Complex.I) := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  rw [h,one_smul]

theorem scale_matter : scaleDerivative matterAction=(-1 : ℂ) • matterAction := by
  rw [derivative_of_current _ _ matter_scale_current]
  congr 1
  calc _ = Complex.I*Complex.I := by ring
       _ = _ := Complex.I_mul_I

theorem scale_local : scaleDerivative localAction=(3 : ℂ) • localAction := by
  rw [derivative_of_current _ _ local_scale_current]
  congr 1
  calc _ = -3*(Complex.I*Complex.I) := by ring
       _ = _ := by rw [Complex.I_mul_I]; ring

theorem scale_spatial : scaleDerivative spatialAction=spatialAction := by
  rw [derivative_of_current _ _ spatial_scale_current]
  have h : (3*Complex.I/2)*(-2*Complex.I/3)=(1 : ℂ) := by
    calc _ = -(Complex.I*Complex.I) := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  rw [h,one_smul]

/-- The source weights -3, -1 and +1 cancel; only the actual +3 local action remains. -/
theorem source_local_from_scale_jet :
    scaleDerivative (scaleDerivative (scaleDerivative diagonalAction))+
      (3 : ℂ) • scaleDerivative (scaleDerivative diagonalAction)-
      scaleDerivative diagonalAction-(3 : ℂ) • diagonalAction=(48 : ℂ) • localAction := by
  rw [original_action_split]
  simp only [map_add,map_smul,scale_kinetic,scale_electric,scale_matter,scale_local,scale_spatial]
  module

theorem local_radius_source (z : SourceCoordinateSlice) :
    localPotential z=sourceTime 0*volume z*(4*GaussYukawaCoefficient.radius z^2-1) := by
  have hnonneg : 0≤1+‖(z.2.1 : Scalar)‖^2/4 := by positivity
  have hr := Real.sq_sqrt hnonneg
  unfold GaussYukawaCoefficient.radius
  rw [hr]
  unfold localPotential volumePotential
  rw [real_inner_self_eq_norm_sq]
  ring

def coreDilation (x : diagonal.domain) : H := embed (dilation (coreEquiv.symm x))

private theorem core_embed (x : diagonal.domain) : embed (coreEquiv.symm x)=(x : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply x)

private theorem scale_pair (f g : QuantumTest) :
    sourcePair f (scaleDerivative diagonalAction g)=
      (3*Complex.I/2)*(sourcePair (dilation f) (diagonalAction g)-
        sourcePair (diagonalAction f) (dilation g)) := by
  change sourcePair f ((3*Complex.I/2) •
    (dilation (diagonalAction g)-diagonalAction (dilation g)))=_
  simp only [sourcePair,map_smul,map_sub,inner_smul_right,inner_sub_right]
  change (3*Complex.I/2)*(sourcePair f (dilation (diagonalAction g))-
    sourcePair f (diagonalAction (dilation g)))=_
  rw [dilation_pair f (diagonalAction g),diagonalAction_pair f (dilation g)]
  rfl

/-- The scale jet meets the actual two resolvents through one antisymmetric defect flux. -/
theorem actual_scale_ward (F : Index) (z : ℂ) (hz : z.im≠0)
    (k g : diagonal.domain) :
    let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
    let p := sourceCore F (star z) hs k
    let q := sourceCore F z hz g
    sourcePair (coreEquiv.symm p) (scaleDerivative diagonalAction (coreEquiv.symm q))=
      (3*Complex.I/2)*(inner ℂ (coreDilation p) (g : H)-inner ℂ (k : H) (coreDilation q)+
        inner ℂ (coreDilation p) (finiteProjectionDefect F z hz g)-
        inner ℂ (finiteProjectionDefect F (star z) hs k) (coreDilation q)) := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  dsimp only
  rw [scale_pair]
  change (3*Complex.I/2)*
    (inner ℂ (coreDilation (sourceCore F (star z) hs k)) (diagonal (sourceCore F z hz g))-
      inner ℂ (diagonal (sourceCore F (star z) hs k)) (coreDilation (sourceCore F z hz g)))=_
  rw [source_core_action,source_core_action]
  simp only [inner_add_right,inner_add_left,inner_smul_right,inner_smul_left,
    starRingEnd_apply,star_star]
  have hd : inner ℂ (coreDilation (sourceCore F (star z) hs k))
      (finiteResolvent F z (g : H))=
    inner ℂ (finiteResolvent F (star z) (k : H)) (coreDilation (sourceCore F z hz g)) := by
    have h := (dilation_pair (coreEquiv.symm (sourceCore F (star z) hs k))
      (coreEquiv.symm (sourceCore F z hz g))).symm
    simp only [sourcePair,core_embed] at h
    exact h
  rw [hd]
  ring

end LowEnergy.SourceHamiltonianScaleJet
