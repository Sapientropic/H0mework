import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseScalarSourceWork
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceHamiltonianScaleJet
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy GaussNativePotential
open GaussNativeForm GaussCoframeForm SourcePhysicalHamiltonianSquare SourceKineticTranspose
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceClockPhiCombinedScalePressure
open SourceCoframeVolumeCurrent SourceHamiltonianScaleJet SourceDilationRemainder SourcePhysicalKineticSquare
open FirstCurrentDilationPrimitive FirstCurrentJointBudget FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open ClockPhiHeatCorrectedCovarianceSource
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev D:End:=combinedGenerator
private abbrev Z:End:=reverseNativeClock
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic GaussMatterCore.matterAction
  nativeDilationWord reverseNativeClock normalizedState normalizedForcing wholeSourceNext correctedCompleteCore

/-- Every residual department is an original native or local source word. The full coframe action is retained in the explicit 18 H0 term. -/
def reverseScaleForce:End:=(3:ℂ) • nativeDilationWord-(24:ℂ) • gaugeKinetic-
  (12:ℂ) • GaussMatterCore.matterAction-(36:ℂ) • localAction-(24:ℂ) • spatialAction
private theorem whole_scale:
    scaleDerivative H0=(-3:ℂ) • H0+(4:ℂ) • gaugeKinetic+(2:ℂ) • GaussMatterCore.matterAction+
      (6:ℂ) • localAction+(4:ℂ) • spatialAction:=by
  rw [show H0=kineticAction+GaussMatterCore.matterAction+localAction+spatialAction from original_action_split]
  simp only [map_add,scale_kinetic,scale_matter,scale_local,scale_spatial]
  module
private theorem Z_scale(T:End):
    bracket Z T=(3:ℂ) • bracket D T-(6:ℂ) • scaleDerivative T:=by
  unfold Z reverseNativeClock bracket scaleDerivative
  simp only [LinearMap.coe_mk,AddHom.coe_mk,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,
    smul_smul,smul_sub]
  have hc:(6:ℂ)*(3*Complex.I/2)=9*Complex.I:=by ring
  rw [hc]
  module

/-- The complete original Hamiltonian has a generated scale-force, before any frequency or damping interpretation is made. -/
theorem actual_reverse_full_hamiltonian_scale:
    bracket Z H0=(18:ℂ) • H0+reverseScaleForce:=by
  rw [Z_scale,actual_combined_native_current,whole_scale]
  unfold reverseScaleForce
  module

/-- The scale-force contains all six native dilation terms and the full original local/spatial actions. -/
theorem actual_reverse_scale_departments:
    reverseScaleForce=(-6:ℂ) • scalarKinetic-(18:ℂ) • gaugeKinetic-
      (15:ℂ) • GaussMatterCore.matterAction+(6:ℂ) • centeredAction-(6:ℂ) • vacuumLinearAction-
      (12:ℂ) • magneticAction-(36:ℂ) • localAction-(24:ℂ) • spatialAction:=by
  unfold reverseScaleForce nativeDilationWord
  module

/-- Same full source, same pole: scaling produces a frequency term and a literal source force, not a physical-time growth estimate. -/
theorem actual_full_reverse_scale_source(z:ℂ)(w f:QuantumTest)(he:H0 w=f+z • w):
    H0 (Z w)=(Z f-(18:ℂ) • f-reverseScaleForce w-(18*z) • w)+z • Z w:=by
  have h:=LinearMap.congr_fun actual_reverse_full_hamiltonian_scale w
  simp only [bracket,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply] at h
  rw [he,map_add,map_smul] at h
  linear_combination (norm:=module) -h

/-- The existing native Noether endpoints consume the full scale-force without altering either actual endpoint. -/
theorem actual_reverse_endpoint_scale_force(h:ℝ)(forward:Bool)(z:ℂ)(w f:QuantumTest)
    (he:H0 w=f+z • w):
    (reverseSourceEndpoint h forward w f).2=
      f+(if forward then (h:ℂ) else -(h:ℂ)) •
        (Z f-(18:ℂ) • f-reverseScaleForce w-(18*z) • w):=by
  have hs:=actual_full_reverse_scale_source z w f he
  have hr:Z f+bracket H0 Z w=Z f-(18:ℂ) • f-reverseScaleForce w-(18*z) • w:=by
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
    rw [he,map_add,map_smul,hs]
    module
  exact congrArg (fun v:QuantumTest=>f+(if forward then (h:ℂ) else -(h:ℂ)) • v) hr

/-- The actual clocked whole-source endpoints carry this same complete scale force. In particular H0 of the actual electric-step discrepancy has not been dropped. -/
theorem actual_clocked_whole_reverse_scale_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ)(h:ℝ)(forward:Bool):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
    H0 (Z a.1)=(Z a.2-(18:ℂ) • a.2-reverseScaleForce a.1-(18*z) • a.1)+z • Z a.1 ∧
    (reverseSourceEndpoint h forward a.1 a.2).2=
      a.2+(if forward then (h:ℂ) else -(h:ℂ)) •
        (Z a.2-(18:ℂ) • a.2-reverseScaleForce a.1-(18*z) • a.1):=by
  dsimp only
  have he:=(((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
  exact ⟨actual_full_reverse_scale_source _ _ _ he,actual_reverse_endpoint_scale_force h forward _ _ _ he⟩
end LowEnergy.ReverseNativeClock
