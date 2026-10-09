import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCombinedScalePressure
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeForwardCore
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceHamiltonianScaleJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatNativeHamiltonianWork
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiOriginalGaussianH0KineticPrimitives
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoframeForm GaussLiveMomentum SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarGaugeScale
open SourceClockPhiCombinedScalePressure SourceClockPhiCoframeForwardCore
open scoped ContDiff InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U : End := inverseVolumeAction
private abbrev a : End := inverseRootAction
private abbrev D : End := combinedGenerator
attribute [local irreducible] scalarKinetic gaugeKinetic GaussMatterCore.matterAction
private theorem combined_delta (T:End):bracket D T=deltaPhi T-deltaGauge T := by
  unfold D combinedGenerator bracket
  rw [sub_mul,mul_sub]
  have hp:=SourceScalarAffineScaleTransport.generator_commutator T
  have hg:=SourceGaugeScaleTransport.generator_commutator T
  linear_combination (norm:=module) hp-hg
private theorem root_native (v:Ambient):Commute (covariantMomentum v) a :=
  SourceClockPhiHeatNativeHamiltonianWork.native_multiplier_commute inverseRootVolume inverse_root_volume_smooth
    (fun z w s=>by simp [inverseRootVolume,GaussNativeEnergy.volume]) v
private theorem root_adjoint (v:Ambient):Commute (GaussMomentumAdjoint.adjoint v) a := by
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have hc:=LinearMap.congr_fun (root_native v).eq f
  change sourcePair f (GaussMomentumAdjoint.adjoint v (a g))=
    sourcePair f (a (GaussMomentumAdjoint.adjoint v g))
  calc
    _=sourcePair (covariantMomentum v f) (a g) := adjoint_pair _ _ _
    _=sourcePair (a (covariantMomentum v f)) g := multiply_pair _ _ _ _
    _=sourcePair (covariantMomentum v (a f)) g := congrArg (fun q=>sourcePair q g) hc.symm
    _=sourcePair (a f) (GaussMomentumAdjoint.adjoint v g) := (adjoint_pair _ _ _).symm
    _=_ := (multiply_pair _ _ _ _).symm
private theorem scalar_root:Commute a scalarKinetic := by
  have hterm (i:ScalarIndex):Commute a (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth) := by
    change Commute a (GaussMomentumAdjoint.adjoint (scalarDirection i)*
      (multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection i)))
    have hw:Commute a (multiply scalarWeight scalarWeight_smooth) := by
      apply LinearMap.ext
      intro f
      apply DFunLike.ext
      intro z
      exact smul_comm (inverseRootVolume z:ℂ) (scalarWeight z:ℂ) (f z)
    exact (root_adjoint _).symm.mul_right (hw.mul_right (root_native _).symm)
  unfold scalarKinetic
  change Commute a ((1/2:ℂ) • ∑i:ScalarIndex,sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth)
  exact (Commute.sum_right _ _ _ (fun i _=>hterm i)).smul_right _
private theorem quantum_root (A:SourceCoordinateSlice→Matrix Mode Mode ℂ)
    (hA:∀z:physicalChart,ContDiffAt ℝ ∞ (fun w=>GaussQuantumMultiplier.quantized (A w)) z.val):
    Commute a (GaussQuantumMultiplier.action A hA) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (inverseRootVolume z:ℂ) • (GaussQuantumMultiplier.quantized (A z) (f z))=
    GaussQuantumMultiplier.quantized (A z) ((inverseRootVolume z:ℂ) • f z)
  rw [map_smul]
private theorem matter_root:Commute a GaussMatterCore.matterAction := by
  unfold GaussMatterCore.matterAction
  exact Commute.sum_right _ _ _ (fun i _=>Commute.sum_right _ _ _ (fun j _=>quantum_root _ _))
private theorem inverse_of_root (T:End)(hc:Commute a T):Commute U T := by
  have hs:a*a=U:=by
    apply LinearMap.ext
    intro f
    exact inverse_root_square f
  rw [←hs]
  exact hc.mul_left hc
private theorem forward_from_current (T:End)(c:ℂ)(hU:Commute U T)
    (hC:dilation*T-T*dilation=c • T):bracket forwardGenerator T=((-9*Complex.I)*c) • (U*T) := by
  have hm:T*(U*dilation)=U*(T*dilation) := by
    rw [←mul_assoc,←hU.eq,mul_assoc]
  calc
    bracket forwardGenerator T=(-9*Complex.I:ℂ) • (U*(dilation*T-T*dilation)) := by
      unfold forwardGenerator bracket
      simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm]
      rw [hm,hU.eq]
      simp only [mul_sub,smul_sub,mul_assoc]
      module
    _=((-9*Complex.I)*c) • (U*T) := by
      rw [hC,mul_smul_comm,smul_smul]

theorem scalar_kinetic_primitives:
    Commute U scalarKinetic ∧ Commute a scalarKinetic ∧
    bracket D scalarKinetic=(-2:ℂ) • scalarKinetic ∧
    bracket forwardGenerator scalarKinetic=(18:ℂ) • (U*scalarKinetic) := by
  have hU:=inverse_of_root scalarKinetic scalar_root
  refine ⟨hU,scalar_root,?_,?_⟩
  · rw [combined_delta,original_scalar_kinetic_phi,original_scalar_kinetic_gauge,sub_zero]
  · have h:=forward_from_current scalarKinetic (2*Complex.I) hU SourceDilationKinetic.scalar_kinetic_current
    have hc:(-9*Complex.I)*(2*Complex.I)=18:=by
      calc (-9*Complex.I)*(2*Complex.I)= -18*(Complex.I*Complex.I) := by ring
           _=18 := by rw [Complex.I_mul_I];ring
    simpa only [hc] using h

theorem gauge_kinetic_primitives:
    Commute U gaugeKinetic ∧ Commute a gaugeKinetic ∧
    bracket D gaugeKinetic=(2:ℂ) • gaugeKinetic ∧
    bracket forwardGenerator gaugeKinetic=(-6:ℂ) • (U*gaugeKinetic) := by
  have ha:Commute a gaugeKinetic:=inverse_root_electric
  have hU:=inverse_of_root gaugeKinetic ha
  refine ⟨hU,ha,?_,?_⟩
  · rw [combined_delta,original_gauge_kinetic_phi,original_gauge_kinetic_gauge,zero_sub]
    module
  · have h:=forward_from_current gaugeKinetic (-2*Complex.I/3) hU SourceDilationKinetic.gauge_kinetic_current
    have hc:(-9*Complex.I)*(-2*Complex.I/3)=(-6):=by
      calc (-9*Complex.I)*(-2*Complex.I/3)=6*(Complex.I*Complex.I) := by ring
           _= -6 := by rw [Complex.I_mul_I];ring
    simpa only [hc] using h

theorem matter_primitives:
    Commute U GaussMatterCore.matterAction ∧ Commute a GaussMatterCore.matterAction ∧
    bracket D GaussMatterCore.matterAction=(-1:ℂ) • GaussMatterCore.matterAction ∧
    bracket forwardGenerator GaussMatterCore.matterAction=(6:ℂ) • (U*GaussMatterCore.matterAction) := by
  have hU:=inverse_of_root GaussMatterCore.matterAction matter_root
  refine ⟨hU,matter_root,?_,?_⟩
  · rw [combined_delta,original_matter_phi,original_matter_gauge,zero_sub]
    module
  · have h:=forward_from_current GaussMatterCore.matterAction (2*Complex.I/3) hU SourceDilationRemainder.matter_scale_current
    have hc:(-9*Complex.I)*(2*Complex.I/3)=6:=by
      calc (-9*Complex.I)*(2*Complex.I/3)= -6*(Complex.I*Complex.I) := by ring
           _=6 := by rw [Complex.I_mul_I];ring
    simpa only [hc] using h
end LowEnergy.SourceClockPhiOriginalGaussianH0KineticPrimitives
