import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageGaussEnergyRead
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeEnergyPort

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNormalizedFullField
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField ProofFreeRicherAnholonomicSource Stage10 Stage10.TemporalGauge
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCanonicalCauchyState StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open Stage9C.Material.SpinPair DiracExteriorMatterAction FullQuantum.StateGreen FullQuantum.CoframeResponse
open PreparationVacuumStaticVoltageSource PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalDensity
open PreparationVacuumPhysicalModeChargeRead PreparationVacuumNativeFieldInjection
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussQuantumMultiplier
open GaussCoreHilbert GaussFockLift CanonicalGradedSpatialSource CanonicalGradedCharge GaussComposite
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert PreparationPhysicalActionUnits
open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace Topology ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
open PreparationPhysicalVoltageNoether
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional


/-- The full variation includes the inverse time-momentum variation. -/
def sourceNormalizedEnergyJet (s v : ActionState) (k : Fin 4) : SourceMatrix :=
  fderiv ℝ sourceCanonicalMomentumInverse s v *
    ((ActionNormalization.actionScale:ℂ) • originalEnergyCoefficient s k)+
  sourceCanonicalMomentumInverse s * ((ActionNormalization.actionScale:ℂ) •
    fderiv ℝ (fun w=>originalEnergyCoefficient w k) s v)

theorem sourceCanonicalMomentumInverse_smooth (s : ActionState) (valid : s∈validStates) :
    ContDiffAt ℝ ∞ sourceCanonicalMomentumInverse s :=
  (statePhase_smooth s valid.1 valid.2).mul contDiffAt_const

/-- Same original energy and same original momentum, along the complete state direction. -/
theorem sourceNormalizedEnergyJet_derivative (s v : ActionState) (valid : s∈validStates) (k : Fin 4) :
    HasDerivAt (fun t : ℝ=>sourceCanonicalMomentumInverse (s+t • v)*
      ((ActionNormalization.actionScale:ℂ) • originalEnergyCoefficient (s+t • v) k))
      (sourceNormalizedEnergyJet s v k) 0 := by
  have left:=((sourceCanonicalMomentumInverse_smooth s valid).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 (state_line s v) (by simp)
  have right:=((originalEnergyCoefficient_smooth s valid.1 k).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 (state_line s v) (by simp)
  convert! left.mul (right.const_smul (ActionNormalization.actionScale:ℂ)) using 1
  simp only [sourceNormalizedEnergyJet,Function.comp_apply,Pi.smul_apply,zero_smul,add_zero]

theorem sourceNormalizedEnergyJet_return (s v : ActionState) (valid : s∈validStates) (k : Fin 4) :
    sourceNormalizedEnergyJet s v k=fderiv ℝ (fun w=>stateHamiltonian w k) s v := by
  have original:=((stateHamiltonian_smooth s valid.1 valid.2 k).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 (state_line s v) (by simp)
  have near : ∀ᶠt in 𝓝 (0:ℝ),s+t • v∈validStates :=
    (state_line s v).continuousAt.preimage_mem_nhds (by simpa using validStates_open.mem_nhds valid)
  have same : (fun t : ℝ=>sourceCanonicalMomentumInverse (s+t • v)*
      ((ActionNormalization.actionScale:ℂ) • originalEnergyCoefficient (s+t • v) k))=ᶠ[𝓝 (0:ℝ)]
      (fun t=>stateHamiltonian (s+t • v) k) :=
    near.mono fun t ht=>sourceCanonicalMomentum_energyCoefficient_return _ ht.1 ht.2 k
  exact (sourceNormalizedEnergyJet_derivative s v valid k).unique (original.congr_of_eventuallyEq same)

/-- No coframe restriction is imposed on the 289-field probe. -/
theorem sourceNormalizedEnergyJet_fullField (s : ActionState) (valid : s∈validStates)
    (f : Field289) (k : Fin 4) :
    sourceNormalizedEnergyJet s (fieldDirection f) k= -(statePhase s*densityVariation f s k) := by
  have original:=((stateHamiltonian_smooth s valid.1 valid.2 k).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 (state_line s (fieldDirection f)) (by simp)
  rw [sourceNormalizedEnergyJet_return s _ valid]
  exact original.unique (PreparationVacuumCausalFieldResponse.state_forcing_generated f s valid.1 valid.2 k)

def sourceNormalizedEnergySymbol (p : PhysicalMomentum) (s v : ActionState) : FullMatrix :=
  fourierLinear p (sourceNormalizedEnergyJet s v)

theorem sourceNormalizedEnergySymbol_original (p : PhysicalMomentum) (s v : ActionState)
    (valid : s∈validStates) : sourceNormalizedEnergySymbol p s v=symbolFirst p s v := by
  have path:=hasDerivAt_pi.mpr (fun k=>sourceNormalizedEnergyJet_derivative s v valid k)
  have lifted:=(fourierLinear p).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 path
  have near : ∀ᶠt in 𝓝 (0:ℝ),s+t • v∈validStates :=
    (state_line s v).continuousAt.preimage_mem_nhds (by simpa using validStates_open.mem_nhds valid)
  have same : (fun t : ℝ=>fourierLinear p (fun k=>sourceCanonicalMomentumInverse (s+t • v)*
      ((ActionNormalization.actionScale:ℂ) • originalEnergyCoefficient (s+t • v) k)))=ᶠ[𝓝 (0:ℝ)]
      (fun t=>sourceSymbol p (s+t • v)) := by
    filter_upwards [near] with t ht
    exact congrArg (fourierLinear p) (funext (sourceCanonicalMomentum_energyCoefficient_return _ ht.1 ht.2))
  exact lifted.unique ((symbol_first_generated p s v valid).congr_of_eventuallyEq same)

/-- The already generated voltage energy is the exact restriction of the full normalized jet. -/
theorem sourceNormalizedEnergySymbol_voltage (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (value slope : ℝ) :
    sourceNormalizedEnergySymbol p s (sourceVoltageStateDirection value slope)=
      sourceVoltageEnergySymbol p s value slope := by
  rw [sourceNormalizedEnergySymbol_original p s _ valid,sourceVoltageSymbol_first p s valid,
    sourceVoltageEnergySymbol_generated p s valid.1 valid.2]

/-- Connection, scalar and coframe variations remain separate in the same lower symbol. -/
def sourceLowerJet (s v : ActionState) : SourceMatrix :=
  (∑mu : Fin 4,(sourceCoframeCoefficientJet s.1 v.1 mu*s.2.1 mu+
    coefficientMatrix mu s.1*v.2.1 mu))+v.2.2

theorem sourceLowerJet_derivative (s v : ActionState) (nondegenerate : s.1.det≠0) :
    HasDerivAt (fun t : ℝ=>stateLower (s+t • v)) (sourceLowerJet s v) 0 := by
  have connection (mu : Fin 4) : HasDerivAt (fun t : ℝ=>s.2.1 mu+t • v.2.1 mu) (v.2.1 mu) 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const (v.2.1 mu)).const_add (s.2.1 mu)
  have scalar : HasDerivAt (fun t : ℝ=>s.2.2+t • v.2.2) v.2.2 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const v.2.2).const_add s.2.2
  have result:=(HasDerivAt.fun_sum (fun mu (_ : mu∈(Finset.univ : Finset (Fin 4)))=>
    (sourceCoframeCoefficient_derivative s.1 v.1 nondegenerate mu).mul (connection mu))).add scalar
  convert! result using 1
  simp only [sourceLowerJet,zero_smul,add_zero]

/-- The temporal principal inverse belongs to the same varying source coframe. -/
def sourcePrincipalInverseJet (s v : ActionState) : SourceMatrix :=
  -(Ring.inverse (principalMatrix s.1)*sourceCoframeCoefficientJet s.1 v.1 0*
    Ring.inverse (principalMatrix s.1))

theorem sourcePrincipalInverse_derivative (s v : ActionState) (valid : s∈validStates) :
    HasDerivAt (fun t : ℝ=>Ring.inverse (principalMatrix (s+t • v).1))
      (sourcePrincipalInverseJet s v) 0 := by
  have unit:=principalMatrix_regular s.1 valid.2
  have inverse:=hasFDerivAt_ringInverse (𝕜:=ℝ) unit.unit
  have unitInverse : (↑unit.unit⁻¹ : SourceMatrix)=Ring.inverse (principalMatrix s.1) := by
    rw [←Ring.inverse_unit,unit.unit_spec]
  have principal : HasDerivAt (fun t : ℝ=>principalMatrix (s.1+t • v.1))
      (sourceCoframeCoefficientJet s.1 v.1 0) 0 := by
    simpa only [principalMatrix_coefficient] using sourceCoframeCoefficient_derivative s.1 v.1 valid.1 0
  have result:=inverse.comp_hasDerivAt_of_eq 0 principal (by simp)
  convert! result using 1
  simp only [unitInverse,sourcePrincipalInverseJet,neg_apply,
    ContinuousLinearMap.mulLeftRight_apply]

/-- A finite matrix formula for every original normalized energy coefficient. -/
def sourceHamiltonianJetMatrix (s v : ActionState) (k : Fin 4) : SourceMatrix :=
  Fin.cases
    ((-Complex.I) • (sourcePrincipalInverseJet s v*stateLower s+
      Ring.inverse (principalMatrix s.1)*sourceLowerJet s v))
    (fun j=>sourcePrincipalInverseJet s v*coefficientMatrix j.succ s.1+
      Ring.inverse (principalMatrix s.1)*sourceCoframeCoefficientJet s.1 v.1 j.succ) k

theorem sourceHamiltonianJetMatrix_derivative (s v : ActionState) (valid : s∈validStates)
    (k : Fin 4) : HasDerivAt (fun t : ℝ=>stateHamiltonian (s+t • v) k)
      (sourceHamiltonianJetMatrix s v k) 0 := by
  have inverse:=sourcePrincipalInverse_derivative s v valid
  cases k using Fin.cases with
  | zero=>
    have lower:=sourceLowerJet_derivative s v valid.1
    apply hasDerivAt_pi.mpr
    intro a
    apply hasDerivAt_pi.mpr
    intro b
    have result:=(HasDerivAt.fun_sum (fun c (_ : c∈(Finset.univ : Finset Quantum.Index))=>
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp inverse a) c).mul
        (hasDerivAt_pi.mp (hasDerivAt_pi.mp lower c) b))).const_mul (-Complex.I)
    convert! result using 1
    simp only [sourceHamiltonianJetMatrix,Fin.cases_zero,
      Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,Matrix.add_apply,
      Finset.sum_add_distrib,zero_smul,add_zero]
  | succ j=>
    have coefficient:=sourceCoframeCoefficient_derivative s.1 v.1 valid.1 j.succ
    apply hasDerivAt_pi.mpr
    intro a
    apply hasDerivAt_pi.mpr
    intro b
    have result:=HasDerivAt.fun_sum (fun c (_ : c∈(Finset.univ : Finset Quantum.Index))=>
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp inverse a) c).mul
        (hasDerivAt_pi.mp (hasDerivAt_pi.mp coefficient c) b))
    convert! result using 1
    simp only [sourceHamiltonianJetMatrix,Fin.cases_succ,
      Matrix.mul_apply,Matrix.add_apply,Finset.sum_add_distrib,zero_smul,add_zero]

/-- Original momentum-energy normalization now returns the literal source inverse-variation port. -/
theorem sourceNormalizedEnergyJet_matrix (s v : ActionState) (valid : s∈validStates) (k : Fin 4) :
    sourceNormalizedEnergyJet s v k=sourceHamiltonianJetMatrix s v k := by
  have original:=((stateHamiltonian_smooth s valid.1 valid.2 k).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 (state_line s v) (by simp)
  rw [sourceNormalizedEnergyJet_return s v valid]
  exact original.unique (sourceHamiltonianJetMatrix_derivative s v valid k)

theorem sourceNormalizedEnergySymbol_matrix (p : PhysicalMomentum) (s v : ActionState)
    (valid : s∈validStates) :
    sourceNormalizedEnergySymbol p s v=fourierLinear p (sourceHamiltonianJetMatrix s v) := by
  unfold sourceNormalizedEnergySymbol
  exact congrArg (fourierLinear p) (funext (sourceNormalizedEnergyJet_matrix s v valid))

/-- This restriction applies only to source directions whose coframe and scalar components actually vanish. -/
theorem sourceHamiltonianJet_connection (s : ActionState) (A : Fin 4→SourceMatrix) (k : Fin 4) :
    sourceHamiltonianJetMatrix s (0,A,0) k=
      if k=0 then (-Complex.I) • (Ring.inverse (principalMatrix s.1)*
        (∑mu : Fin 4,coefficientMatrix mu s.1*A mu)) else 0 := by
  cases k using Fin.cases <;>
    simp [sourceHamiltonianJetMatrix,sourcePrincipalInverseJet,sourceLowerJet,
      sourceCoframeCoefficientJet]

theorem sourceNormalizedEnergySymbol_connection (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (A : Fin 4→SourceMatrix) :
    sourceNormalizedEnergySymbol p s (0,A,0)=SourceRealScalarFock.branches
      ((-Complex.I) • (Ring.inverse (principalMatrix s.1)*
        (∑mu : Fin 4,coefficientMatrix mu s.1*A mu))) := by
  rw [sourceNormalizedEnergySymbol_matrix p s _ valid]
  rw [show sourceHamiltonianJetMatrix s (0,A,0)=(fun k=>if k=0 then (-Complex.I) •
    (Ring.inverse (principalMatrix s.1)*(∑mu : Fin 4,coefficientMatrix mu s.1*A mu)) else 0) from
      funext (sourceHamiltonianJet_connection s A)]
  change realFourierMatrix (fun k=>if k=0 then (-Complex.I) •
    (Ring.inverse (principalMatrix s.1)*(∑mu : Fin 4,coefficientMatrix mu s.1*A mu)) else 0) p=_
  simp [realFourierMatrix,affineMatrix,SourceRealScalarFock.branches]

end LowEnergy.PreparationPhysicalNormalizedFullField

