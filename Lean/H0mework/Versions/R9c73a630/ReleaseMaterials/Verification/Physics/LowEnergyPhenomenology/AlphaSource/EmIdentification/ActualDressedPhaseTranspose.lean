import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseAmbient

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhaseConfiguration
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
open ActualEMOriginWard Stage9C.Material.SpinPair PreparationVacuumPhysicalModeContact


open GaussLiveMomentum GaussNativeMatter SourceQuantumScalarChart SourceQuantumResidualGaugeSlice
open StageNineP286GaugeConnectionVariationDensity
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumNativeFieldInjection
open PreparationVacuumActionDecomposition StageNineHolonomicField
open ActualEMCompleteOrbit

open PreparationVacuumElectricConstraint GaussNativeForm GaussMomentumAdjoint GaussFockPair CanonicalGradedCharge
private theorem dev_smooth : ContDiff ℝ ∞ phaseAmbientDeviation :=
  (variationL.contDiff.comp (contDiff_id.sub contDiff_const)).clm_apply contDiff_const

def phaseDevScalarCoefficient (j : ScalarIndex) (z : SourceCoordinateSlice) : ℝ :=
  ⟪scalarBasis j,(phaseAmbientDeviation z).1⟫_ℝ

def phaseDevElectricCoefficient (i : Fin 3) (j : LieIndex) (z : SourceCoordinateSlice) : ℝ :=
  ⟪lieBasis j,gaugeCoordinates (phaseAmbientDeviation z).2 i⟫_ℝ

private theorem dev_scalar_smooth (j : ScalarIndex) : ContDiff ℝ ∞ (phaseDevScalarCoefficient j) :=
  contDiff_const.inner ℝ dev_smooth.fst

private theorem dev_electric_smooth (i : Fin 3) (j : LieIndex) :
    ContDiff ℝ ∞ (phaseDevElectricCoefficient i j) :=
  contDiff_const.inner ℝ ((contDiff_apply ℝ NativeLie i).comp
    (gaugeCoordinates.toContinuousLinearEquiv.contDiff.comp dev_smooth.snd))

/-- Positive source coefficient construction on the original compact test domain. -/
def phaseDevAction : QuantumTest→ₗ[ℂ]QuantumTest :=
  (∑j : ScalarIndex,(GaussNativeForm.multiply (phaseDevScalarCoefficient j)
    (fun _=>(dev_scalar_smooth j).contDiffAt)).comp (covariantMomentum (scalarDirection j)))+
  (∑i : Fin 3,∑j : LieIndex,(GaussNativeForm.multiply (phaseDevElectricCoefficient i j)
    (fun _=>(dev_electric_smooth i j).contDiffAt)).comp (covariantMomentum (gaugeDirection i j)))

/-- Each original weighted momentum transpose acts after its actual variable coefficient; divergence, Jacobian and Number ordering are retained. -/
def phaseDevAdjoint : QuantumTest→ₗ[ℂ]QuantumTest :=
  (∑j : ScalarIndex,(GaussMomentumAdjoint.adjoint (scalarDirection j)).comp
    (GaussNativeForm.multiply (phaseDevScalarCoefficient j) (fun _=>(dev_scalar_smooth j).contDiffAt)))+
  (∑i : Fin 3,∑j : LieIndex,(GaussMomentumAdjoint.adjoint (gaugeDirection i j)).comp
    (GaussNativeForm.multiply (phaseDevElectricCoefficient i j) (fun _=>(dev_electric_smooth i j).contDiffAt)))

theorem phase_dev_action_actual (f : QuantumTest) (z : SourceCoordinateSlice) :
    phaseDevAction f z=covariantMomentum (phaseAmbientDeviation z) f z := by
  have expanded:=congrArg (pointMomentum z f) (ambient_expansion (phaseAmbientDeviation z))
  simp only [map_add,map_sum,map_smul] at expanded
  let ev : QuantumTest→ₗ[ℂ]FockFiber :=
    {toFun:=fun g=>g z,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
  change ev (phaseDevAction f)=_
  simp only [phaseDevAction,LinearMap.add_apply,LinearMap.sum_apply,LinearMap.comp_apply,map_add,map_sum]
  change (∑j : ScalarIndex,(phaseDevScalarCoefficient j z:ℂ) • covariantMomentum (scalarDirection j) f z)+
    (∑i : Fin 3,∑j : LieIndex,(phaseDevElectricCoefficient i j z:ℂ) • covariantMomentum (gaugeDirection i j) f z)=_
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),pointMomentum,LinearMap.coe_mk,AddHom.coe_mk] at expanded
  convert! expanded using 1

/-- The actual configuration derivative and the same native connection come from the original inverse, with no missing slice component assigned zero. -/
theorem phase_dev_configuration_current (f : QuantumTest) (z : physicalChart) :
    phaseDevAction f z.val=(-Complex.I) •
      (fderiv ℝ f z.val (0,-(inverseL z.val phaseAmbientReference).2)+
        nativeFock (sourcePhaseGaugeLie-(inverseL z.val phaseAmbientReference).1) (f z.val)) := by
  rw [phase_dev_action_actual,covariantMomentum_apply,phase_deviation_inverse]
  simp only [Prod.fst_sub,Prod.snd_sub,zero_sub]

/-- The same full scalar+electric Gauss orbit is the deviation plus its original fixed reference tangent. -/
theorem phase_dev_reference_balance :
    phaseDevAction+covariantMomentum phaseAmbientReference=orbitAction sourcePhaseGaugeLie := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change phaseDevAction f z+covariantMomentum phaseAmbientReference f z=orbitAction sourcePhaseGaugeLie f z
  rw [phase_dev_action_actual,orbitAction_apply]
  have generated:=congrArg (pointMomentum z f) (phase_deviation_ambient z)
  simp only [map_sub] at generated
  change covariantMomentum (phaseAmbientDeviation z) f z=
    covariantMomentum (orbitMap z sourcePhaseGaugeLie) f z-covariantMomentum phaseAmbientReference f z at generated
  rw [generated]
  abel

theorem phase_dev_gauss_return :
    phaseDevAction+covariantMomentum phaseAmbientReference= -chargeAction sourcePhaseGaugeLie := by
  rw [phase_dev_reference_balance,original_gauss_constraint]

/-- This is the actual Hilbert transpose of the source-generated deviation action, derived by the original weighted integration by parts. -/
theorem phase_dev_weighted_pair (f g : QuantumTest) :
    sourcePair f (phaseDevAction g)=sourcePair (phaseDevAdjoint f) g := by
  have term (v : Ambient) (c : SourceCoordinateSlice→ℝ)
      (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
      inner ℂ (embed f) (embed (GaussNativeForm.multiply c hc (covariantMomentum v g)))=
        inner ℂ (embed (GaussMomentumAdjoint.adjoint v (GaussNativeForm.multiply c hc f))) (embed g) :=
    (multiply_pair c hc f (covariantMomentum v g)).trans
      (GaussMomentumAdjoint.momentum_pair v (GaussNativeForm.multiply c hc f) g)
  simp only [phaseDevAction,phaseDevAdjoint,LinearMap.add_apply,LinearMap.sum_apply,LinearMap.comp_apply]
  simp only [sourcePair,map_add,map_sum,inner_add_right,inner_add_left,inner_sum,sum_inner]
  simp_rw [term]

/-- The complete transpose balance keeps the fixed-reference momentum in its correct weighted branch. -/
theorem phase_dev_weighted_balance (f g : QuantumTest) :
    sourcePair (phaseDevAdjoint f+GaussMomentumAdjoint.adjoint phaseAmbientReference f) g=
      sourcePair (orbitAdjoint sourcePhaseGaugeLie f) g := by
  have left:=(phase_dev_weighted_pair f g).symm
  have right:=(GaussMomentumAdjoint.momentum_pair phaseAmbientReference f g).symm
  have full:=orbit_adjoint_pair sourcePhaseGaugeLie f g
  have same:=congrArg (fun A : QuantumTest→ₗ[ℂ]QuantumTest=>sourcePair f (A g)) phase_dev_reference_balance
  change sourcePair f (phaseDevAction g+covariantMomentum phaseAmbientReference g)=_ at same
  simp only [sourcePair,map_add,inner_add_left,inner_add_right] at left right full same ⊢
  rw [left,right,same,full]

end LowEnergy.GaussComposite.ActualDressedPhaseConfiguration
