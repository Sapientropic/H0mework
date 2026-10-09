import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeConstraint
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedJointGraph
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderContactBasis

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNativeQuantumWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open FullQuantum.StateGreen PreparationVacuumFixedMomentumActionReturn PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization SourceQuantumFockGauge PreparationVacuumNonlinearFieldCurve
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumActionFieldLift PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction
open PreparationVacuumLowerClassical PreparationVacuumTemporalCharge PreparationVacuumGaugeSourceInjection
open PreparationVacuumNoetherChart PreparationVacuumSourceActionJets PreparationVacuumFullFieldRiesz
open SourcePropagationNativeActionHessian GaussNativeMatter GaussCoreHilbert
open ActualDressedNativeConstraint ActualDressedNullNative ActualDressedLockedWard ActualDressedConstraintRead
open ActualDressedTemporalCurrent PreparationVacuumWeightedChargeActionWard
open Filter
open scoped Matrix BigOperators Topology Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local irreducible] nativeSourceColumn noetherReader nativeReader nativeReaderContact

/-- These are the actual source generator coordinates in the original twelve-dimensional Lie basis. -/
theorem native_color_generator (g : Fin 3) :
    nativeMatterGenerator (Fin.castAdd 6 g)=
      ∑a : Fin 12,gaugeColorRaw g a • nativePrimal (originalUnit a) :=by
  simp only [nativeMatterGenerator,Fin.addCases_left]
  change nativePrimal (show NativeLie from p286CoordinateEquiv (sourceColorP286Generator g))=_
  have source:=congrArg (fun a : NativeLie=>nativePrimal a)
    (raw_original_expansion (show NativeLie from p286CoordinateEquiv (sourceColorP286Generator g)))
  simp only [map_sum,map_smul,gaugeColor_source] at source
  exact source

/-- All four source parameter derivatives become their original gauge-current directions. -/
theorem native_color_gradient_state (g : Fin 3) (gradient : Fin 4→ℝ) (s : ActionState) :
    stateVariation (Fin.castAdd 6 g) 0 gradient s=
      ∑a : Fin 12,∑mu : Fin 4,(-gradient mu*gaugeColorRaw g a) • fieldDirection (gaugeField mu a) :=by
  simp only [stateVariation,zero_smul,zero_mul,gauge_direction,native_color_generator]
  apply Prod.ext
  · simp [Prod.fst_sum]
  apply Prod.ext
  · funext mu
    simp [Prod.snd_sum,Prod.fst_sum,Finset.sum_apply,smul_ite,Finset.smul_sum,smul_smul]
  · simp [Prod.snd_sum]

/-- The original fixed-momentum action produces all four color current insertions. -/
theorem native_color_gradient_action (g : Fin 3) (gradient : Fin 4→ℝ) (p : PhysicalMomentum)
    (base candidate : ActionState) :
    nativeNoether (Fin.castAdd 6 g) 0 gradient p base candidate=
      ∑a : Fin 12,∑mu : Fin 4,(-gradient mu*gaugeColorRaw g a) •
        sourceFixedMomentumGradient (gaugeField mu a) p base candidate :=by
  let source : ActionState→ₗ[ℝ] FullMatrix := -(4:ℂ) •
    ((LinearMap.mulLeft ℝ (sourceActionWeight base)).comp (fderiv ℝ (sourceSymbol p) candidate).toLinearMap)
  have generated:=congrArg source (native_color_gradient_state g gradient candidate)
  simp only [map_sum,map_smul] at generated
  exact generated

/-- The same original Legendre transport supplies the genuine Noether density, without changing its time weight. -/
theorem native_color_gradient_transport (g : Fin 3) (gradient : Fin 4→ℝ) (p : PhysicalMomentum)
    (base candidate : ActionState) (valid : candidate∈validStates) :
    nativeNoether (Fin.castAdd 6 g) 0 gradient p base candidate=
      ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) •
        transportedRawSymbol (gaugeField b.2 b.1) base candidate p :=by
  rw [native_color_gradient_action,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro mu _
  rw [sourceFixedMomentumGradient_raw (gaugeField mu a) p base candidate valid]
  exact RCLike.real_smul_eq_coe_smul (K:=ℂ) (-gradient mu*gaugeColorRaw g a)
    (transportedRawSymbol (gaugeField mu a) base candidate p)

end LowEnergy.GaussComposite.ActualDressedNativeQuantumWard
