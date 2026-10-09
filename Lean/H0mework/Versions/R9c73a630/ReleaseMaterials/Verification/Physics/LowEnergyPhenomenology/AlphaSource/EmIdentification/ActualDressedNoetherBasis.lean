import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderBasis

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedConstraintRead
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

open PreparationVacuumFixedMomentumActionReturn


private theorem sample_basis (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (small : ‖h‖<ambientRadius a) :
    noetherSample f p a b (h,z)=∑j : Fin 289,(f j:ℂ) • noetherSample (fieldUnit j) p a b (h,z) := by
  by_cases inside : z∈tsupport a
  · have valid:=ambientRadius_valid a h z small.le inside
    change (pairRight z (a z))
        (quantizer (transportedRawSymbol f (sourceState z) (ambientState (h,z)) p) (b z))=
      ∑j : Fin 289,(f j:ℂ) • (pairRight z (a z))
        (quantizer (transportedRawSymbol (fieldUnit j) (sourceState z) (ambientState (h,z)) p) (b z))
    rw [source_reader_transport_basis f p (sourceState z) (ambientState (h,z)) valid,map_sum]
    simp only [sum_apply,smul_apply,map_sum,map_smul]
  · rw [noetherSample_zero f p a b h z inside]
    simp only [noetherSample_zero _ p a b h z inside,smul_zero,Finset.sum_const_zero]

/-- Compact original source tests pay all289 coefficients in one common chart neighbourhood. -/
theorem source_reader_form_basis (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (small : ‖h‖<ambientRadius a) :
    noetherForm f p a b h=∑j : Fin 289,(f j:ℂ) • noetherForm (fieldUnit j) p a b h := by
  have integrable (j : Fin 289) : Integrable (fun z=>noetherSample (fieldUnit j) p a b (h,z))
      GaussHistoryHilbert.configurationMeasure :=
    parameter_slice_integrable (noetherSample (fieldUnit j) p a b) (tsupport a) a.hasCompactSupport h
      (fun z=>noetherSample_near_smooth (fieldUnit j) p a b h z small)
      (noetherSample_zero (fieldUnit j) p a b)
  unfold noetherForm
  calc
    _=∫z,∑j : Fin 289,(f j:ℂ) • noetherSample (fieldUnit j) p a b (h,z)
        ∂GaussHistoryHilbert.configurationMeasure :=
      integral_congr_ae (Eventually.of_forall (fun z=>sample_basis f p a b h z small))
    _=_ := by
      simpa only [Pi.smul_apply,integral_smul] using
        (integral_finsetSum Finset.univ (fun j _=>(integrable j).smul (f j:ℂ)))

end LowEnergy.GaussComposite.ActualDressedConstraintRead
