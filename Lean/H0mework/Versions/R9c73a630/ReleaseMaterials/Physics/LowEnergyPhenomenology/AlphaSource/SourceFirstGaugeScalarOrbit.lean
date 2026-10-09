import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePoleGradedObservation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstGaugeBackgroundReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalResponseChargeGrading
open PreparationVacuumLowerClassical PreparationVacuumMixedFieldReturn
open PreparationVacuumNativeFieldInjection PreparationVacuumPhysicalConstraint114
open PreparationVacuumPhysicalElectromagneticDirection PreparationCoordinates
open SourceQuantumScalarChart SourceQuantumResidualGaugeSlice GaussNativeMatter
open StageNineHolonomicField StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum
open StageNineExteriorMotherLieRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair
open scoped Matrix BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
local instance : DecidableEq Quantum.Index:=Classical.decEq _

/-- These are the four actual source vacuum components, not chosen representation eigenstates. -/
def sourceFirstVacuumWeight (output input : Fin 2) : ℚ :=
  (!![-5/11,-3/11;1/11,3/11] : Matrix (Fin 2) (Fin 2) ℚ) output input

theorem sourceFirstVacuumWeight_generated (output input : Fin 2) :
    sourceFirstExteriorWeight (finiteGenerationScalarIndex output input)=sourceFirstVacuumWeight output input := by
  exact (show ∀ o i : Fin 2,sourceFirstExteriorWeight (finiteGenerationScalarIndex o i)=
    sourceFirstVacuumWeight o i from by decide +kernel) output input

theorem sourceFirstVacuumBasis_action (output input : Fin 2) :
    exteriorMotherLieAction 4 sourceFirstTemporalMother (finiteGenerationBreakingTensor output input)=
      ((sourceFirstVacuumWeight output input:ℂ)*Complex.I) • finiteGenerationBreakingTensor output input := by
  rw [finiteGenerationBreakingTensor,sourceFirstTemporal_exterior,sourceFirstVacuumWeight_generated]

private theorem vacuum_original :
    scalarCoordinateEquiv.symm vacuum=finiteGenerationJointBreakingScalar := by
  rw [vacuum,sourceGeneratedVacuumCoordinates,LinearEquiv.symm_apply_apply,positive_sourceGeneratedVacuumBase]

/-- The actual full-background scalar orbit of the source-generated temporal gauge direction. -/
def sourceFirstVacuumOrbit : Scalar := orbit sourceFirstTemporalLie

theorem sourceFirstVacuumOrbit_generated :
    scalarCoordinateEquiv.symm sourceFirstVacuumOrbit=
      ∑ output : Fin 2,∑ input : Fin 2,
        ((sourceFirstVacuumWeight output input:ℂ)*Complex.I) • finiteGenerationBreakingTensor output input := by
  change scalarCoordinateEquiv.symm (action vacuum sourceFirstTemporalLie)=_
  rw [scalarAction_mother,vacuum_original]
  change exteriorMotherLieAction 4 sourceFirstTemporalMother finiteGenerationJointBreakingScalar=_
  simp only [finiteGenerationJointBreakingScalar,map_sum,sourceFirstVacuumBasis_action]

private theorem scalar_index (a b c d : Fin 2) :
    finiteGenerationScalarIndex a b=finiteGenerationScalarIndex c d ↔ a=c ∧ b=d := by
  exact (show ∀ a b c d : Fin 2,finiteGenerationScalarIndex a b=finiteGenerationScalarIndex c d ↔
    a=c ∧ b=d from by decide +kernel) a b c d

/-- Every one of the original four scalar coordinates is read back from the generated orbit. -/
theorem sourceFirstVacuumOrbit_entry (output input : Fin 2) :
    (su7ExteriorBasis 4).repr (scalarCoordinateEquiv.symm sourceFirstVacuumOrbit)
      (finiteGenerationScalarIndex output input)=
        (sourceFirstVacuumWeight output input:ℂ)*Complex.I := by
  rw [sourceFirstVacuumOrbit_generated]
  simp only [map_sum,map_smul,
    finiteGenerationBreakingTensor]
  fin_cases output <;> fin_cases input <;> simp [scalar_index]

theorem sourceFirstVacuumOrbit_nonzero : sourceFirstVacuumOrbit≠0 := by
  intro zero
  have value:=sourceFirstVacuumOrbit_entry 0 0
  rw [zero,map_zero,map_zero,Finsupp.zero_apply] at value
  have imaginary:=congrArg Complex.im value
  norm_num [sourceFirstVacuumWeight,Complex.mul_im] at imaginary

private theorem orbit_seven : orbit (originalUnit 7)=orbit (originalUnit 6) := by
  have generated:=congrArg orbit sourceConstraintDirection_color
  simp only [map_smul,map_sub,sourceScalar_color_locked] at generated
  have difference : orbit (originalUnit 6)-orbit (originalUnit 7)=0 :=
    (smul_eq_zero.mp generated).resolve_left (by norm_num)
  exact (sub_eq_zero.mp difference).symm

private theorem temporal_raw : sourceFirstTemporalLie=
    (6/11:ℝ) • originalUnit 6+(-5/11:ℝ) • originalUnit 7+
      (3/11:ℝ) • originalUnit 10+(5/11:ℝ) • originalUnit 11 := by
  unfold sourceFirstTemporalLie sourceFirstGaugeConnection
  simp [sourceFirstGaugeCoefficients,sourceFirstTemporalCoefficients,Pi.single_apply,add_smul,Finset.sum_add_distrib]

/-- The same orbit is generated in the original nine scalar-gauge coordinates. -/
theorem sourceFirstVacuumOrbit_slots : sourceFirstVacuumOrbit=
    (1/11:ℝ) • orbit (originalUnit 6)+(3/11:ℝ) • orbit (originalUnit 10)+
      (5/11:ℝ) • orbit (originalUnit 11) := by
  rw [sourceFirstVacuumOrbit,temporal_raw]
  simp only [map_add,map_smul,orbit_seven]
  module

def sourceFirstScalarField : Field289 :=
  Pi.single (scalarSlot 4) (1/11)+Pi.single (scalarSlot 7) (3/11)+Pi.single (scalarSlot 8) (5/11)

private theorem scalar_single (j : Fin 9) (c : ℝ) :
    fieldScalar (Pi.single (scalarSlot j) c)=c • orbit (originalUnit (originalJColumns j)) := by
  have injective : Function.Injective scalarSlot := by
    intro a b same
    apply Fin.ext
    exact congrArg (fun k : Fin 289=>k.val) same
  simp [fieldScalar,Pi.single_apply,injective.eq_iff]

/-- This is the literal full289 scalar supplement, not a free field-realization witness. -/
theorem sourceFirstScalarField_return : fieldScalar sourceFirstScalarField=sourceFirstVacuumOrbit := by
  rw [sourceFirstScalarField,fieldScalar_add,fieldScalar_add,scalar_single,scalar_single,scalar_single,
    sourceFirstVacuumOrbit_slots]
  have four : originalJColumns 4=6 := by decide
  have seven : originalJColumns 7=10 := by decide
  have eight : originalJColumns 8=11 := by decide
  rw [four,seven,eight]

/-- The original repaired Yukawa action consumes the entire scalar orbit and full252 generator. -/
theorem sourceFirstScalarField_yukawa :
    PreparationVacuumGaugeSourceInjection.scalarLinear (fieldScalar sourceFirstScalarField)=
      Quantum.operatorMatrix sourceFirstTemporalGenerator*PreparationVacuumGaugeSourceInjection.scalarLinear vacuum-
        PreparationVacuumGaugeSourceInjection.scalarLinear vacuum*Quantum.operatorMatrix sourceFirstTemporalGenerator := by
  rw [sourceFirstScalarField_return,sourceFirstTemporal_native]
  exact originalScalar_commutator sourceFirstTemporalLie vacuum

end LowEnergy.PreparationPhysicalFirstGaugeBackgroundReturn
