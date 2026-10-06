import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrincipalHistory
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeGradeProjection

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalGradeZeroRead
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open PreparationVacuumElectromagneticIdentity PreparationVacuumMovingPoleGaussReturn
open GaussCoreHilbert GaussFockLift GaussComposite CanonicalGradedCharge
open GaussYukawaGrade NativeHistoryGrade
open QuantizationCheck.Fermion
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local irreducible] actualMovingPolePreparation sourcePolePrepared

private theorem embedded_six_zero (values : Source.Index→ℂ) :
    MixedSymbol.degreeSix (Stage9DEF.Compatibility.embed values)=0:=by
  funext spin
  change ((∑ state : Fin 2,values (spin,state) • sourceColorDoubletMatter state).1,0,0)=(0,0,0)
  simp [sourceColorDoubletMatter]

theorem sourcePolePrimalCoordinates_six (momentum : CanonicalGradedSpatialSource.PhysicalMomentum)
    (state : RestStateIndex) (index : Quantum.Index) (six : isSix index) :
    sourcePolePrimalCoordinates momentum state index=0:=by
  have source : MixedSymbol.degreeSix (actualMovingPolePreparation momentum state
      (Stage9DEF.Compatibility.embed (Stage9DEF.Source.vector 0)))=0:=by
    rw [actualMovingPole_source]
    exact embedded_six_zero _
  have generated:=congrArg (fun v=>Quantum.coordinates v index) source
  rw [coordinates_degreeSix] at generated
  simpa only [if_pos six,one_mul,map_zero,Pi.zero_apply,sourcePolePrimalCoordinates] using generated

theorem sourcePoleCoordinates_target (momentum : CanonicalGradedSpatialSource.PhysicalMomentum)
    (state : RestStateIndex) (index : Mode) (inside : index∈target) :
    sourcePoleCoordinates momentum state index=0:=by
  cases index with
  | inl i=>exact sourcePolePrimalCoordinates_six momentum state i (mem_target_left i |>.mp inside)
  | inr i=>rfl

theorem sourcePoleFiber_gradeZero (momentum : CanonicalGradedSpatialSource.PhysicalMomentum)
    (state : RestStateIndex) : fiberGrade (sourcePoleFiber momentum state)=0:=by
  apply fiberCoordinates.injective
  rw [fiber_coordinates_grade,map_zero]
  change SourceFockRaising.grade target (oneParticle (sourcePoleCoordinates momentum state))=0
  funext word
  rw [SourceFockRaising.grade_apply]
  by_cases singleton : ∃i : Mode,word={i}
  · obtain ⟨i,rfl⟩:=singleton
    rw [oneParticle_singleton]
    by_cases inside : i∈target
    · rw [sourcePoleCoordinates_target momentum state i inside,mul_zero]
      rfl
    · simp [inside]
  · rw [oneParticle_eq_zero_of_not_singleton _ _ (fun i same=>singleton ⟨i,same⟩),mul_zero]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem sourcePolePrepared_gradeZero (epsilon : ℝ) (precision : 0<epsilon)
    (momentum : CanonicalGradedSpatialSource.PhysicalMomentum) (state : RestStateIndex) :
    GaussYukawaGrade.grade (sourcePolePrepared epsilon precision momentum state)=0:=by
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  apply PiLp.ext
  intro word
  have coordinate:=congrArg (fun f : FockFiber=>f word) (sourcePoleFiber_gradeZero momentum state)
  simp only [GaussYukawaGrade.fiberGrade,GaussFockLabel.blockWeight_apply,PiLp.zero_apply] at coordinate
  simp only [map_zero,PiLp.zero_apply,GaussHalfDensity.fockHalfDensityEquiv,
    LinearIsometryEquiv.piLpCongrRight_apply]
  change GaussHalfDensity.halfDensityEquiv word.card
      ((GaussYukawaGrade.grade (sourcePolePrepared epsilon precision momentum state)) word)=0
  rw [source_grade_apply,map_smul]
  change ((NativeHistoryGrade.sourceGrade word).val:ℂ) •
    (GaussHalfDensity.fockHalfDensityEquiv (sourcePolePrepared epsilon precision momentum state) word)=0
  rw [sourcePolePrepared_coordinates,smul_smul]
  change (((NativeHistoryGrade.sourceLabel word).2.val:ℂ)*sourcePoleFiber momentum state word) •
    sourcePoleBase epsilon precision=0
  rw [coordinate,zero_smul]

theorem sourcePolePrepared_gradeZero_fixed (epsilon : ℝ) (precision : 0<epsilon)
    (momentum : CanonicalGradedSpatialSource.PhysicalMomentum) (state : RestStateIndex) :
    gradeZeroProjection (sourcePolePrepared epsilon precision momentum state)=
      sourcePolePrepared epsilon precision momentum state:=
  grade_zero_fixed _ (sourcePolePrepared_gradeZero epsilon precision momentum state)

private theorem sourcePoleFiber_off_label (momentum : CanonicalGradedSpatialSource.PhysicalMomentum)
    (state : RestStateIndex) (word : Occupation)
    (off : NativeHistoryGrade.sourceLabel word≠CanonicalGradedCurrent.sourceLabel) :
    sourcePoleFiber momentum state word=0:=by
  change oneParticle (sourcePoleCoordinates momentum state) word=0
  by_cases singleton : ∃i : Mode,word={i}
  · obtain ⟨i,rfl⟩:=singleton
    rw [oneParticle_singleton]
    by_cases inside : i∈target
    · exact sourcePoleCoordinates_target momentum state i inside
    · exfalso
      apply off
      simp [NativeHistoryGrade.sourceLabel,NativeHistoryGrade.sourceNumber,
        NativeHistoryGrade.sourceGrade,CanonicalGradedCurrent.sourceLabel,SourceGradeTransport.count,inside]
  · exact oneParticle_eq_zero_of_not_singleton _ _ (fun i same=>singleton ⟨i,same⟩)

theorem sourcePolePrepared_sourceProjection (epsilon : ℝ) (precision : 0<epsilon)
    (momentum : CanonicalGradedSpatialSource.PhysicalMomentum) (state : RestStateIndex) :
    CanonicalGradedCurrent.sourceProjection (sourcePolePrepared epsilon precision momentum state)=
      sourcePolePrepared epsilon precision momentum state:=by
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  apply PiLp.ext
  intro word
  change GaussHalfDensity.halfDensityEquiv word.card
    ((NativeHistoryGrade.projection CanonicalGradedCurrent.sourceLabel
      (sourcePolePrepared epsilon precision momentum state)) word)=_
  rw [NativeHistoryGrade.projection_apply]
  split_ifs with inside
  · rfl
  · simp only [map_zero]
    rw [sourcePolePrepared_coordinates,sourcePoleFiber_off_label momentum state word inside,zero_smul]

end LowEnergy.PreparationVacuumPhysicalGradeZeroRead
