import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGaugeBand

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalNumberOneRead
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineDiracDualYukawaSpinJurisdiction SU7MotherLieAlgebra
open PreparationVacuumGaugeSourceInjection PreparationVacuumSourceFieldFamily
open PreparationVacuumActualFieldQuantization PreparationVacuumActionFieldLift
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates CanonicalGradedSpatialSource
open GaussFockLabel GaussNativeMatter GaussYukawaGrade GaussHistoryHilbert
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open GaussCoreHilbert GaussCoreDifferential GaussCoreLabel NativeHistoryGrade
open PreparationVacuumSourceActionJets PreparationVacuumRawJointFeedback PreparationVacuumFullFieldRiesz
open PreparationVacuumPhysicalZeroRead PreparationVacuumPhysicalHalfAxis
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumElectromagneticIdentity
open CanonicalGradedCurrent PreparationVacuumPhysicalFeedback SourceFiniteUnitary
open MeasureTheory Set
open scoped Matrix BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussYukawaCoefficient GaussYukawaGrade SourceFockRaising SourceGradeTransport

def sourceExcitedLabel : NativeHistoryGrade.Label := (1,1)
def sourceExcitedProjection : GaussCoreHilbert.H→L[ℂ] GaussCoreHilbert.H :=
  NativeHistoryGrade.projection sourceExcitedLabel

private theorem piece_number (g : Fin 57) (psi : FockFiber) :
    SourceFockRaising.total (fiberCoordinates (fiberPiece (1,g) psi))=
      (1 : ℂ) • fiberCoordinates (fiberPiece (1,g) psi) := by
  funext word
  rw [SourceFockRaising.total_apply]
  change (word.card : ℂ)*fiberPiece (1,g) psi word=(1 : ℂ)*fiberPiece (1,g) psi word
  rw [fiberPiece_apply]
  by_cases same : NativeHistoryGrade.sourceLabel word=(1,g)
  · have hn := congrArg (fun l : NativeHistoryGrade.Label=>l.1.val) same
    change word.card=1 at hn
    simp only [if_pos same,hn,Nat.cast_one]
  · simp only [if_neg same,mul_zero]

private theorem piece_grade (g : Fin 57) (psi : FockFiber) :
    SourceFockRaising.grade target (fiberCoordinates (fiberPiece (1,g) psi))=
      (g.val : ℂ) • fiberCoordinates (fiberPiece (1,g) psi) := by
  funext word
  rw [SourceFockRaising.grade_apply]
  change (count target word : ℂ)*fiberPiece (1,g) psi word=(g.val : ℂ)*fiberPiece (1,g) psi word
  rw [fiberPiece_apply]
  by_cases same : NativeHistoryGrade.sourceLabel word=(1,g)
  · have hg := congrArg (fun l : NativeHistoryGrade.Label=>l.2.val) same
    change count target word=g.val at hg
    simp only [if_pos same,hg]
  · simp only [if_neg same,mul_zero]

private theorem piece_fixed (g : Fin 57) (psi : FockFiber)
    (number : SourceFockRaising.total (fiberCoordinates psi)=(1 : ℂ) • fiberCoordinates psi)
    (grading : SourceFockRaising.grade target (fiberCoordinates psi)=(g.val : ℂ) • fiberCoordinates psi) :
    fiberPiece (1,g) psi=psi := by
  apply PiLp.ext
  intro word
  rw [fiberPiece_apply]
  by_cases zero : psi word=0
  · simp only [zero,ite_self]
  · have hn := congrFun number word
    have hg := congrFun grading word
    rw [SourceFockRaising.total_apply] at hn
    change (word.card : ℂ)*psi word=(1 : ℂ)*psi word at hn
    rw [SourceFockRaising.grade_apply] at hg
    change (count target word : ℂ)*psi word=(g.val : ℂ)*psi word at hg
    have hn' : word.card=1 := by
      apply Nat.cast_injective (R:=ℂ)
      simpa only [Nat.cast_one] using mul_right_cancel₀ zero hn
    have hg' : count target word=g.val := by
      exact Nat.cast_injective (R:=ℂ) (mul_right_cancel₀ zero hg)
    have label : NativeHistoryGrade.sourceLabel word=(1,g):=
      Prod.ext (Fin.ext hn') (Fin.ext hg')
    rw [if_pos label]

private theorem sourceMap_number_eigen (phi : Scalar) (x : FockFiber)
    (number : SourceFockRaising.total (fiberCoordinates x)=(1 : ℂ) • fiberCoordinates x) :
    SourceFockRaising.total (fiberCoordinates (sourceMap phi x))=
      (1 : ℂ) • fiberCoordinates (sourceMap phi x) := by
  have h := LinearMap.congr_fun (SourceFockRaising.quantize_preserves_number (fullMatrix phi)) (fiberCoordinates x)
  change SourceFockRaising.total (SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize (fullMatrix phi) (fiberCoordinates x))=
    SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize (fullMatrix phi) (SourceFockRaising.total (fiberCoordinates x)) at h
  rw [number,map_smul] at h
  exact h

private theorem sourceMap_grade_eigen (phi : Scalar) (x : FockFiber) (g : ℕ)
    (grading : SourceFockRaising.grade target (fiberCoordinates x)=(g : ℂ) • fiberCoordinates x) :
    SourceFockRaising.grade target (fiberCoordinates (sourceMap phi x))=
      ((g+1 : ℕ) : ℂ) • fiberCoordinates (sourceMap phi x) :=
  SourceFockRaising.raises_eigenstate target _ (GaussYukawaGrade.raw_grade phi) _ g grading

theorem sourceMap_N1G0_range (phi : Scalar) (psi : FockFiber) :
    fiberPiece sourceExcitedLabel (sourceMap phi (fiberPiece CanonicalGradedCurrent.sourceLabel psi))=
      sourceMap phi (fiberPiece CanonicalGradedCurrent.sourceLabel psi) := by
  exact piece_fixed 1 _ (sourceMap_number_eigen phi _ (piece_number 0 psi))
    (by simpa only [CanonicalGradedCurrent.sourceLabel,Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one,zero_add] using sourceMap_grade_eigen phi _ 0 (piece_grade 0 psi))

theorem sourceMap_N1G1_zero (phi : Scalar) (psi : FockFiber) :
    sourceMap phi (fiberPiece sourceExcitedLabel psi)=0 := by
  apply fiberCoordinates.injective
  have number := sourceMap_number_eigen phi _ (piece_number 1 psi)
  have grading := sourceMap_grade_eigen phi _ 1 (piece_grade 1 psi)
  have zero := SourceFockRaising.grade_above_particle_number target 1 2 (by omega) _ (by simpa only [Nat.cast_one] using number) (by simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,one_add_one_eq_two] using grading)
  simpa only [sourceExcitedLabel,map_zero] using zero



end LowEnergy.PreparationVacuumPhysicalNumberOneRead
