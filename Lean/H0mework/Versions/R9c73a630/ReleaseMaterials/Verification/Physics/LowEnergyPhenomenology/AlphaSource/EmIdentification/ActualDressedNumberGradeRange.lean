import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourcePreparation
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationPhysicalTimePolynomial
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationYukawaUncutDomain

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberSector
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56 SourceQuantumScalarChart
open GaussCoreHilbert GaussCoreDifferential GaussCoreLabel GaussFockLabel GaussFockPair
open NativeHistoryGrade GaussYukawaGrade GaussYukawaCoefficient SourceFockRaising SourceGradeTransport
open PreparationVacuumUncutYukawa PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalHalfAxis
open CanonicalGradedSpatialSource
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance n2LabelFintype : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance n2QuantumIndexDecidable : DecidableEq LowEnergy.Quantum.Index:=Classical.decEq _
local instance n2ModeDecidable : DecidableEq Mode:=Classical.decEq _

/-- These are restrictions of the original occupation-grade projection on the same Hilbert space. -/
def numberTwoGrade (g : Fin 57) : H→L[ℂ]H:=NativeHistoryGrade.projection (2,g)

private theorem fiber_piece_number (N : Fin 505) (g : Fin 57) (psi : FockFiber) :
    SourceFockRaising.total (fiberCoordinates (fiberPiece (N,g) psi))=
      (N.val:ℂ) • fiberCoordinates (fiberPiece (N,g) psi) := by
  funext word
  rw [SourceFockRaising.total_apply]
  change (word.card:ℂ)*fiberPiece (N,g) psi word=(N.val:ℂ)*fiberPiece (N,g) psi word
  rw [fiberPiece_apply]
  by_cases same : NativeHistoryGrade.sourceLabel word=(N,g)
  · have hn:=congrArg (fun l : NativeHistoryGrade.Label=>l.1.val) same
    change word.card=N.val at hn
    simp only [if_pos same,hn]
  · simp only [if_neg same,mul_zero]

private theorem fiber_piece_grade (N : Fin 505) (g : Fin 57) (psi : FockFiber) :
    SourceFockRaising.grade target (fiberCoordinates (fiberPiece (N,g) psi))=
      (g.val:ℂ) • fiberCoordinates (fiberPiece (N,g) psi) := by
  funext word
  rw [SourceFockRaising.grade_apply]
  change (count target word:ℂ)*fiberPiece (N,g) psi word=(g.val:ℂ)*fiberPiece (N,g) psi word
  rw [fiberPiece_apply]
  by_cases same : NativeHistoryGrade.sourceLabel word=(N,g)
  · have hg:=congrArg (fun l : NativeHistoryGrade.Label=>l.2.val) same
    change count target word=g.val at hg
    simp only [if_pos same,hg]
  · simp only [if_neg same,mul_zero]

private theorem fiber_piece_fixed (N : Fin 505) (g : Fin 57) (psi : FockFiber)
    (number : SourceFockRaising.total (fiberCoordinates psi)=(N.val:ℂ) • fiberCoordinates psi)
    (grading : SourceFockRaising.grade target (fiberCoordinates psi)=(g.val:ℂ) • fiberCoordinates psi) :
    fiberPiece (N,g) psi=psi := by
  apply PiLp.ext
  intro word
  rw [fiberPiece_apply]
  by_cases zero : psi word=0
  · simp only [zero,ite_self]
  · have hn:=congrFun number word
    have hg:=congrFun grading word
    rw [SourceFockRaising.total_apply] at hn
    rw [SourceFockRaising.grade_apply] at hg
    change (word.card:ℂ)*psi word=(N.val:ℂ)*psi word at hn
    change (count target word:ℂ)*psi word=(g.val:ℂ)*psi word at hg
    have hn' : word.card=N.val:=Nat.cast_injective (R:=ℂ) (mul_right_cancel₀ zero hn)
    have hg' : count target word=g.val:=Nat.cast_injective (R:=ℂ) (mul_right_cancel₀ zero hg)
    rw [if_pos (Prod.ext (Fin.ext hn') (Fin.ext hg'))]

private theorem source_number_eigen (phi : Scalar) (N : ℕ) (psi : FockFiber)
    (number : SourceFockRaising.total (fiberCoordinates psi)=(N:ℂ) • fiberCoordinates psi) :
    SourceFockRaising.total (fiberCoordinates (sourceMap phi psi))=
      (N:ℂ) • fiberCoordinates (sourceMap phi psi) := by
  have paid:=LinearMap.congr_fun (SourceFockRaising.quantize_preserves_number (fullMatrix phi)) (fiberCoordinates psi)
  change SourceFockRaising.total (LowEnergy.Fermion.quantize (fullMatrix phi) (fiberCoordinates psi))=
    LowEnergy.Fermion.quantize (fullMatrix phi) (SourceFockRaising.total (fiberCoordinates psi)) at paid
  rw [number,map_smul] at paid
  exact paid

private theorem source_grade_eigen (phi : Scalar) (m : ℕ) (psi : FockFiber)
    (grading : SourceFockRaising.grade target (fiberCoordinates psi)=(m:ℂ) • fiberCoordinates psi) :
    SourceFockRaising.grade target (fiberCoordinates (sourceMap phi psi))=
      ((m+1:ℕ):ℂ) • fiberCoordinates (sourceMap phi psi) :=
  SourceFockRaising.raises_eigenstate target _ (GaussYukawaGrade.raw_grade phi) _ m grading

theorem original_yukawa_N2G0_range (phi : Scalar) (psi : FockFiber) :
    fiberPiece (2,1) (sourceMap phi (fiberPiece (2,0) psi))=sourceMap phi (fiberPiece (2,0) psi) := by
  exact fiber_piece_fixed 2 1 _
    (source_number_eigen phi 2 _ (by simpa using fiber_piece_number 2 0 psi))
    (by simpa using source_grade_eigen phi 0 _ (by simpa using fiber_piece_grade 2 0 psi))

theorem original_yukawa_N2G1_range (phi : Scalar) (psi : FockFiber) :
    fiberPiece (2,2) (sourceMap phi (fiberPiece (2,1) psi))=sourceMap phi (fiberPiece (2,1) psi) := by
  exact fiber_piece_fixed 2 2 _
    (source_number_eigen phi 2 _ (by simpa using fiber_piece_number 2 1 psi))
    (by simpa using source_grade_eigen phi 1 _ (by simpa using fiber_piece_grade 2 1 psi))

theorem original_yukawa_N2G2_zero (phi : Scalar) (psi : FockFiber) :
    sourceMap phi (fiberPiece (2,2) psi)=0 := by
  apply fiberCoordinates.injective
  have number:=source_number_eigen phi 2 _ (by simpa using fiber_piece_number 2 2 psi)
  have grading:=source_grade_eigen phi 2 _ (by simpa using fiber_piece_grade 2 2 psi)
  have zero:=SourceFockRaising.grade_above_particle_number target 2 3 (by omega) _ number
    (by simpa only [Nat.cast_ofNat,show (2+1:ℕ)=3 from rfl] using! grading)
  simpa only [map_zero] using zero

end LowEnergy.GaussComposite.ActualDressedNumberSector
