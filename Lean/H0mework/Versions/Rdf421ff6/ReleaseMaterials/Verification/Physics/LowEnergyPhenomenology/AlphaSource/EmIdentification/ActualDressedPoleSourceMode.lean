import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedVisibleFullMode
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualDressedVisiblePoleOwn.ActualDressedSourceVisiblePoles

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPoleWardMode
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedCorrectedElectronRead
open ActualDressedUniformMaterialCoefficients LowEnergy.GaussComposite.ActualDressedVisiblePole
open LowEnergy.ActualDressedVisiblePole LowEnergy.ActualDressedPoleWardMode
open PreparationVacuumPhysicalFeedback ActualCompositeFieldCurrent
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonCurrentNumerator commonDeterminant commonDenominator
  ActualCompositeFieldCurrent.compositeCurrent correctedGreen correctedProbeResponse

def sourceSheetPencil (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ[X] := (commonClearedPencil event n).map (sheetSlice eps sigma)

/-- One full multivariate source vector precedes both the clock restriction and every observer. -/
def sourceCommonVector (event : DressedEvent) (n ps : PhysicalMomentum) (sL sR : CompositeLeg) :
    Fin 289 → Parameters := commonDenominator event n •
      ((commonClearedPencil event n).adjugate*ᵥfun i => MvPolynomial.C
        (ActualCompositeFieldCurrent.compositeCurrent ps sL sR i))

def sourceSheetVector (event : DressedEvent) (eps sigma : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) : Fin 289 → ℂ[X] :=
  fun i => sheetSlice eps sigma (sourceCommonVector event n ps sL sR i)

def actualVisibleMode (event : DressedEvent) (eps sigma : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) (a : ℂ) : Fin 289 → ℂ :=
  sourcePoleMode (sourceSheetVector event eps sigma n ps sL sR) (sheetDeterminant event eps sigma n) a

private theorem sheet_constant (eps sigma : ℝ) (c : ℂ) :
    sheetSlice eps sigma (MvPolynomial.C c)=C c := by simp [sheetSlice]

private theorem observer_numerator {α ι : Type*} [CommRing α] [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι α) (fd fs : ι → α) (d : α) :
    dotProduct fd (d • (H.adjugate*ᵥfs))=d*dotProduct fd (H.adjugate*ᵥfs) := by
  rw [dotProduct_smul, smul_eq_mul]

private theorem mapped_observer {ι : Type*} [Fintype ι] (f : Parameters →+* ℂ[X])
    (constant : ∀c : ℂ, f (MvPolynomial.C c)=C c) (fd : ι → ℂ) (V : ι → Parameters) :
    dotProduct (fun i => C (fd i)) (fun i => f (V i))=
      f (dotProduct (fun i => MvPolynomial.C (fd i)) V) := by
  simp only [dotProduct, map_sum, map_mul, constant]

private theorem adjugate_equation {α ι : Type*} [CommRing α] [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι α) (d : α) (f : ι → α) :
    H*ᵥ(d • (H.adjugate*ᵥf))=H.det • (d • f) := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  exact smul_comm _ _ _

private theorem mapped_equation {α β ι : Type*} [CommRing α] [CommRing β] [Fintype ι]
    (f : α →+* β) (H : Matrix ι ι α) (V F : ι → α) (D : α) (paid : H*ᵥV=D • F) :
    H.map f*ᵥ(fun i => f (V i))=f D • (fun i => f (F i)) := by
  have mapped := congrArg (fun v : ι → α => fun i => f (v i)) paid
  funext i
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
    Pi.smul_apply, smul_eq_mul] using congrFun mapped i

theorem actual_common_observer_vector (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    dotProduct (fun i => MvPolynomial.C (ActualCompositeFieldCurrent.compositeCurrent pd dL dR i))
      (sourceCommonVector event n ps sL sR)=commonCurrentNumerator event n pd ps dL dR sL sR := by
  unfold sourceCommonVector commonCurrentNumerator
  exact observer_numerator _ _ _ _

theorem actual_sheet_observer_numerator (event : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    dotProduct (fun i => C (ActualCompositeFieldCurrent.compositeCurrent pd dL dR i))
      (sourceSheetVector event eps sigma n ps sL sR)=
        sheetCurrentNumerator event eps sigma n pd ps dL dR sL sR := by
  have paid := mapped_observer (sheetSlice eps sigma) (sheet_constant eps sigma)
    (ActualCompositeFieldCurrent.compositeCurrent pd dL dR) (sourceCommonVector event n ps sL sR)
  rw [actual_common_observer_vector] at paid
  exact paid

theorem actual_common_full_equation (event : DressedEvent) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) :
    commonClearedPencil event n*ᵥsourceCommonVector event n ps sL sR=
      commonDeterminant event n • (commonDenominator event n •
        fun i => MvPolynomial.C (ActualCompositeFieldCurrent.compositeCurrent ps sL sR i)) := by
  unfold sourceCommonVector commonDeterminant
  exact adjugate_equation _ _ _

theorem actual_sheet_full_equation (event : DressedEvent) (eps sigma : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) :
    sourceSheetPencil event eps sigma n*ᵥsourceSheetVector event eps sigma n ps sL sR=
      sheetDeterminant event eps sigma n •
        (fun i => sheetSlice eps sigma (commonDenominator event n •
          (fun j => MvPolynomial.C (ActualCompositeFieldCurrent.compositeCurrent ps sL sR j)) i)) :=
  mapped_equation (sheetSlice eps sigma) _ _ _ _ (actual_common_full_equation event n ps sL sR)

theorem actual_visible_full_mode (event : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (a : ℂ)
    (root : a ∈ visibleRoots (sheetReadFraction event eps sigma n pd ps dL dR sL sR)) :
    actualVisibleMode event eps sigma n ps sL sR a ≠ 0 ∧
      (sourceSheetPencil event eps sigma n).map (Polynomial.eval a)*ᵥ
        actualVisibleMode event eps sigma n ps sL sR a=0 := by
  have observed : a ∈ visibleRoots (readFraction
      (dotProduct (fun i => C (ActualCompositeFieldCurrent.compositeCurrent pd dL dR i))
        (sourceSheetVector event eps sigma n ps sL sR)) (sheetDeterminant event eps sigma n)) := by
    rw [actual_sheet_observer_numerator]
    exact root
  exact ⟨source_pole_mode_nonzero _ _ _ _ observed,
    source_visible_full_kernel _ _ _ _ _ _ (actual_sheet_full_equation event eps sigma n ps sL sR) observed⟩

end LowEnergy.GaussComposite.ActualDressedPoleWardMode
