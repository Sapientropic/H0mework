import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPoleWardReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMTensorClock
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualEMResponseSplit ActualEMCurrentSplit ActualEMCarrierOwn ActualCompositeFieldCurrent
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonDenominator commonDeterminant
  correctedGreen emInsertion emResponseTensor

/-- Complete original gauge insertion, before any current or frequency restriction. -/
def commonEMTensorNumerator (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) Parameters :=
  fun mu nu => commonDenominator event n *
    dotProduct (fun i => MvPolynomial.C (emInsertion i mu))
      ((commonClearedPencil event n).adjugate*ᵥfun j => MvPolynomial.C (emInsertion j nu))

def correctedEMTensor (event : DressedEvent) (eps s sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ := emResponseTensor (correctedGreen event eps s sigma n)

private theorem map_adjugate_read {α β ι : Type*} [CommRing α] [CommRing β]
    [Fintype ι] [DecidableEq ι] (f : α →+* β) (H : Matrix ι ι α) (fd fs : ι → α) (d : α) :
    f (d*dotProduct fd (H.adjugate*ᵥfs))=
      f d*dotProduct (fun i => f (fd i)) ((H.map f).adjugate*ᵥfun i => f (fs i)) := by
  have mapped : H.adjugate.map f=(H.map f).adjugate := f.map_adjugate H
  rw [map_mul, ← mapped]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]

private theorem tensor_entry {ι κ α : Type*} [Fintype ι] [Fintype κ] [CommRing α]
    (E : Matrix ι κ α) (G : Matrix ι ι α) (mu nu : κ) :
    (E.transpose*G*E) mu nu=dotProduct (fun i => E i mu) (G*ᵥfun j => E j nu) := by
  rw [Matrix.mul_assoc]
  rfl

theorem common_em_tensor_numerator_eval (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) :
    MvPolynomial.eval (irValues eps sigma s) (commonEMTensorNumerator event n mu nu)=
      MvPolynomial.eval (irValues eps sigma s) (commonDenominator event n)*
        dotProduct (fun i => emInsertion i mu)
          (((commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma s))).adjugate*ᵥ
            fun j => emInsertion j nu) := by
  unfold commonEMTensorNumerator
  have paid := map_adjugate_read (MvPolynomial.eval (irValues eps sigma s))
    (commonClearedPencil event n) (fun i => MvPolynomial.C (emInsertion i mu))
    (fun j => MvPolynomial.C (emInsertion j nu)) (commonDenominator event n)
  simpa only [MvPolynomial.eval_C] using paid

/-- This generated tensor is a restriction of the same complete corrected response, with no branch-speed normalization. -/
theorem actual_corrected_em_tensor_clear (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) (regular : correctedDet event eps s sigma n≠0) :
    MvPolynomial.eval (irValues eps sigma s) (commonDeterminant event n) •
      correctedEMTensor event eps s sigma n=
        (commonEMTensorNumerator event n).map (MvPolynomial.eval (irValues eps sigma s)) := by
  ext mu nu
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, common_em_tensor_numerator_eval]
  unfold correctedEMTensor emResponseTensor
  rw [tensor_entry, common_determinant_eval]
  exact adjugate_full_read _ _ _ _ _ _
    (actual_common_ir_pencil_clear event n eps sigma s positive)
    (actual_corrected_green_inverse event eps s sigma n positive regular).1

def emSheetNumerator (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ[X] := (commonEMTensorNumerator event n).map (sheetSlice eps sigma)

def emSheetFraction (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) (RatFunc ℂ) :=
  fun mu nu => readFraction (emSheetNumerator event eps sigma n mu nu) (sheetDeterminant event eps sigma n)

/-- Raw determinant zero has no spectral packet; otherwise all sixteen independent canonical denominators are retained. -/
def sourceEMTensorPoles (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) :
    Option (Matrix (Fin 4) (Fin 4) (Multiset (ℂ × ℕ × List ℂ))) := by
  classical
  exact if sheetDeterminant event eps sigma n=0 then none else some (fun mu nu =>
    let R := emSheetFraction event eps sigma n mu nu
    (visibleRoots R).map (fun a =>
      (a,poleOrder R a,List.ofFn (fun k : Fin (poleOrder R a) => principalCoefficient R a k.val))))

theorem actual_corrected_em_tensor_canonical (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) (regular : correctedDet event eps s sigma n≠0)
    (mu nu : Fin 4) :
    correctedEMTensor event eps s sigma n mu nu=
      (emSheetFraction event eps sigma n mu nu).num.eval (s : ℂ)/
        (emSheetFraction event eps sigma n mu nu).denom.eval (s : ℂ) := by
  have determinant := actual_common_determinant_nonzero event eps sigma s n positive regular
  have read := congrFun (congrFun (actual_corrected_em_tensor_clear event eps sigma s n positive regular) mu) nu
  have raw : correctedEMTensor event eps s sigma n mu nu=
      MvPolynomial.eval (irValues eps sigma s) (commonEMTensorNumerator event n mu nu)/
        MvPolynomial.eval (irValues eps sigma s) (commonDeterminant event n) := by
    apply (eq_div_iff determinant).mpr
    exact (mul_comm _ _).trans read
  have sheetRegular : (sheetDeterminant event eps sigma n).eval (s : ℂ)≠0 := by
    rw [sheetDeterminant, sheet_slice_eval]
    exact determinant
  refine raw.trans ?_
  rw [← sheet_slice_eval, ← sheet_slice_eval]
  exact (reduced_read_at_regular _ _ (s : ℂ) sheetRegular).symm

/-- The actual complete probe read retains both mixed pieces and its full non-EM residual around this same generated tensor. -/
theorem actual_probe_tensor_four_parts (event : DressedEvent) (eps sigma s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    let G := correctedGreen event eps s sigma n
    let fd := ActualCompositeFieldCurrent.compositeCurrent pd dL dR
    let fs := ActualCompositeFieldCurrent.compositeCurrent ps sL sR
    correctedProbeRead event eps s sigma n pd ps dL dR sL sR=
      dotProduct (emCoordinateCurrent fd) (correctedEMTensor event eps s sigma n*ᵥemCoordinateCurrent fs)+
      emCurrentObservation G (emCurrentForce fd) (emCurrentResidual fs)+
      emCurrentObservation G (emCurrentResidual fd) (emCurrentForce fs)+
      emCurrentObservation G (emCurrentResidual fd) (emCurrentResidual fs) :=
  actual_corrected_probe_four_parts event eps s sigma n pd ps dL dR sL sR

end LowEnergy.GaussComposite.ActualDressedEMTensorClock
