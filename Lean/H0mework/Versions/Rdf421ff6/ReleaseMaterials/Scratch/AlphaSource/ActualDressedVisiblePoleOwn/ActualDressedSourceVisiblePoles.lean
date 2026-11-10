import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonCurrentNumerator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedVisiblePole
open Polynomial ActualDressedUniformMaterialCoefficients ActualDressedCorrectedElectronRead
open ActualDressedCorrectedGreen ActualDressedFullCoulomb ActualCompositeFieldCurrent
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn LowEnergy.ActualDressedVisiblePole
open scoped Matrix
attribute [local irreducible] commonCurrentNumerator commonDeterminant correctedProbeRead

def sheetSlice (eps sigma : ℝ) : Parameters →+* ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 3 => if i=0 then Polynomial.C (eps : ℂ) else if i=1 then Polynomial.C (sigma : ℂ) else Polynomial.X)

theorem sheet_slice_eval (eps sigma s : ℝ) (P : Parameters) :
    (sheetSlice eps sigma P).eval (s : ℂ) = MvPolynomial.eval (irValues eps sigma s) P := by
  have hom : (Polynomial.evalRingHom (s : ℂ)).comp (sheetSlice eps sigma) =
      MvPolynomial.eval (irValues eps sigma s) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [sheetSlice]
    · intro i
      simp [sheetSlice, irValues]
      split_ifs <;> simp_all
  exact congrArg (fun f : Parameters →+* ℂ => f P) hom

def sheetDeterminant (background : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) : ℂ[X] :=
  sheetSlice eps sigma (commonDeterminant background n)
def sheetCurrentNumerator (background : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ[X] :=
  sheetSlice eps sigma (commonCurrentNumerator background n pd ps dL dR sL sR)

def sheetReadDisposition (background : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    ReadDisposition (sheetCurrentNumerator background eps sigma n pd ps dL dR sL sR)
      (sheetDeterminant background eps sigma n) := sourceReadDisposition _ _

def sheetVisiblePoles (background : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Option (Multiset ℂ) :=
  sourcePoleRoots (sheetCurrentNumerator background eps sigma n pd ps dL dR sL sR)
    (sheetDeterminant background eps sigma n)

def sheetReadFraction (background : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : RatFunc ℂ :=
  readFraction (sheetCurrentNumerator background eps sigma n pd ps dL dR sL sR)
    (sheetDeterminant background eps sigma n)

def sheetPoleData (background : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Option (Multiset (ℂ × ℕ × List ℂ)) :=
  (sheetVisiblePoles background eps sigma n pd ps dL dR sL sR).map (fun roots =>
    roots.map (fun a =>
      let R := sheetReadFraction background eps sigma n pd ps dL dR sL sR
      (a, poleOrder R a, List.ofFn (fun k : Fin (poleOrder R a) => principalCoefficient R a k.val))))

def sheetPoleResidue (background : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (a : ℂ) : ℂ :=
  poleResidue (sheetReadFraction background eps sigma n pd ps dL dR sL sR) a

theorem singular_common_sheet_no_chart (background : DressedEvent) (eps sigma : ℝ)
    (n : PhysicalMomentum) (zero : sheetDeterminant background eps sigma n = 0) (s : ℝ) :
    MvPolynomial.eval (irValues eps sigma s) (commonDeterminant background n) = 0 := by
  rw [← sheet_slice_eval]
  simpa only [sheetDeterminant, eval_zero] using congrArg (Polynomial.eval (s : ℂ)) zero

theorem singular_common_sheet_no_original_chart (background : DressedEvent) (eps sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (zero : sheetDeterminant background eps sigma n = 0) (s : ℝ) :
    correctedDet background eps s sigma n = 0 := by
  by_contra regular
  exact actual_common_determinant_nonzero background eps sigma s n positive regular
    (singular_common_sheet_no_chart background eps sigma n zero s)

theorem singular_common_sheet_no_pole_packet (background : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (zero : sheetDeterminant background eps sigma n = 0) :
    sheetVisiblePoles background eps sigma n pd ps dL dR sL sR = none :=
  singular_no_pole_packet _ _ zero

theorem actual_reduced_current_read (background : DressedEvent) (eps sigma s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (positive : 0 < sigma)
    (regular : correctedDet background eps s sigma n ≠ 0) :
    correctedProbeRead background eps s sigma n pd ps dL dR sL sR =
      (sheetReadFraction background eps sigma n pd ps dL dR sL sR).num.eval (s : ℂ) /
        (sheetReadFraction background eps sigma n pd ps dL dR sL sR).denom.eval (s : ℂ) := by
  have determinant : (sheetDeterminant background eps sigma n).eval (s : ℂ) ≠ 0 := by
    rw [sheetDeterminant, sheet_slice_eval]
    exact actual_common_determinant_nonzero background eps sigma s n positive regular
  exact (actual_common_current_read_fraction background eps sigma s n pd ps dL dR sL sR positive regular).trans
    (by
      rw [← sheet_slice_eval, ← sheet_slice_eval]
      exact (reduced_read_at_regular _ _ (s : ℂ) determinant).symm)

theorem actual_zero_current_read (background : DressedEvent) (eps sigma s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (positive : 0 < sigma)
    (regular : correctedDet background eps s sigma n ≠ 0)
    (zero : sheetCurrentNumerator background eps sigma n pd ps dL dR sL sR = 0) :
    correctedProbeRead background eps s sigma n pd ps dL dR sL sR = 0 := by
  rw [actual_common_current_read_fraction background eps sigma s n pd ps dL dR sL sR positive regular,
    ← sheet_slice_eval]
  change (sheetCurrentNumerator background eps sigma n pd ps dL dR sL sR).eval (s : ℂ) / _ = 0
  rw [zero, eval_zero, zero_div]

theorem source_visible_root_data (background : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (a : ℂ)
    (root : a ∈ visibleRoots (sheetReadFraction background eps sigma n pd ps dL dR sL sR)) :
    let R := sheetReadFraction background eps sigma n pd ps dL dR sL sR
    0 < poleOrder R a ∧ R.num.eval a ≠ 0 ∧ principalCoefficient R a 0 ≠ 0 ∧
      (visibleRoots R).count a = poleOrder R a :=
  ⟨visible_pole_order_positive _ _ root, visible_numerator_nonzero _ _ root,
    principal_leading_nonzero _ _ root, visible_roots_count _ _⟩

theorem source_visible_principal_part (background : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (a z : ℂ)
    (root : a ∈ visibleRoots (sheetReadFraction background eps sigma n pd ps dL dR sL sR))
    (away : z ≠ a)
    (regular : (rootRemainder (sheetReadFraction background eps sigma n pd ps dL dR sL sR) a).eval z ≠ 0) :
    let R := sheetReadFraction background eps sigma n pd ps dL dR sL sR
    R.num.eval z/R.denom.eval z =
      (∑ k ∈ Finset.range (poleOrder R a), principalCoefficient R a k*(z-a)^k/(z-a)^poleOrder R a)+
        (analyticNumerator R a).eval z/(rootRemainder R a).eval z := by
  dsimp only
  rw [complete_principal_part _ a z away regular, principal_negative_powers _ a z root]

theorem source_reduced_denominator_divides (background : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    (sheetReadFraction background eps sigma n pd ps dL dR sL sR).denom ∣
      sheetDeterminant background eps sigma n := reduced_denominator_dvd _ _

theorem source_cancelled_zero_analytic (background : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (a : ℂ)
    (visibleRegular : (sheetReadFraction background eps sigma n pd ps dL dR sL sR).denom.eval a ≠ 0) :
    let R := sheetReadFraction background eps sigma n pd ps dL dR sL sR
    AnalyticAt ℂ (fun z : ℂ => R.num.eval z/R.denom.eval z) a :=
  reduced_analytic_at _ a visibleRegular

theorem source_visible_order_limit (background : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (a : ℂ) :
    let R := sheetReadFraction background eps sigma n pd ps dL dR sL sR
    Filter.Tendsto (fun z : ℂ => (z-a)^poleOrder R a*(R.num.eval z/R.denom.eval z))
      (nhdsWithin a ({a}ᶜ)) (nhds (leadingPoleCoefficient R a)) := pole_order_limit _ a

theorem actual_current_principal_part (background : DressedEvent) (eps sigma s : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) (a : ℂ)
    (positive : 0 < sigma) (originalRegular : correctedDet background eps s sigma n ≠ 0)
    (root : a ∈ visibleRoots (sheetReadFraction background eps sigma n pd ps dL dR sL sR))
    (away : (s : ℂ) ≠ a)
    (remainderRegular : (rootRemainder (sheetReadFraction background eps sigma n pd ps dL dR sL sR) a).eval (s : ℂ) ≠ 0) :
    let R := sheetReadFraction background eps sigma n pd ps dL dR sL sR
    correctedProbeRead background eps s sigma n pd ps dL dR sL sR =
      (∑ k ∈ Finset.range (poleOrder R a), principalCoefficient R a k*((s : ℂ)-a)^k/((s : ℂ)-a)^poleOrder R a)+
        (analyticNumerator R a).eval (s : ℂ)/(rootRemainder R a).eval (s : ℂ) :=
  (actual_reduced_current_read background eps sigma s n pd ps dL dR sL sR positive originalRegular).trans
    (source_visible_principal_part background eps sigma n pd ps dL dR sL sR a (s : ℂ) root away remainderRegular)

end LowEnergy.GaussComposite.ActualDressedVisiblePole

#print axioms LowEnergy.GaussComposite.ActualDressedVisiblePole.actual_reduced_current_read
#print axioms LowEnergy.GaussComposite.ActualDressedVisiblePole.singular_common_sheet_no_original_chart
#print axioms LowEnergy.GaussComposite.ActualDressedVisiblePole.actual_current_principal_part
#print axioms LowEnergy.GaussComposite.ActualDressedVisiblePole.source_visible_order_limit
