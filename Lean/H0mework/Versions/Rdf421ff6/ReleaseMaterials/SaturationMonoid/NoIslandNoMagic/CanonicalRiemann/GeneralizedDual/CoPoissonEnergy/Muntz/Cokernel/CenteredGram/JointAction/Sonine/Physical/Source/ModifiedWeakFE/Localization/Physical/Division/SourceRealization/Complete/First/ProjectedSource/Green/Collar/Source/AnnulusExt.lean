import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.EvenAction

/-! Reflection and the actual annulus cut extend a local source equality to the whole L² vector. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem source_even_annulus_ext (left right : BurnolL2)
    (leftEven : reflectL2 left = left) (rightEven : reflectL2 right = right)
    (leftCut : sourceAnnulusCut left = left) (rightCut : sourceAnnulusCut right = right)
    (localRead : ∀ᵐ t ∂volume, t ∈ Ioo (1 / 4 : ℝ) 4 → left t = right t) :
    left = right := by
  have leftReflection := Lp.coeFn_compMeasurePreserving left negMeasurePreserving
  have rightReflection := Lp.coeFn_compMeasurePreserving right negMeasurePreserving
  change (reflectL2 left : ℝ → ℂ) =ᵐ[volume] (fun x => left (-x)) at leftReflection
  change (reflectL2 right : ℝ → ℂ) =ᵐ[volume] (fun x => right (-x)) at rightReflection
  rw [leftEven] at leftReflection
  rw [rightEven] at rightReflection
  have leftSupport := sourceAnnulusCut_coeFn left
  have rightSupport := sourceAnnulusCut_coeFn right
  rw [leftCut] at leftSupport
  rw [rightCut] at rightSupport
  apply Lp.ext
  filter_upwards [localRead, negMeasurePreserving.quasiMeasurePreserving.ae localRead,
    leftReflection, rightReflection, leftSupport, rightSupport,
    volume.ae_ne (4 : ℝ), volume.ae_ne (-4 : ℝ)]
      with t positiveRead negativeRead leftReflect rightReflect supportLeft supportRight notFour notNegFour
  by_cases band : (1 / 4 : ℝ) < |t| ∧ |t| ≤ 4
  · have upper : |t| < 4 := by
      apply lt_of_le_of_ne band.2
      intro atFour
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 4)).mp atFour with right | left
      · exact notFour right
      · exact notNegFour left
    by_cases positive : 0 ≤ t
    · apply positiveRead
      simpa only [mem_Ioo, abs_of_nonneg positive] using
        (show (1 / 4 : ℝ) < |t| ∧ |t| < 4 from ⟨band.1, upper⟩)
    · rw [leftReflect, rightReflect]
      apply negativeRead
      simpa only [mem_Ioo, abs_of_neg (lt_of_not_ge positive)] using
        (show (1 / 4 : ℝ) < |t| ∧ |t| < 4 from ⟨band.1, upper⟩)
  · rw [supportLeft, supportRight, if_neg band, if_neg band]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
