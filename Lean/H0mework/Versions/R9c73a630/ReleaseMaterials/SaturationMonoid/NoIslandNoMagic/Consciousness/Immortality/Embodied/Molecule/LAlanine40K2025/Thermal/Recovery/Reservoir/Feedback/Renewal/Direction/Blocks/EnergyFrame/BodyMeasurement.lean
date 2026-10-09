import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.InstrumentState
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Source.SourceGeneratedPointerEffect

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def bodyRegroup : Matrix ((ι × κ) × ι) ((ι × κ) × ι) ℂ ≃⋆ₐ[ℂ]
    Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ (Incidence.bodyReservoir (ι := ι) (κ := κ)).symm with
    map_star' := by intro A; rfl
    map_smul' := by intro c A; rfl }

def bodyObservableHom : Matrix (ι × κ) (ι × κ) ℂ →⋆ₙₐ[ℂ]
    Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ :=
  bodyRegroup.toStarAlgHom.toNonUnitalStarAlgHom.comp (tensorLeft (ι := ι × κ) (κ := ι))

theorem body_observable_map (A : Matrix (ι × κ) (ι × κ) ℂ) :
    bodyObservableHom A = Incidence.bodyObservable A := rfl

theorem body_observable_norm (A : Matrix (ι × κ) (ι × κ) ℂ) :
    ‖Incidence.bodyObservable A‖ ≤ ‖A‖ := NonUnitalStarAlgHom.norm_apply_le bodyObservableHom A

theorem body_observable_sqrt (A : Matrix (ι × κ) (ι × κ) ℂ) (positive : A.PosSemidef) :
    Incidence.bodyObservable (CFC.sqrt A) = CFC.sqrt (Incidence.bodyObservable A) := by
  symm
  apply CFC.sqrt_unique
  · have product := map_mul bodyObservableHom (CFC.sqrt A) (CFC.sqrt A)
    change Incidence.bodyObservable (CFC.sqrt A*CFC.sqrt A) =
      Incidence.bodyObservable (CFC.sqrt A)*Incidence.bodyObservable (CFC.sqrt A) at product
    rw [← product,CFC.sqrt_mul_sqrt_self A positive.nonneg]
  · exact (bodyObservable_positive _ (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))).nonneg

theorem body_root_error (A B : Matrix (ι × κ) (ι × κ) ℂ)
    (positiveA : A.PosSemidef) (positiveB : B.PosSemidef) :
    ‖CFC.sqrt (Incidence.bodyObservable A)-CFC.sqrt (Incidence.bodyObservable B)‖ ≤
      ‖CFC.sqrt A-CFC.sqrt B‖ := by
  rw [← body_observable_sqrt A positiveA,← body_observable_sqrt B positiveB,← bodyObservable_sub]
  exact body_observable_norm _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
