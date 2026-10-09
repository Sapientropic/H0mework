import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedBodyMeasurement
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.JointObservableIncidence

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open scoped Matrix ComplexOrder
noncomputable section

section Incidence
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
theorem bodyObservable_positive (O : Matrix (ι × κ) (ι × κ) ℂ) (positive : O.PosSemidef) :
    (Incidence.bodyObservable O).PosSemidef :=
  (positive.kronecker Matrix.PosSemidef.one).submatrix _

omit [Fintype ι] [Fintype κ] in
theorem bodyObservable_one :
    Incidence.bodyObservable (1 : Matrix (ι × κ) (ι × κ) ℂ) = 1 := by
  ext i j
  simp [Incidence.bodyObservable, Matrix.kronecker,
    Incidence.bodyReservoir, Matrix.one_apply, Prod.mk.injEq]
  aesop

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem bodyObservable_sub (A B : Matrix (ι × κ) (ι × κ) ℂ) :
    Incidence.bodyObservable (A - B) = Incidence.bodyObservable A - Incidence.bodyObservable B := by
  ext i j
  change (A _ _ - B _ _) * (1 : Matrix ι ι ℂ) _ _ = _
  exact sub_mul _ _ _

omit [Fintype ι] [Fintype κ] in
theorem bodyObservable_complement (O : Matrix (ι × κ) (ι × κ) ℂ) :
    1 - Incidence.bodyObservable O = Incidence.bodyObservable (1 - O) := by
  rw [bodyObservable_sub, bodyObservable_one]

theorem bodyObservable_lawful (O : Matrix (ι × κ) (ι × κ) ℂ)
    (positive : O.PosSemidef) (complement : (1 - O).PosSemidef) :
    (Incidence.bodyObservable O).PosSemidef ∧ (1 - Incidence.bodyObservable O).PosSemidef :=
  ⟨bodyObservable_positive O positive,
    bodyObservable_complement O ▸ bodyObservable_positive (1 - O) complement⟩
end Incidence

def sourceEffect : Current.FullJoint :=
  Incidence.bodyObservable (Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian)

theorem sourceEffect_lawful : sourceEffect.PosSemidef ∧ (1 - sourceEffect).PosSemidef :=
  bodyObservable_lawful _ (Measurement.sourceMeasurement_lawful _ Load.Source.loadTotalHamiltonian_hermitian).1
    (Measurement.sourceMeasurement_lawful _ Load.Source.loadTotalHamiltonian_hermitian).2

def received : Current.State := Current.supplyNext Current.initial

theorem sourceEffect_actual_read :
    Measurement.sourceMeasurementDecode Load.Source.loadTotalHamiltonian (Collision.energy sourceEffect received.joint) =
      Collision.energy Load.Source.loadTotalHamiltonian Source.received.joint := by
  rw [sourceEffect, Incidence.bodyObservable_energy]
  exact Measurement.sourceMeasurement_actual Load.Source.loadTotalHamiltonian

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
