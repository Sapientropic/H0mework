import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.PacketNoise.Shift
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeGreen.Dirac

/-! The actual Dirac graph is closed under spatial momentum transfer; its commutator is the original gamma insertion. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen SpatialWeak YangMills.FullPairing
open ProofFreeRicherAnholonomicSource
noncomputable section

theorem sourceField_shift (point : BasePoint) (energy damping : ℝ) (field : FullMatterL2) (shift : Position) :
    sourceField point energy damping (phaseShift shift field) =ᵐ[volume]
      fun frequency => sourceField point energy damping field (frequency-shift)-
        shiftSymbol point shift (fourier field (frequency-shift)) := by
  filter_upwards [frequencyShift_ae shift (fourier field)] with frequency shifted
  simp only [sourceField,phaseShift_fourier,shifted,symbol_shift point energy damping frequency shift]
  rfl

theorem phaseShift_domain (point : BasePoint) (energy damping : ℝ)
    (field : Domain point energy damping) (shift : Position) :
    MemLp (sourceField point energy damping (phaseShift shift field.val)) 2 volume := by
  have translated := field.property.comp_measurePreserving (measurePreserving_sub_right volume shift)
  have image := ((shiftSymbol point shift).comp_memLp (fourier field.val)).comp_measurePreserving
    (measurePreserving_sub_right volume shift)
  exact (translated.sub image).ae_eq (sourceField_shift point energy damping field.val shift).symm

def domainShift (point : BasePoint) (energy damping : ℝ) (shift : Position)
    (field : Domain point energy damping) : Domain point energy damping :=
  ⟨phaseShift shift field.val,phaseShift_domain point energy damping field shift⟩

theorem original_dirac_shift (point : BasePoint) (energy damping : ℝ)
    (field : Domain point energy damping) (shift : Position) :
    dirac point energy damping (domainShift point energy damping shift field)=
      phaseShift shift (dirac point energy damping field)-
        (shiftSymbol point shift).compLpL 2 volume (phaseShift shift field.val) := by
  apply fourier.injective
  rw [map_sub,phaseShift_fourier,GaugeGreen.constant_fourier]
  apply Lp.ext
  have translated := (measurePreserving_sub_right volume shift).quasiMeasurePreserving.ae
    (dirac_fourier_ae point energy damping field)
  filter_upwards [dirac_fourier_ae point energy damping (domainShift point energy damping shift field),
    sourceField_shift point energy damping field.val shift,
    frequencyShift_ae shift (dirac point energy damping field |> fourier),translated,
    (shiftSymbol point shift).coeFn_compLpL (fourier (phaseShift shift field.val)),
    frequencyShift_ae shift (fourier field.val),
    Lp.coeFn_sub (frequencyShift shift (fourier (dirac point energy damping field)))
      ((shiftSymbol point shift).compLpL 2 volume (fourier (phaseShift shift field.val)))]
    with frequency left equation shiftedSource original constant shiftedField difference
  rw [left]
  change sourceField point energy damping (phaseShift shift field.val) frequency=_
  rw [equation,difference]
  simp only [Pi.sub_apply]
  rw [shiftedSource,original,constant,phaseShift_fourier,shiftedField]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
