import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.FullCurrentSymbol.Vertex

/-! The reducing source projection generates an actual twelve-coordinate
inverse and the complete current leg, including forcing outside its range. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrentSymbol
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open ActiveSector MatterSpace StageNineHolonomicField
open SU7MotherLieAlgebra SU7ExteriorBreakingYukawa StageNineDiracDualYukawaSpinJurisdiction
noncomputable section

def compress (A : Mother) : Module.End ℂ (SourceIndex → ℂ) :=
  tripletRestrict.comp (A.comp tripletLift)

theorem projection_lift (v : SourceIndex → ℂ) : projection (tripletLift v)=tripletLift v :=
  projection_triplet _

theorem compress_one : compress 1=1 := by
  apply LinearMap.ext
  intro v
  exact restrict_lift v

theorem compress_mul (A B : Mother) (reduced : Commute projection B) :
    compress (A*B)=compress A*compress B := by
  apply LinearMap.ext
  intro v
  change tripletRestrict (A (B (tripletLift v)))=
    tripletRestrict (A (tripletLift (tripletRestrict (B (tripletLift v)))))
  rw [lift_restrict]
  have commute := LinearMap.congr_fun reduced.eq (tripletLift v)
  change projection (B (tripletLift v))=B (projection (tripletLift v)) at commute
  rw [commute,projection_lift]

theorem compressed_action (A : Mother) (reduced : Commute projection A) (v : DiracExteriorMatterCarrier) :
    tripletLift (compress A (tripletRestrict v))=projection (A v) := by
  change tripletLift (tripletRestrict (A (tripletLift (tripletRestrict v))))=_
  rw [lift_restrict,lift_restrict]
  have commute := LinearMap.congr_fun reduced.eq v
  change projection (A v)=A (projection v) at commute
  rw [← commute]
  exact LinearMap.congr_fun projection_idempotent (A v)

theorem compressed_source_inverse (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (regular : IsUnit (FullCurrent.stationaryKernel point k z)) :
    compress (FullCurrent.stationaryKernel point k z)*compress (FullCurrent.stationaryGreen point k z)=1 ∧
    compress (FullCurrent.stationaryGreen point k z)*compress (FullCurrent.stationaryKernel point k z)=1 := by
  have inverse := FullCurrent.stationaryGreen_two_sided point k z regular
  constructor
  · rw [← compress_mul _ _ (stationaryGreen_reducing point k z),inverse.1,compress_one]
  · rw [← compress_mul _ _ (stationary_reducing point k z),inverse.2,compress_one]

theorem source_inverse_identification (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (regular : IsUnit (FullCurrent.stationaryKernel point k z)) :
    compress (FullCurrent.stationaryGreen point k z)=Ring.inverse (compress (FullCurrent.stationaryKernel point k z)) := by
  have inverse := compressed_source_inverse point k z regular
  let unit : (Module.End ℂ (SourceIndex → ℂ))ˣ :=
    ⟨compress (FullCurrent.stationaryKernel point k z),compress (FullCurrent.stationaryGreen point k z),inverse.1,inverse.2⟩
  exact (Ring.inverse_unit unit).symm

structure PrimitiveVariation where
  deltaGamma : LorentzianIndex → DiracCliffordRepresentation.DiracMatrix
  deltaSpin : LorentzianIndex → DiracCliffordRepresentation.DiracMatrix
  deltaGauge : LorentzianIndex → P286LieBlockData
  deltaVolume : ℂ
  deltaScalar : ExteriorBreakingScalarCarrier

def PrimitiveVariation.operator (data : PrimitiveVariation) (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ) : Mother :=
  primitiveVertex point k z data.deltaGamma data.deltaSpin data.deltaGauge data.deltaVolume data.deltaScalar

theorem complete_source_leg_reduction (data : PrimitiveVariation) (point : BasePoint)
    (readerK : Fin 3 → ℝ) (readerZ : ℂ) (k : Fin 3 → ℝ) (z : ℂ) (V : Mother) :
    actual.conjugateMatter point (data.operator point readerK readerZ
      (FullCurrent.stationaryGreen point k z (V (actual.matter point))))=
    actual.conjugateMatter point (data.operator point readerK readerZ
      (tripletLift (compress (FullCurrent.stationaryGreen point k z)
        (tripletRestrict (V (actual.matter point)))))) := by
  rw [compressed_action _ (stationaryGreen_reducing point k z)]
  symm
  exact primitive_left_retained _ _ _ _ _ _ _ _ _

theorem scalar_forcing_zero_read (data : PrimitiveVariation) (point : BasePoint)
    (readerK : Fin 3 → ℝ) (readerZ : ℂ) (k : Fin 3 → ℝ) (z : ℂ)
    (scalar : ExteriorBreakingScalarCarrier) :
    actual.conjugateMatter point (data.operator point readerK readerZ
      (FullCurrent.stationaryGreen point k z (diracDualRightChiralYukawaAction scalar (actual.matter point))))=0 := by
  have left := primitive_left_retained point readerK readerZ data.deltaGamma data.deltaSpin data.deltaGauge
    data.deltaVolume data.deltaScalar (FullCurrent.stationaryGreen point k z
      (diracDualRightChiralYukawaAction scalar (actual.matter point)))
  change actual.conjugateMatter point (data.operator point readerK readerZ (projection _))=
    actual.conjugateMatter point (data.operator point readerK readerZ
      (FullCurrent.stationaryGreen point k z (diracDualRightChiralYukawaAction scalar (actual.matter point)))) at left
  rw [← left]
  have commute := LinearMap.congr_fun (stationaryGreen_reducing point k z).eq
    (diracDualRightChiralYukawaAction scalar (actual.matter point))
  change projection (FullCurrent.stationaryGreen point k z _)=FullCurrent.stationaryGreen point k z
    (projection (diracDualRightChiralYukawaAction scalar (actual.matter point))) at commute
  rw [commute]
  have zero := LinearMap.congr_fun (projection_yukawa_zero scalar) (actual.matter point)
  change projection (diracDualRightChiralYukawaAction scalar (actual.matter point))=0 at zero
  rw [zero,map_zero,map_zero,map_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrentSymbol
