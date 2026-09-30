import H0mework.Physics.LowEnergy.PacketGaugeNoise.Current
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The primitive affine current is centered in the unchanged source state.
Its true strong derivative generates both ordered legs of the noise response. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
open FullQuantum FullSpace PacketNoise PacketFourier GaugeGreen HistoryPrepared
noncomputable section

theorem positiveDamping : (0 : ℝ)<1 := by norm_num

def preparedState : FullMatterL2 := filteredPacket 0 1 positiveDamping

def variationFilter (gauge : GaugeProfile) (shift : Position) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (currentVariation gauge shift).comp (sourceFilter 0 1 positiveDamping)

def currentFilterFamily (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  phaseCurrentFilter 0 1 positiveDamping shift 0+(epsilon : ℂ) • variationFilter gauge shift

theorem currentFilterFamily_original (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position) :
    currentFilterFamily gauge epsilon shift preparedPacket=
      currentFamily gauge epsilon shift (preparedDomain 0 1 positiveDamping) := by
  rw [currentFilterFamily,add_apply,smul_apply,phaseCurrentFilter_prepared,currentFamily_affine]
  rfl

def meanVariation (gauge : GaugeProfile) (shift : Position) : ℂ :=
  inner ℂ preparedState (variationFilter gauge shift preparedPacket)

def meanFamily (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position) : ℂ :=
  inner ℂ preparedState (currentFilterFamily gauge epsilon shift preparedPacket)

theorem meanFamily_affine (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position) :
    meanFamily gauge epsilon shift=phaseMean 0 1 positiveDamping shift 0+
      (epsilon : ℂ)*meanVariation gauge shift := by
  simp only [meanFamily,currentFilterFamily,add_apply,smul_apply,inner_add_right,inner_smul_right]
  rfl

def centeredVariation (gauge : GaugeProfile) (shift : Position) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  variationFilter gauge shift-meanVariation gauge shift • sourceFilter 0 1 positiveDamping

def centeredFamily (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  currentFilterFamily gauge epsilon shift-meanFamily gauge epsilon shift • sourceFilter 0 1 positiveDamping

attribute [local irreducible] sourceFilter phaseCurrentFilter phaseMean variationFilter meanVariation

theorem centeredFamily_affine (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position) :
    centeredFamily gauge epsilon shift=phaseCenteredFilter 0 1 positiveDamping shift 0+
      (epsilon : ℂ) • centeredVariation gauge shift := by
  rw [centeredFamily,meanFamily_affine,currentFilterFamily,centeredVariation,phaseCenteredFilter]
  module

def variationVector (gauge : GaugeProfile) (shift : Position) : FullMatterL2 :=
  centeredVariation gauge shift preparedPacket

def packetFamily (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position) : FullMatterL2 :=
  centeredFamily gauge epsilon shift preparedPacket

theorem packetFamily_affine (gauge : GaugeProfile) (epsilon : ℝ) (shift : Position) :
    packetFamily gauge epsilon shift=phasePacket 0 1 positiveDamping shift 0+
      (epsilon : ℂ) • variationVector gauge shift := by
  rw [packetFamily,centeredFamily_affine,add_apply,smul_apply]
  rfl

theorem packetFamily_zero (gauge : GaugeProfile) (shift : Position) :
    packetFamily gauge 0 shift=phasePacket 0 1 positiveDamping shift 0 := by
  rw [packetFamily_affine]
  simp

private theorem real_affine_derivative (first second : FullMatterL2) (epsilon : ℝ) :
    HasDerivAt (fun r : ℝ => first+(r : ℂ) • second) second epsilon := by
  convert! ((hasDerivAt_id epsilon).smul_const second).const_add first using 1
  norm_num

theorem packetFamily_derivative (gauge : GaugeProfile) (shift : Position) (epsilon : ℝ) :
    HasDerivAt (fun r => packetFamily gauge r shift) (variationVector gauge shift) epsilon := by
  simpa only [packetFamily_affine] using
    real_affine_derivative (phasePacket 0 1 positiveDamping shift 0) (variationVector gauge shift) epsilon

def noiseFamily (gauge : GaugeProfile) (epsilon : ℝ) (left right : Position) : ℂ :=
  inner ℂ (packetFamily gauge epsilon left) (packetFamily gauge epsilon right)

def noiseSlope (gauge : GaugeProfile) (left right : Position) : ℂ :=
  inner ℂ (variationVector gauge left) (phasePacket 0 1 positiveDamping right 0)+
    inner ℂ (phasePacket 0 1 positiveDamping left 0) (variationVector gauge right)

theorem noiseFamily_derivative (gauge : GaugeProfile) (left right : Position) :
    HasDerivAt (fun epsilon => noiseFamily gauge epsilon left right) (noiseSlope gauge left right) 0 := by
  have generated := (packetFamily_derivative gauge left 0).inner ℂ (packetFamily_derivative gauge right 0)
  simpa only [noiseFamily,noiseSlope,packetFamily_zero,add_comm] using generated

theorem noiseFamily_zero (gauge : GaugeProfile) (left right : Position) :
    noiseFamily gauge 0 left right=phaseCovariance 0 1 positiveDamping left right 0 0 := by
  rw [noiseFamily,packetFamily_zero,packetFamily_zero]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
