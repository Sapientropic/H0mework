import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.FullCurrentSymbol.Source

/-! Primitive coframe, Lorentz, P286 and scalar jets generate the entire
vertex class. Scalar output remains outside the retained current carrier. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrentSymbol
open DiracExteriorMatterAction DiracCliffordRepresentation ProofFreeRicherAnholonomicSource
open StageNineHolonomicField Stage9C.Material.SpinPair ActiveSector MatterSpace
open SU7MotherLieAlgebra SU7ExteriorBreakingYukawa StageNineDiracDualYukawaSpinJurisdiction
noncomputable section

def incoming (k : Fin 3 → ℝ) (z : ℂ) : LorentzianIndex → ℂ :=
  Fin.cases (-Complex.I*z) (fun j => Complex.I*(k j : ℂ))

def coframeVertex (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (deltaGamma : LorentzianIndex → DiracMatrix) : Mother :=
  Complex.I • ∑ mu, diracMatrixMatterAction (deltaGamma mu)*
    ((incoming k z mu) • 1+connection actual point mu)

def connectionVertex (deltaSpin : LorentzianIndex → DiracMatrix)
    (deltaGauge : LorentzianIndex → P286LieBlockData) : Mother :=
  Complex.I • ∑ mu, diracMatrixMatterAction (sourceInverseGamma mu)*
    (diracMatrixMatterAction (deltaSpin mu)+diracExteriorMotherLieAction (p286LieBlockEmbed (deltaGauge mu)))

def freeVertex (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (deltaGamma deltaSpin : LorentzianIndex → DiracMatrix)
    (deltaGauge : LorentzianIndex → P286LieBlockData) (deltaVolume : ℂ) : Mother :=
  deltaVolume • FullCurrent.stationaryKernel point k z+(lapse : ℂ) •
    (coframeVertex point k z deltaGamma+connectionVertex deltaSpin deltaGauge+
      (frequency : ℂ) • (diracMatrixMatterAction (deltaGamma 0)*FullPhase.phaseGenerator))

def primitiveVertex (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (deltaGamma deltaSpin : LorentzianIndex → DiracMatrix)
    (deltaGauge : LorentzianIndex → P286LieBlockData) (deltaVolume : ℂ)
    (deltaScalar : ExteriorBreakingScalarCarrier) : Mother :=
  freeVertex point k z deltaGamma deltaSpin deltaGauge deltaVolume+
    (lapse : ℂ) • diracDualRightChiralYukawaAction deltaScalar

theorem coframeVertex_reducing (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (deltaGamma : LorentzianIndex → DiracMatrix) : Commute projection (coframeVertex point k z deltaGamma) := by
  apply Commute.smul_right
  apply Commute.sum_right
  intro mu _
  exact (spin_reducing _).mul_right (((Commute.one_right projection).smul_right _).add_right
    (connection_reducing actual point mu))

theorem connectionVertex_reducing (deltaSpin : LorentzianIndex → DiracMatrix)
    (deltaGauge : LorentzianIndex → P286LieBlockData) : Commute projection (connectionVertex deltaSpin deltaGauge) := by
  apply Commute.smul_right
  apply Commute.sum_right
  intro mu _
  exact (spin_reducing _).mul_right ((spin_reducing _).add_right (projection_gauge _))

theorem freeVertex_reducing (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (deltaGamma deltaSpin : LorentzianIndex → DiracMatrix)
    (deltaGauge : LorentzianIndex → P286LieBlockData) (deltaVolume : ℂ) :
    Commute projection (freeVertex point k z deltaGamma deltaSpin deltaGauge deltaVolume) :=
  ((stationary_reducing point k z).smul_right _).add_right
    ((((coframeVertex_reducing point k z deltaGamma).add_right (connectionVertex_reducing deltaSpin deltaGauge)).add_right
      (((spin_reducing _).mul_right phase_reducing).smul_right _)).smul_right _)

theorem source_primal_retained (point : BasePoint) : projection (actual.matter point)=actual.matter point := by
  rw [actual_matter]
  exact projection_original _ _

theorem source_dual_retained (point : BasePoint) (v : DiracExteriorMatterCarrier) :
    actual.conjugateMatter point (projection v)=actual.conjugateMatter point v := by
  rw [actual_conjugateMatter]
  exact LinearMap.congr_fun (original_dual_projection _ _) v

theorem source_scalar_left_zero (point : BasePoint) (scalar : ExteriorBreakingScalarCarrier)
    (v : DiracExteriorMatterCarrier) : actual.conjugateMatter point (diracDualRightChiralYukawaAction scalar v)=0 := by
  rw [← source_dual_retained point (diracDualRightChiralYukawaAction scalar v)]
  have generated := LinearMap.congr_fun (projection_yukawa_zero scalar) v
  change projection (diracDualRightChiralYukawaAction scalar v)=0 at generated
  rw [generated,map_zero]

theorem primitive_left_retained (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (deltaGamma deltaSpin : LorentzianIndex → DiracMatrix)
    (deltaGauge : LorentzianIndex → P286LieBlockData) (deltaVolume : ℂ)
    (deltaScalar : ExteriorBreakingScalarCarrier) (v : DiracExteriorMatterCarrier) :
    actual.conjugateMatter point (primitiveVertex point k z deltaGamma deltaSpin deltaGauge deltaVolume deltaScalar (projection v))=
      actual.conjugateMatter point (primitiveVertex point k z deltaGamma deltaSpin deltaGauge deltaVolume deltaScalar v) := by
  simp only [primitiveVertex,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,
    source_scalar_left_zero,smul_zero,add_zero]
  have reduced := LinearMap.congr_fun (freeVertex_reducing point k z deltaGamma deltaSpin deltaGauge deltaVolume).eq v
  change projection (freeVertex point k z deltaGamma deltaSpin deltaGauge deltaVolume v)=
    freeVertex point k z deltaGamma deltaSpin deltaGauge deltaVolume (projection v) at reduced
  rw [← reduced,source_dual_retained]

theorem primitive_force_projection (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (deltaGamma deltaSpin : LorentzianIndex → DiracMatrix)
    (deltaGauge : LorentzianIndex → P286LieBlockData) (deltaVolume : ℂ)
    (deltaScalar : ExteriorBreakingScalarCarrier) :
    projection (primitiveVertex point k z deltaGamma deltaSpin deltaGauge deltaVolume deltaScalar (actual.matter point))=
      freeVertex point k z deltaGamma deltaSpin deltaGauge deltaVolume (actual.matter point) := by
  have scalar := LinearMap.congr_fun (projection_yukawa_zero deltaScalar) (actual.matter point)
  change projection (diracDualRightChiralYukawaAction deltaScalar (actual.matter point))=0 at scalar
  simp only [primitiveVertex,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,scalar,smul_zero,add_zero]
  have reduced := LinearMap.congr_fun (freeVertex_reducing point k z deltaGamma deltaSpin deltaGauge deltaVolume).eq
    (actual.matter point)
  change projection (freeVertex point k z deltaGamma deltaSpin deltaGauge deltaVolume (actual.matter point))=
    freeVertex point k z deltaGamma deltaSpin deltaGauge deltaVolume (projection (actual.matter point)) at reduced
  simpa only [source_primal_retained] using reduced

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrentSymbol
