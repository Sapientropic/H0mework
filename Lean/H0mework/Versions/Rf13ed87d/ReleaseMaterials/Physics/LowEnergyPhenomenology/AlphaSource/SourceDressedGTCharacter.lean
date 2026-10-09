import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFilteredFirstEnergy
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeVertex

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalDressedSpinChargeReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstGaugeBackgroundReturn
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open DiracExteriorMatterAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open StageNineExteriorMotherLieRepresentation
open GaussComposite Electromagnetic.Identification
open scoped BigOperators Matrix
local instance : DecidableEq Quantum.Index:=Classical.decEq _

/-- The original exterior subsets calculate a common total weight, before either spin is selected. -/
theorem sourceDressedGT_weight (channel : Fin 2) (color : Fin 3) :
    sourceFirstExteriorWeight (Composite.scalarBasis channel color)+
      sourceFirstExteriorWeight (Composite.matterBasis color)=5/11 := by
  exact (show ∀a : Fin 2,∀c : Fin 3,
    sourceFirstExteriorWeight (Composite.scalarBasis a c)+
      sourceFirstExteriorWeight (Composite.matterBasis c)=5/11 from by decide +kernel) channel color

theorem sourceDressedGT_scalar (channel : Fin 2) (color : Fin 3) (phi : Scalar) :
    scalarCoefficient channel color (scalarMotherLieAction sourceFirstTemporalMother phi)=
      ((sourceFirstExteriorWeight (Composite.scalarBasis channel color):ℂ)*Complex.I)*
        scalarCoefficient channel color phi := by
  have diagonal : (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color)
      (exteriorMotherLieAction 4 sourceFirstTemporalMother (scalarCoordinateEquiv.symm phi))=
      ((sourceFirstExteriorWeight (Composite.scalarBasis channel color):ℂ)*Complex.I)*
        (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color) (scalarCoordinateEquiv.symm phi) := by
    rw [←(su7ExteriorBasis 4).sum_repr (scalarCoordinateEquiv.symm phi)]
    simp only [map_sum,map_smul,sourceFirstTemporal_exterior,Module.Basis.coord_apply,
      Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,if_true]
    ring
  change (if color=1 then (-1:ℂ) else 1) •
    (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color)
      (scalarCoordinateEquiv.symm (scalarMotherLieAction sourceFirstTemporalMother phi))=_
  rw [scalarMotherLieAction,LinearEquiv.symm_apply_apply,diagonal]
  simp only [scalarCoefficient,LinearMap.smul_apply,LinearMap.comp_apply,smul_eq_mul]
  change (if color=1 then (-1:ℂ) else 1)*
      (((sourceFirstExteriorWeight (Composite.scalarBasis channel color):ℂ)*Complex.I)*
        (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color) (scalarCoordinateEquiv.symm phi))=
    ((sourceFirstExteriorWeight (Composite.scalarBasis channel color):ℂ)*Complex.I)*
      ((if color=1 then (-1:ℂ) else 1)*
        (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color) (scalarCoordinateEquiv.symm phi))
  ring

theorem sourceDressedGT_matter (spin : Fin 2) (color : Fin 3) (psi : DiracExteriorMatterCarrier) :
    Quantum.coordinates (sourceFirstTemporalGenerator psi)
      ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis color))⟩=
      ((sourceFirstExteriorWeight (Composite.matterBasis color):ℂ)*Complex.I)*
        Quantum.coordinates psi ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis color))⟩ := by
  rw [←Quantum.matrix_action,sourceFirstTemporal_matrix,Matrix.mulVec_diagonal]
  rfl

/-- Both elementary variations are present; the shared factor is generated from the full scalar and mother actions. -/
theorem sourceDressedGT_read (channel spin : Fin 2) (phi : Scalar) (psi : DiracExteriorMatterCarrier) :
    originalRead channel spin (scalarMotherLieAction sourceFirstTemporalMother phi) psi+
      originalRead channel spin phi (sourceFirstTemporalGenerator psi)=
      ((5/11:ℂ)*Complex.I)*originalRead channel spin phi psi := by
  simp only [originalRead,←original_mode_read,sourceDressedGT_scalar,sourceDressedGT_matter,
    ←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have weight : (sourceFirstExteriorWeight (Composite.scalarBasis channel c):ℂ)+
      (sourceFirstExteriorWeight (Composite.matterBasis c):ℂ)=(5/11:ℂ) := by
    have cast:=congrArg (fun q : ℚ=>(q:ℂ)) (sourceDressedGT_weight channel c)
    norm_num only [Rat.cast_add,Rat.cast_div] at cast
    exact cast
  linear_combination (Complex.I*scalarCoefficient channel c phi*
    Quantum.coordinates psi ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis c))⟩)*weight

/-- The second endpoint remains an independent dual, with its original negative composition action. -/
def sourceDressedDualRead (channel spin : Fin 2) (phi : Scalar)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) : ℂ :=
  ∑c : Fin 3,star (scalarCoefficient channel c phi)*
    dual (Quantum.wholeBasis ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis c))⟩)

theorem sourceDressedGT_dual (channel spin : Fin 2) (phi : Scalar)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    sourceDressedDualRead channel spin (scalarMotherLieAction sourceFirstTemporalMother phi) dual+
      sourceDressedDualRead channel spin phi (-dual.comp sourceFirstTemporalGenerator)=
      (-((5/11:ℂ)*Complex.I))*sourceDressedDualRead channel spin phi dual := by
  simp only [sourceDressedDualRead,sourceDressedGT_scalar,LinearMap.neg_apply,LinearMap.comp_apply,
    sourceFirstTemporal_basis,sourceFirstWholeWeight,sourceFirstInternalWeight,map_smul,
    ←Finset.sum_add_distrib,Finset.mul_sum,map_mul,Complex.star_def,Complex.conj_I,
    map_ratCast,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _
  have weight : (sourceFirstExteriorWeight (Composite.scalarBasis channel c):ℂ)+
      (sourceFirstExteriorWeight (Composite.matterBasis c):ℂ)=(5/11:ℂ) := by
    have cast:=congrArg (fun q : ℚ=>(q:ℂ)) (sourceDressedGT_weight channel c)
    norm_num only [Rat.cast_add,Rat.cast_div] at cast
    exact cast
  simp only [starRingEnd_apply]
  linear_combination (-Complex.I*star (scalarCoefficient channel c phi)*
    dual (Quantum.wholeBasis ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis c))⟩))*weight

end LowEnergy.PreparationPhysicalDressedSpinChargeReturn
