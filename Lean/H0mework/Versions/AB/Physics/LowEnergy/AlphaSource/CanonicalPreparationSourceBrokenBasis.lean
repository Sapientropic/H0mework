import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceChartGuard

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceMatrixInverse
open PreparationVacuumSourceChartBudget PreparationChartGuard PreparationPhaseScalar
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice
open scoped BigOperators RealInnerProductSpace

def normalBuildLinear : NormalCoordinates →ₗ[ℝ] NativeLie where
  toFun := normalBuild
  map_add' x y := by
    apply nativeCoordinates.injective
    simp only [normalBuild,map_add,LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · ext i; fin_cases i <;> simp [PiLp.add_apply]
    · apply Prod.ext
      · ext i; fin_cases i <;> simp [PiLp.add_apply]
      · simp [PiLp.add_apply]
  map_smul' r x := by
    apply nativeCoordinates.injective
    simp only [normalBuild,map_smul,LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · ext i; fin_cases i <;> simp [PiLp.smul_apply]
    · apply Prod.ext
      · ext i; fin_cases i <;> simp [PiLp.smul_apply]
      · simp [PiLp.smul_apply]

def normalReadLinear : NativeLie →ₗ[ℝ] NormalCoordinates where
  toFun := normalRead
  map_add' a b := by
    ext i
    fin_cases i <;> simp [normalRead,map_add,PiLp.add_apply,PiLp.toLp_apply]
  map_smul' r a := by
    ext i
    fin_cases i <;> simp [normalRead,map_smul,PiLp.smul_apply,PiLp.toLp_apply]

theorem normalRead_build (x : NormalCoordinates) : normalReadLinear (normalBuildLinear x)=x := by
  ext i
  fin_cases i <;> simp [normalReadLinear,normalBuildLinear,normalRead,normalBuild,PiLp.toLp_apply]

theorem normalRead_stabilizer (a : stabilizer) : normalReadLinear a.val=0 := by
  obtain ⟨v,rfl⟩ := colorStabilizerEquiv.surjective a
  change normalReadLinear (colorCombination v)=0
  ext i
  fin_cases i <;> simp [normalReadLinear,normalRead,colorCombination_coordinates,PiLp.toLp_apply]

def brokenBuild : NormalCoordinates →ₗ[ℝ] broken :=
  broken.orthogonalProjectionOnto.toLinearMap.comp normalBuildLinear

def brokenRead : broken →ₗ[ℝ] NormalCoordinates := normalReadLinear.comp broken.subtype

theorem brokenRead_build (x : NormalCoordinates) : brokenRead (brokenBuild x)=x := by
  have residual : (normalBuildLinear x)-(brokenBuild x).val ∈ stabilizer := by
    have original := broken.sub_starProjection_mem_orthogonal (normalBuildLinear x)
    simpa only [brokenBuild,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,
      Submodule.coe_orthogonalProjectionOnto_apply,broken,Submodule.orthogonal_orthogonal] using original
  have zero := normalRead_stabilizer ⟨_,residual⟩
  change normalReadLinear ((normalBuildLinear x)-(brokenBuild x).val)=0 at zero
  rw [map_sub,normalRead_build] at zero
  exact (sub_eq_zero.mp zero).symm

theorem brokenBuild_read (a : broken) : brokenBuild (brokenRead a)=a := by
  apply sub_eq_zero.mp
  apply broken_zero_of_normal_zero
  change brokenRead (brokenBuild (brokenRead a)-a)=0
  rw [map_sub,brokenRead_build,sub_self]

def brokenCoordinates : broken ≃ₗ[ℝ] NormalCoordinates where
  toFun := brokenRead
  invFun := brokenBuild
  left_inv := brokenBuild_read
  right_inv := brokenRead_build
  map_add' := brokenRead.map_add
  map_smul' := brokenRead.map_smul

theorem sourceBroken_build (i : Fin 9) : brokenBuild (sourceNormal i)=sourceBroken i := rfl

theorem sourceNormal_expansion (x : NormalCoordinates) : x=∑ i : Fin 9,x i • sourceNormal i := by
  ext j
  simp [sourceNormal,Pi.single_apply]

theorem sourceBroken_expansion (a : broken) :
    a=∑ j : Fin 9,brokenCoordinates a j • sourceBroken j := by
  calc
    a=brokenBuild (brokenCoordinates a) := (brokenBuild_read a).symm
    _=brokenBuild (∑ j : Fin 9,brokenCoordinates a j • sourceNormal j) :=
      congrArg brokenBuild (sourceNormal_expansion (brokenCoordinates a))
    _=∑ j : Fin 9,brokenCoordinates a j • sourceBroken j := by
      rw [map_sum]
      simp only [map_smul,sourceBroken_build]

theorem sourceD9_pair_coordinates (phi : Scalar) (a : broken) (i : Fin 9) :
    inner ℝ (orbit (normalBuild (sourceNormal i))) (action phi a.val)=
      ∑ j : Fin 9,sourceD9 phi i j*brokenCoordinates a j := by
  nth_rw 1 [sourceBroken_expansion a]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,inner_sum,
    real_inner_smul_right]
  change (∑ j : Fin 9,brokenCoordinates a j*sourceD9 phi i j)=_
  apply Finset.sum_congr rfl
  intro j _
  ring

end LowEnergy.PreparationVacuumSourceMatrixInverse
