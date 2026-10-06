import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.GaussComposite
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCutoffVolterra

/-! The source composite letters change Number and retain the actual Yukawa
grade. This is the original degree-six occupation, not a fitted charge. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open GaussCoreHilbert GaussCoreDifferential GaussFockLift GaussFockLabel
open GaussYukawaGrade NativeHistoryGrade
open scoped ContDiff InnerProductSpace BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance labelFintype : Fintype Label := Fintype.ofFinite _

theorem mode_not_target (spin : Fin 2) (color : Fin 3) : mode spin color ∉ target := by
  simp [mode,mem_target_left,isSix]

theorem fiber_annihilation_grade (spin : Fin 2) (color : Fin 3) :
    Commute fiberGrade (GaussCARHistory.annihilateFiber (mode spin color)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  change fiberCoordinates (fiberGrade (GaussCARHistory.annihilateFiber (mode spin color) f)) =
    fiberCoordinates (GaussCARHistory.annihilateFiber (mode spin color) (fiberGrade f))
  rw [fiber_coordinates_grade]
  change SourceFockRaising.grade target
      (LowEnergy.Fermion.annihilation (mode spin color) (fiberCoordinates f)) =
    LowEnergy.Fermion.annihilation (mode spin color) (fiberCoordinates (fiberGrade f))
  rw [fiber_coordinates_grade]
  have h := LowEnergy.Fermion.occupationCharge_annihilation
    (fun i : Mode => if i∈target then (1:ℂ) else 0) (mode spin color)
  simp only [mode_not_target,if_false,zero_smul,sub_zero] at h
  have he : SourceFockRaising.grade target = LowEnergy.Fermion.occupationCharge
      (fun i : Mode => if i∈target then (1:ℂ) else 0) := by
    unfold SourceFockRaising.grade
    congr 1
    funext i
    by_cases hi : i∈target <;> simp [hi]
  rw [he]
  exact LinearMap.congr_fun h (fiberCoordinates f)

theorem fiber_creation_grade (spin : Fin 2) (color : Fin 3) :
    Commute fiberGrade (GaussCARHistory.createFiber (mode spin color)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  change fiberCoordinates (fiberGrade (GaussCARHistory.createFiber (mode spin color) f)) =
    fiberCoordinates (GaussCARHistory.createFiber (mode spin color) (fiberGrade f))
  rw [fiber_coordinates_grade]
  change SourceFockRaising.grade target
      (LowEnergy.Fermion.creation (mode spin color) (fiberCoordinates f)) =
    LowEnergy.Fermion.creation (mode spin color) (fiberCoordinates (fiberGrade f))
  rw [fiber_coordinates_grade]
  have h := LowEnergy.Fermion.occupationCharge_creation
    (fun i : Mode => if i∈target then (1:ℂ) else 0) (mode spin color)
  simp only [mode_not_target,if_false,zero_smul,add_zero] at h
  have he : SourceFockRaising.grade target = LowEnergy.Fermion.occupationCharge
      (fun i : Mode => if i∈target then (1:ℂ) else 0) := by
    unfold SourceFockRaising.grade
    congr 1
    funext i
    by_cases hi : i∈target <;> simp [hi]
  rw [he]
  exact LinearMap.congr_fun h (fiberCoordinates f)

theorem lift_blockWeight (c : Label → ℂ) :
    lift (blockWeight c) = ∑ g : Label, c g • projection g := by
  apply ContinuousLinearMap.ext
  intro f
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  rw [lift_apply,LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro word
  simp only [flatLift_apply,entry,blockWeight_apply,EuclideanSpace.single]
  simp only [GaussHalfDensity.fockHalfDensityEquiv,LinearIsometryEquiv.piLpCongrRight_apply,
    sum_apply,smul_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,projection_apply]
  simp [Finset.sum_ite_eq,eq_comm,ite_smul,smul_ite,map_smul]

theorem grade_lift : lift fiberGrade = GaussYukawaGrade.grade := by
  exact lift_blockWeight (fun g => (g.2.val : ℂ))

theorem annihilation_grade (spin : Fin 2) (color : Fin 3) :
    Commute GaussYukawaGrade.grade (GaussCARHistory.annihilate (mode spin color)) := by
  show GaussYukawaGrade.grade * GaussCARHistory.annihilate (mode spin color) = _
  rw [←grade_lift,GaussCARHistory.annihilate,←lift_mul,←lift_mul]
  exact congrArg lift (fiber_annihilation_grade spin color).eq

theorem creation_grade (spin : Fin 2) (color : Fin 3) :
    Commute GaussYukawaGrade.grade (GaussCARHistory.create (mode spin color)) := by
  show GaussYukawaGrade.grade * GaussCARHistory.create (mode spin color) = _
  rw [←grade_lift,GaussCARHistory.create,←lift_mul,←lift_mul]
  exact congrArg lift (fiber_creation_grade spin color).eq

theorem scalar_multiplier_grade (c : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice → ℂ)
    (smooth : ContDiff ℝ ∞ c) (f : QuantumTest) :
    gradeCore (scalarMultiplier c smooth f) = scalarMultiplier c smooth (gradeCore f) := by
  apply DFunLike.ext
  intro z
  change fiberGrade (c z • f z) = c z • fiberGrade (f z)
  exact map_smul fiberGrade (c z) (f z)

theorem annihilation_source_grade (channel spin : Fin 2) (f : QuantumTest) :
    GaussYukawaGrade.grade (annihilationSource channel spin f) = annihilationSource channel spin (gradeCore f) := by
  rw [annihilation_source_apply,annihilation_source_apply,map_sum]
  apply Finset.sum_congr rfl
  intro color _
  have h := congrArg (fun A : H →L[ℂ] H => A
    (embed (scalarMultiplier (coefficient channel color) (coefficient_smooth channel color) f)))
      (annihilation_grade spin color).eq
  change GaussYukawaGrade.grade (GaussCARHistory.annihilate _ _) =
    GaussCARHistory.annihilate _ (GaussYukawaGrade.grade _) at h
  rw [h]
  rw [grade_core,scalar_multiplier_grade]

theorem creation_source_grade (channel spin : Fin 2) (f : QuantumTest) :
    GaussYukawaGrade.grade (creationSource channel spin f) =
      creationSource channel spin (gradeCore f) := by
  simp only [creationSource,LinearMap.sum_apply,LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe,map_sum]
  apply Finset.sum_congr rfl
  intro color _
  have h (x : H) := congrArg (fun A : H →L[ℂ] H => A x) (creation_grade spin color).eq
  change ∀ x : H, GaussYukawaGrade.grade (GaussCARHistory.create (mode spin color) x) =
    GaussCARHistory.create (mode spin color) (GaussYukawaGrade.grade x) at h
  rw [h,grade_core,scalar_multiplier_grade]

theorem leg_source_grade (addition : Bool) (channel spin : Fin 2) (f : QuantumTest) :
    GaussYukawaGrade.grade (leg addition channel spin f) =
      leg addition channel spin (gradeCore f) := by
  cases addition
  · exact annihilation_source_grade channel spin f
  · exact creation_source_grade channel spin f

end LowEnergy.GaussComposite
