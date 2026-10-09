import H0mework.Physics.LowEnergy.PacketField.BandPole
import H0mework.Physics.LowEnergy.PacketField.Extension
import H0mework.Physics.LowEnergy.PacketPairResponse.Slope

/-! The original current drives every primitive pole field. Source-generated
radial and circle bounds give its strong measurability and actual L² existence. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace PacketPairResponse
noncomputable section
attribute [local irreducible] PacketFourier.phasePacket phaseBranch poleColumn
variable {ι : Type*} [Fintype ι]

def branchOnBand (energy damping : ℝ) (positive : 0 < damping) (sign : Bool) (time : ℝ) (point : LightBand) :
    FullMatterL2 := phaseBranch energy damping positive (bandShift point) time sign

theorem branchOnBand_continuous (energy damping : ℝ) (positive : 0 < damping) (sign : Bool) (time : ℝ) :
    Continuous (branchOnBand energy damping positive sign time) := by
  have path : Continuous (fun point : LightBand => (point,time)) := continuous_id.prodMk continuous_const
  have slope := (bandSlope_continuous energy damping positive true sign).comp path
  have scaled : Continuous (fun point : LightBand => time • bandSlope energy damping positive true sign point time) := by
    simpa using! slope.const_smul time
  have same : branchOnBand energy damping positive sign time=
      fun point => time • bandSlope energy damping positive true sign point time := by
    funext point
    exact phaseBranch_slope energy damping positive true sign point time
  rw [same]
  exact scaled

theorem branchOnBand_bounded (energy damping : ℝ) (positive : 0 < damping) (sign : Bool) (time : ℝ) :
    ∃ bound : ℝ, 0≤bound ∧ ∀ point, ‖branchOnBand energy damping positive sign time point‖≤bound := by
  obtain ⟨bound,upper⟩ := isCompact_univ.bddAbove_image
    (branchOnBand_continuous energy damping positive sign time).norm.continuousOn
  exact ⟨max bound 0,le_max_right _ _,fun point =>
    (upper (Set.mem_image_of_mem _ (Set.mem_univ point))).trans (le_max_left _ _)⟩

def retardedField (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (point : LightBand) (row : ι) : FullMatterL2 :=
  -(∑ sign : Bool, poleColumn circleY circleZ numerator sign point row • branchOnBand energy damping positive sign time point)

theorem retardedField_stronglyMeasurable (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (row : ι) :
    StronglyMeasurable (fun point => retardedField circleY circleZ numerator energy damping positive time point row) := by
  unfold retardedField
  apply StronglyMeasurable.neg
  have generated := Finset.stronglyMeasurable_sum (Finset.univ : Finset Bool) (fun sign _ =>
    (poleColumn_measurable circleY circleZ numerator sign row).stronglyMeasurable.smul
      (branchOnBand_continuous energy damping positive sign time).stronglyMeasurable)
  simpa only [Finset.sum_apply,Pi.smul_apply] using! generated

theorem retardedField_bounded (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (row : ι) :
    ∃ bound : ℝ, 0≤bound ∧ ∀ point, ‖retardedField circleY circleZ numerator energy damping positive time point row‖≤bound := by
  choose poleBound poleBounded using (fun sign => poleColumn_bounded circleY circleZ numerator sign)
  choose branchBound branchNonnegative branchBounded using (fun sign => branchOnBand_bounded energy damping positive sign time)
  refine ⟨∑ sign : Bool, max (poleBound sign row) 0*branchBound sign,?_,?_⟩
  · exact Finset.sum_nonneg (fun sign _ => mul_nonneg (le_max_right _ _) (branchNonnegative sign))
  · intro point
    rw [retardedField,norm_neg]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro sign _
    rw [norm_smul]
    exact mul_le_mul ((poleBounded sign point row).trans (le_max_left _ _))
      (branchBounded sign point) (norm_nonneg _) (le_max_right _ _)

theorem retardedField_memLp (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (row : ι) :
    MemLp (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point row))
      2 (volume : Measure Position) := by
  obtain ⟨bound,nonnegative,bounded⟩ := retardedField_bounded circleY circleZ numerator energy damping positive time row
  exact extendBand_memLp _ (retardedField_stronglyMeasurable circleY circleZ numerator energy damping positive time row)
    bound nonnegative bounded

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
