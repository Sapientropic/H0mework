import H0mework.Versions.X.NavierStokes.WindowSchurMean.ResidualLoad
import H0mework.Versions.X.NavierStokes.StressWholeH1.Cancellation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanStrongBilinear
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeTimeJetCarrier NativeHigherTimeJets NativeEndpointVelocityCarrier
open NativeWholeH1Mixed (modes modes_zero modes_closed restrict row finiteRow)
open NativeWindowHistoryCreationGeometry (transport)
open NativeWindowHistoryAdjointSpatialHalf (moment outputSquare)
open NativeWindowHistoryAdjointSpatialFeedback (transportCap transportCap_nonnegative)
open NativeUnheatedSexticLatticePower (radical)
noncomputable section

theorem transport_stress (nu : Viscosity) (F : Finset IntegerWavevector) (zero : 0∉F)
    (closed : FiniteModeNegClosed F) (u v : physicalSpace F) (k : IntegerWavevector) (inside : k∈F) :
    (transport F zero closed nu u v).1 k=projectedDivergenceCLM k (mixedFlux u.1 v.1 k) := by
  have split:=congrArg (fun op : Module.End ℝ (physicalSpace F) => (op v).1 k)
    (NativeWindowOperatorGreen.operator_split F zero closed nu (curlLift F u.1)
      (curlLift_reality F closed u.1 (physical_reality (fun {_} member => closed _ member) u)))
  change frozenOperator F nu (curlLift F u.1) v.1 k=
    -nu.coeff • (NativeWindowOperatorGreen.laplacian F zero closed nu v).1 k+(transport F zero closed nu u v).1 k at split
  rw [NativeWindowOperatorGreen.laplacian_row,
    NativeConvectionFlux.operator_stress_row F nu (curlLift F u.1) v.1
      (fun q outside => by simp [curlLift,finiteComplexVorticityState_apply,outside])
      (physical_supported v) (physical_transverse v) k inside (fun eq => zero (eq ▸ inside)),
    NativeWholeH1Cancellation.curlLift_velocity F zero u] at split
  have paid:=congrArg (fun z : ComplexCoordinateVector => z+(nu.coeff*integerWaveViscousMultiplier k) • v.1 k) split
  simp only [sub_add_cancel,smul_smul,neg_mul,neg_smul] at paid
  convert paid.symm using 1
  abel

def density (n : ℕ) (v : wholePhysical) (k : IntegerWavevector) : ℝ :=
  radical k^(2*n)*‖euclideanCoordinateRow (wholeVelocity v.1 k)‖^2

def mass (n : ℕ) (v : wholePhysical) : ℝ := ∑'k,density n v k

def Regular (n : ℕ) (v : wholePhysical) : Prop := Summable (density n v)

theorem density_nonnegative (n : ℕ) (v : wholePhysical) (k : IntegerWavevector) : 0 ≤  density n v k := by
  unfold density
  positivity [NativeUnheatedSexticLatticePower.radical_positive k]

theorem mass_nonnegative (n : ℕ) (v : wholePhysical) : 0 ≤ mass n v :=
  tsum_nonneg (density_nonnegative n v)

theorem finite_moment (n M : ℕ) (v : wholePhysical) :
    moment (modes M) n (restrict M v)=∑k∈modes M,density n v k := by
  rw [NativeWindowHistoryAdjointSpatialHalf.moment_original]
  apply Finset.sum_congr rfl
  intro k member
  rw [NativeWholeH1Mixed.restrict_row,if_pos member]
  simp only [density,euclideanCoordinateRow,EuclideanSpace.norm_sq_eq]

theorem moment_bound (n M : ℕ) (v : wholePhysical) (regular : Regular n v) :
    moment (modes M) n (restrict M v) ≤  mass n v := by
  rw [finite_moment]
  exact regular.sum_le_tsum _ (fun k _ => density_nonnegative n v k)

theorem finite_strong (nu : Viscosity) (M : ℕ) (u v : wholePhysical) (ru : Regular 2 u) (rv : Regular 3 v) :
    (∑k∈modes M,‖euclideanCoordinateRow (finiteRow M u v k)‖^2) ≤ transportCap*mass 2 u*mass 3 v := by
  have source:=NativeWindowHistoryAdjointSpatialHalf.transport_bound true (modes M) (modes_zero M) (modes_closed M)
    nu (restrict M u) (restrict M v)
  have actual : outputSquare true (modes M) (transport (modes M) (modes_zero M) (modes_closed M) nu (restrict M u) (restrict M v))=
      ∑k∈modes M,‖euclideanCoordinateRow (finiteRow M u v k)‖^2 := by
    unfold outputSquare
    apply Finset.sum_congr rfl
    intro k inside
    rw [transport_stress nu (modes M) (modes_zero M) (modes_closed M) _ _ k inside]
    simp only [NativeWindowHistoryAdjointSpatialHalf.weight,if_true,one_pow,one_mul,
      finiteRow,euclideanCoordinateRow,EuclideanSpace.norm_sq_eq]
  rw [actual] at source
  have bounds:=mul_le_mul (moment_bound 2 M u ru) (moment_bound 3 M v rv)
    (NativeWindowHistoryAdjointSpatialHalf.moment_nonnegative _ _ _)
    (mass_nonnegative 2 u)
  exact source.trans (by simpa only [transportCap,NativeWindowHistoryAdjointSpatialHalf.inputOrder,if_true,mul_assoc]
    using mul_le_mul_of_nonneg_left bounds transportCap_nonnegative)

theorem divergence_zero (stress : ThreeDimensionalVorticityCoefficientNativeFluidMedium.NativeFluidStressCoefficient) :
    projectedDivergenceCLM 0 stress=0 := by
  rw [projectedDivergenceCLM_apply]
  have source : ThreeDimensionalVorticityCoefficientNativeFluidMedium.nativeFluidStressDivergenceCoefficient
      (fun _ => stress) 0=0 := by
    ext i
    simp [ThreeDimensionalVorticityCoefficientNativeFluidMedium.nativeFluidStressDivergenceCoefficient,complexWavevector]
  rw [source]
  change (ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory.transverseProjectionCLM 0) 0=0
  exact map_zero _


theorem observed_strong (nu : Viscosity) (u v : wholePhysical) (ru : Regular 2 u) (rv : Regular 3 v)
    (F : Finset IntegerWavevector) :
    (∑k∈F,‖euclideanCoordinateRow (row u v k)‖^2) ≤ transportCap*mass 2 u*mass 3 v := by
  have limit (k : IntegerWavevector) : Tendsto (fun M => ‖euclideanCoordinateRow (finiteRow M u v k)‖^2) atTop
      (𝓝 (‖euclideanCoordinateRow (row u v k)‖^2)) :=
    ((NativeCompleteStressAction.euclideanCLM.continuous.tendsto _).comp (NativeWholeH1Mixed.row_tendsto u v k)).norm.pow 2
  apply le_of_tendsto (tendsto_finsetSum F (fun k _ => limit k))
  filter_upwards [NativeWindowStressOseenSource.cover_eventually F] with M covers
  have included : F⊆insert 0 (modes M) := by
    intro k inside
    by_cases h:k=0
    · simp [h]
    · exact Finset.mem_insert_of_mem (covers k inside h)
  have sum:=(Finset.sum_le_sum_of_subset_of_nonneg included (fun k _ _ => sq_nonneg ‖euclideanCoordinateRow (finiteRow M u v k)‖))
  have atZero : finiteRow M u v 0=0 := by
    exact divergence_zero _
  rw [Finset.sum_insert (modes_zero M),atZero] at sum
  simp only [show euclideanCoordinateRow (0 : ComplexCoordinateVector)=0 from rfl,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_add] at sum
  exact sum.trans (finite_strong nu M u v ru rv)

theorem density_project (n M : ℕ) (v : wholePhysical) (k : IntegerWavevector) :
    density n (NativeWholeH1Approximation.project M v) k=if k∈modes M then density n v k else 0 := by
  simp only [density,NativeWholeH1Approximation.project_whole,NativeWholeH1Mixed.restrict_row]
  split_ifs <;> simp only [show euclideanCoordinateRow (0 : ComplexCoordinateVector)=0 from rfl,norm_zero,
    zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]

theorem density_difference (n M : ℕ) (v : wholePhysical) (k : IntegerWavevector) :
    density n (v-NativeWholeH1Approximation.project M v) k=if k∈modes M then 0 else density n v k := by
  have original : wholeVelocity (v-NativeWholeH1Approximation.project M v).1=
      wholeVelocity v.1-wholeVelocity (NativeWholeH1Approximation.project M v).1 := by
    exact wholeVelocityCLM.map_sub _ _
  simp only [density,original,NativeWholeH1Approximation.project_whole,NativeWholeH1Mixed.restrict_row,lp.coeFn_sub,Pi.sub_apply]
  split_ifs <;> simp only [sub_self,sub_zero,show euclideanCoordinateRow (0 : ComplexCoordinateVector)=0 from rfl,
    norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]

theorem regular_project (n M : ℕ) (v : wholePhysical) (paid : Regular n v) :
    Regular n (NativeWholeH1Approximation.project M v) :=
  paid.of_nonneg_of_le (density_nonnegative n _) (fun k => by rw [density_project]; split_ifs <;>
    first | exact le_rfl | exact density_nonnegative n v k)

theorem mass_project (n M : ℕ) (v : wholePhysical) (paid : Regular n v) :
    mass n (NativeWholeH1Approximation.project M v) ≤  mass n v := by
  apply (regular_project n M v paid).tsum_le_tsum _ paid
  intro k
  rw [density_project]
  split_ifs <;> first | exact le_rfl | exact density_nonnegative n v k

theorem regular_difference (n M : ℕ) (v : wholePhysical) (paid : Regular n v) :
    Regular n (v-NativeWholeH1Approximation.project M v) :=
  paid.of_nonneg_of_le (density_nonnegative n _) (fun k => by rw [density_difference]; split_ifs <;>
    first | exact le_rfl | exact density_nonnegative n v k)

theorem density_two_le_three (v : wholePhysical) (k : IntegerWavevector) : density 2 v k ≤  density 3 v k := by
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_right₀ (Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (NativeUnheatedSexticLatticePower.mass_one k))) (by norm_num)

theorem regular_two (v : wholePhysical) (paid : Regular 3 v) : Regular 2 v :=
  paid.of_nonneg_of_le (density_nonnegative 2 v) (density_two_le_three v)

theorem mass_two (v : wholePhysical) (paid : Regular 3 v) : mass 2 v ≤  mass 3 v :=
  (regular_two v paid).tsum_le_tsum (density_two_le_three v) paid

theorem observed_difference (nu : Viscosity) (M : ℕ) (v : wholePhysical) (regular : Regular 3 v)
    (F : Finset IntegerWavevector) :
    (∑k∈F,‖euclideanCoordinateRow (row v v k-finiteRow M v v k)‖^2) ≤
      4*transportCap*mass 3 v*mass 3 (v-NativeWholeH1Approximation.project M v) := by
  let p:=NativeWholeH1Approximation.project M v
  let d:=v-p
  have projected (k : IntegerWavevector) : row p p k=finiteRow M v v k := by
    simp only [row,p,NativeWholeH1Approximation.project_whole,finiteRow]
  have rp:=regular_project 3 M v regular
  have rd:=regular_difference 3 M v regular
  have first:=observed_strong nu d v (regular_two d rd) regular F
  have last:=observed_strong nu p d (regular_two p rp) rd F
  have same (k : IntegerWavevector) : row v v k-finiteRow M v v k=row d v k+row p d k := by
    rw [← projected]
    rw [show row d v k=row v v k-row p v k from NativeWholeH1Approximation.row_sub_left v p v k,
      show row p d k=row p v k-row p p k from NativeWholeH1Approximation.row_sub_right p v p k]
    abel
  have point (k : IntegerWavevector) : ‖euclideanCoordinateRow (row v v k-finiteRow M v v k)‖^2 ≤
      2*(‖euclideanCoordinateRow (row d v k)‖^2+‖euclideanCoordinateRow (row p d k)‖^2) := by
    rw [same]
    change ‖NativeCompleteStressAction.euclideanCLM (row d v k+row p d k)‖^2 ≤ _
    rw [map_add]
    change ‖euclideanCoordinateRow (row d v k)+euclideanCoordinateRow (row p d k)‖^2 ≤ _
    have triangle:=pow_le_pow_left₀ (norm_nonneg _) (norm_add_le
      (euclideanCoordinateRow (row d v k)) (euclideanCoordinateRow (row p d k))) 2
    nlinarith only [triangle,sq_nonneg (‖euclideanCoordinateRow (row d v k)‖-‖euclideanCoordinateRow (row p d k)‖)]
  have sums:=Finset.sum_le_sum (s := F) (fun k _ => point k)
  rw [← Finset.mul_sum,Finset.sum_add_distrib] at sums
  have firstBound:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mass_two d rd) transportCap_nonnegative)
    (mass_nonnegative 3 v)
  have lastBound:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((mass_two p rp).trans (mass_project 3 M v regular))
    transportCap_nonnegative) (mass_nonnegative 3 d)
  nlinarith only [sums,first,last,firstBound,lastBound]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanStrongBilinear
