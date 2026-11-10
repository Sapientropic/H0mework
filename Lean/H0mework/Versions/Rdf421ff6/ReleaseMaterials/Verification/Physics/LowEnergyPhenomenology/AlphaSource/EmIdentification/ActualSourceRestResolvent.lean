import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceMovingSylvester
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualMovingSourceLight
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ActualSourcePreparationBridge ActualSourceLightCircuit
open PreparationVacuumElectromagneticIdentity CanonicalGradedSpatialSource
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert
open SourceQuantumConfigurationHilbert PreparationVacuumRawJointFeedback
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local irreducible] actualMovingSourceSylvester actualSourceBlockHamiltonian
  PreparationVacuumSourceFieldFamily.sourceState sourceHSSylvester actualMatterCarrierHamiltonian
  sourceHSCoordinates
local instance restCompleteHS : CompleteSpace HS:=PiLp.completeSpace 2 (fun _ : HSIndex=>ℂ)
local instance restCompleteOperator : CompleteSpace HSOperator:=ContinuousLinearMap.instCompleteSpace
local instance restResolventRational : NormedAlgebra ℚ HSOperator:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance restResolventReal : NormedAlgebra ℝ HSOperator:=NormedAlgebra.restrictScalars ℝ ℂ _

/-- These are the original matching rates, in the actual rest-preparation HS coordinates. -/
def sourceRestHSRate (block : RestBlock) (index : HSIndex) : ℂ :=
  (if block.1 then (-1 : ℂ) else 1)*(
    if index.1=0 ∧ index.2≠0 then -sourceRestMatchingEigenvalue block.2
    else if index.1≠0 ∧ index.2=0 then sourceRestMatchingEigenvalue block.2 else 0)

def sourceRestHSGenerator (block : RestBlock) : HSOperator :=
  (Matrix.toEuclideanCLM (n:=HSIndex) (𝕜:=ℂ)) (Matrix.diagonal (sourceRestHSRate block))

def sourceRestHSResolvent (block : RestBlock) (spectral : ℂ) : HSOperator :=
  (Matrix.toEuclideanCLM (n:=HSIndex) (𝕜:=ℂ)) (Matrix.diagonal (fun index=>(spectral-sourceRestHSRate block index)⁻¹))

private theorem actual_primal_moving_sylvester_at_rest (side : Fin 2) :
    actualMovingSourceSylvester (false,side) 0 0 (0,GaussHistoryHilbert.sourcePoint.val)=sourceRestHSGenerator (false,side) := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨B,rfl⟩:=sourceHSCoordinates.surjective v
  unfold actualMovingSourceSylvester
  rw [ambientState_zero]
  rw [actual_source_block_hamiltonian_at_source,source_HS_sylvester_value,matching_clock_same_source]
  have atRest := actualMatterMatchingSylvester_atRest 0 side B
  change (Complex.I/(sourceRestMatchingClock:ℂ)) •
    (actualMatterCarrierHamiltonian 0 side 0*B-B*actualMatterCarrierHamiltonian 0 side 0)=
      actualRestMatchingSylvester 0 side B at atRest
  rw [atRest,actualRestMatchingSylvester_spectral]
  unfold sourceHSCoordinates sourceRestHSGenerator
  apply PiLp.ext
  intro index
  change (-sourceRestMatchingEigenvalue side)*sourceRestHeavyUp B index.1 index.2+
    sourceRestMatchingEigenvalue side*sourceRestHeavyDown B index.1 index.2=
      (Matrix.diagonal (sourceRestHSRate (false,side))*ᵥ(fun i=>B i.1 i.2)) index
  rw [Matrix.mulVec_diagonal]
  by_cases left : index.1=0 <;> by_cases right : index.2=0 <;>
    simp [sourceRestHSRate,sourceRestHeavyUp,sourceRestHeavyDown,left,right]

private theorem source_rest_energy_star (side : Fin 2) : (sourceRestEnergyMatrix side).map star=sourceRestEnergyMatrix side := by
  ext i j
  by_cases same : i=j
  · subst j
    simp only [sourceRestEnergyMatrix,Matrix.diagonal_apply,Matrix.map_apply]
    by_cases zero : i=0 <;> fin_cases side <;>
      simp [sourceRestPoleEnergy,sourceRestStatePole,sourceRestSign,sourceRestSymmetry,zero]
  · simp [sourceRestEnergyMatrix,same]

/-- Both actual source branches have their generated signed rest spectra on the same HS space. -/
theorem actual_moving_sylvester_at_rest (block : RestBlock) :
    actualMovingSourceSylvester block 0 0 (0,GaussHistoryHilbert.sourcePoint.val)=sourceRestHSGenerator block := by
  rcases block with ⟨dual,side⟩
  cases dual
  · exact actual_primal_moving_sylvester_at_rest side
  · have energy : actualSourceBlockHamiltonian (false,side) 0
        (PreparationVacuumSourceFieldFamily.sourceState GaussHistoryHilbert.sourcePoint.val)=sourceRestEnergyMatrix side := by
      rw [actual_source_block_hamiltonian_at_source]
      have original:=actualRestCarrierHamiltonian_generated 0 side
      unfold actualMatterCarrierHamiltonian
      unfold actualRestCarrierHamiltonian at original
      exact original
    have dualEnergy:=actual_source_dual_block_hamiltonian side 0
      (PreparationVacuumSourceFieldFamily.sourceState GaussHistoryHilbert.sourcePoint.val)
    rw [neg_zero,energy,source_rest_energy_star] at dualEnergy
    have signed : actualMovingSourceSylvester (true,side) 0 0 (0,GaussHistoryHilbert.sourcePoint.val)=
        -actualMovingSourceSylvester (false,side) 0 0 (0,GaussHistoryHilbert.sourcePoint.val) := by
      unfold actualMovingSourceSylvester
      rw [ambientState_zero,dualEnergy,energy]
      change sourceHSSylvester (-(sourceRestEnergyMatrix side,sourceRestEnergyMatrix side))=
        -sourceHSSylvester (sourceRestEnergyMatrix side,sourceRestEnergyMatrix side)
      exact map_neg _ _
    rw [signed,actual_primal_moving_sylvester_at_rest]
    unfold sourceRestHSGenerator
    rw [←map_neg]
    apply congrArg (Matrix.toEuclideanCLM (n:=HSIndex) (𝕜:=ℂ))
    ext i j
    by_cases same : i=j
    · subst j
      by_cases left : i.1=0 <;> by_cases right : i.2=0 <;>
        simp [sourceRestHSRate,left,right]
    · simp [same]

theorem source_rest_rate_norm (block : RestBlock) (index : HSIndex) :
    ‖sourceRestHSRate block index‖=if (index.1=0 ↔ index.2=0) then 0 else 6/5 := by
  rcases block with ⟨dual,side⟩
  have normRate : ‖sourceRestMatchingEigenvalue side‖=6/5 := by
    fin_cases side <;> norm_num [sourceRestMatchingEigenvalue,sourceRestSign,norm_mul]
  by_cases left : index.1=0 <;> by_cases right : index.2=0 <;>
    cases dual <;> simp [sourceRestHSRate,left,right,normRate]

/-- The original source spectrum puts the complete circle1/4 in the true rest resolvent set. -/
theorem source_rest_circle_denominator (block : RestBlock) (spectral : ℂ) (circle : ‖spectral‖=1/4)
    (index : HSIndex) : 1/4≤‖spectral-sourceRestHSRate block index‖ := by
  have rate:=source_rest_rate_norm block index
  by_cases light : (index.1=0 ↔ index.2=0)
  · have zero : sourceRestHSRate block index=0 := by
      apply norm_eq_zero.mp;rw [rate,if_pos light]
    rw [zero,sub_zero,circle]
  · rw [if_neg light] at rate
    have triangle:=norm_sub_norm_le (sourceRestHSRate block index) spectral
    rw [norm_sub_rev,rate,circle] at triangle
    linarith

private theorem source_rest_inverse_product (block : RestBlock) (spectral : ℂ)
    (nonzero : ∀index : HSIndex,spectral-sourceRestHSRate block index≠0) :
    (spectral • (1 : HSOperator)-sourceRestHSGenerator block)*sourceRestHSResolvent block spectral=1 ∧
      sourceRestHSResolvent block spectral*(spectral • (1 : HSOperator)-sourceRestHSGenerator block)=1 := by
  have matrix : spectral • (1 : HSOperator)-sourceRestHSGenerator block=
      (Matrix.toEuclideanCLM (n:=HSIndex) (𝕜:=ℂ)) (Matrix.diagonal (fun i=>spectral-sourceRestHSRate block i)) := by
    unfold sourceRestHSGenerator
    rw [←map_one ((Matrix.toEuclideanCLM (n:=HSIndex) (𝕜:=ℂ))),←map_smul,←map_sub]
    congr 1
    ext i j
    by_cases same : i=j <;> simp [same]
  rw [matrix,sourceRestHSResolvent,←map_mul,←map_mul]
  constructor <;> rw [←map_one (Matrix.toEuclideanCLM (n:=HSIndex) (𝕜:=ℂ))]
  all_goals apply congrArg (Matrix.toEuclideanCLM (n:=HSIndex) (𝕜:=ℂ))
  all_goals rw [Matrix.diagonal_mul_diagonal]
  all_goals
    ext i j
    by_cases same : i=j
    · subst j
      simp only [Matrix.diagonal_apply,Matrix.one_apply,ite_true]
      first | exact mul_inv_cancel₀ (nonzero i) | exact inv_mul_cancel₀ (nonzero i)
    · simp only [Matrix.diagonal_apply,Matrix.one_apply,same,if_false]

def sourceRestCircleUnit (block : RestBlock) (spectral : ℂ) (circle : ‖spectral‖=1/4) : HSOperatorˣ where
  val:=spectral • 1-sourceRestHSGenerator block
  inv:=sourceRestHSResolvent block spectral
  val_inv:=(source_rest_inverse_product block spectral (fun i=>
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (source_rest_circle_denominator block spectral circle i)))).1
  inv_val:=(source_rest_inverse_product block spectral (fun i=>
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (source_rest_circle_denominator block spectral circle i)))).2

/-- Source-generated resolvent norm on the whole fixed contour; no arbitrary spectral certificate is assumed. -/
theorem source_rest_circle_resolvent_price (block : RestBlock) (spectral : ℂ) (circle : ‖spectral‖=1/4) :
    ‖sourceRestHSResolvent block spectral‖≤4 := by
  rw [sourceRestHSResolvent,Matrix.l2_opNorm_toEuclideanCLM,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro index
  rw [norm_inv]
  have gap:=source_rest_circle_denominator block spectral circle index
  calc
    _≤(1/4:ℝ)⁻¹ := (inv_le_inv₀ (lt_of_lt_of_le (by norm_num) gap) (by norm_num)).mpr gap
    _=4 := by norm_num

/-- Every actual matrix in the strict source Neumann tube has a source-generated unit on circle1/4. -/
theorem actual_moving_circle_isUnit (block : RestBlock) (S : HSOperator) (spectral : ℂ) (circle : ‖spectral‖=1/4)
    (small : ‖S-sourceRestHSGenerator block‖<1/4) : IsUnit (spectral • (1 : HSOperator)-S) := by
  let unit:=sourceRestCircleUnit block spectral circle
  have inverse : (↑unit⁻¹ : HSOperator)=sourceRestHSResolvent block spectral:=rfl
  have bound:=source_rest_circle_resolvent_price block spectral circle
  have difference : (spectral • (1 : HSOperator)-S)-(↑unit : HSOperator)=
      -(S-sourceRestHSGenerator block) := by
    change (spectral • 1-S)-(spectral • 1-sourceRestHSGenerator block)=_
    abel
  have paid : ‖(spectral • (1 : HSOperator)-S)-(↑unit : HSOperator)‖<‖(↑unit⁻¹ : HSOperator)‖⁻¹ := by
    rw [difference,norm_neg,inverse]
    have lower : (1/4:ℝ)≤‖sourceRestHSResolvent block spectral‖⁻¹ := by
      have positive : 0<‖sourceRestHSResolvent block spectral‖:=by simpa only [inverse] using Units.norm_pos unit⁻¹
      calc
        (1/4:ℝ)=(4:ℝ)⁻¹ :=by norm_num
        _≤_ :=(inv_le_inv₀ (by norm_num) positive).mpr bound
    exact small.trans_le lower
  exact (unit.ofNearby (spectral • 1-S) paid).isUnit

/-- The actual source perturbation budget pays the complete contour inverse, including its generated denominator. -/
theorem actual_moving_circle_resolvent_price (block : RestBlock) (S : HSOperator) (spectral : ℂ) (circle : ‖spectral‖=1/4)
    (small : ‖S-sourceRestHSGenerator block‖<1/8) :
    ‖Ring.inverse (spectral • (1 : HSOperator)-S)‖≤8 := by
  let unit:=sourceRestCircleUnit block spectral circle
  let R:=sourceRestHSResolvent block spectral
  let E:=S-sourceRestHSGenerator block
  let T:=R*E
  have rbound : ‖R‖≤4:=source_rest_circle_resolvent_price block spectral circle
  have tbound : ‖T‖<1/2 := by
    have product : ‖T‖≤4*‖E‖:=(norm_mul_le R E).trans
      (mul_le_mul_of_nonneg_right rbound (norm_nonneg E))
    have esmall : ‖E‖<1/8:=small
    linarith
  have tsmall : ‖T‖<1:=tbound.trans (by norm_num)
  have inverseBound : ‖Ring.inverse (1-T)‖≤2 := by
    have bound:=tsum_geometric_le_of_norm_lt_one T tsmall
    have series : Ring.inverse (1-T)=∑'n : ℕ,T^n:=NormedRing.inverse_one_sub T tsmall
    rw [←series,norm_one,sub_self,zero_add] at bound
    have denominator : (1-‖T‖)⁻¹≤2 := by
      apply (inv_le_iff_one_le_mul₀ (by linarith)).mpr
      linarith
    exact bound.trans denominator
  have factor : spectral • (1 : HSOperator)-S=(↑unit : HSOperator)*(1-T) := by
    change spectral • 1-S=(spectral • 1-sourceRestHSGenerator block)*(1-R*(S-sourceRestHSGenerator block))
    rw [mul_sub,mul_one,←mul_assoc]
    have paid : (spectral • (1 : HSOperator)-sourceRestHSGenerator block)*R=1:=unit.val_inv
    rw [paid,one_mul]
    abel
  rw [factor,Ring.inverse_mul (Or.inl unit.isUnit),Ring.inverse_unit]
  change ‖Ring.inverse (1-T)*R‖≤8
  exact (norm_mul_le _ _).trans ((mul_le_mul inverseBound rbound (norm_nonneg R) (by norm_num)).trans (by norm_num))

end LowEnergy.GaussComposite.ActualMovingSourceLight
