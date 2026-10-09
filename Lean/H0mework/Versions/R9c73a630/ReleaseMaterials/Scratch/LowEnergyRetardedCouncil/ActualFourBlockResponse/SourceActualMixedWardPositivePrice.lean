import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorBulkSourcePrice
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeScalarInverseEnergyBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedWardPositivePrice
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussLiveMomentum GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarInverseNativeEnergy SourceClockPhiSecondPressure
open SourceScalarPositiveBulkWard SourceScalarAffineCutoffTail SourceInverseFixedEnergyTail
open SourceResolventBandLimit FullYSourceResolventGraphSplice ActualVectorJointCost
open ActualVectorBulkSourcePrice
open Lean Meta Elab Term
open scoped InnerProductSpace ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

elab "paid_positive_bulk%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorBulkSourcePrice 0) "LowEnergy") "ActualVectorBulkSourcePrice"
  let name:=Name.str ns field.getId.toString
  unless (←getEnv).contains name do throwError "Missing actual outer-resolvent source price"
  mkConstWithFreshMVarLevels name

/-- The coefficients are the original full-CAR real-linear source maps, including the
independent adjoint branch. The column displacement is the source half-vacuum. -/
def shiftedY (sharp:Bool) : End :=
  ∑a:ScalarIndex,constantAction sharp (scalarBasis a)*shiftedColumn a

private theorem source_columns (sharp:Bool)(v:Scalar)(x:FockFiber) :
    (∑a:ScalarIndex,branchMap sharp (scalarBasis a) ((inner ℝ v (scalarBasis a):ℂ) • x))=
      branchMap sharp v x := by
  have he:∑a:ScalarIndex,inner ℝ v (scalarBasis a) • scalarBasis a=v := by
    simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm] using scalarBasis.sum_repr v
  conv_rhs => rw [←he,map_sum,sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul,map_smul]
  rfl

/-- Exact source completion occurs before estimating; no duplicate full-vacuum
triangle term is introduced. -/
theorem actual_half_vacuum_split (sharp:Bool) :
    fullAction sharp=(1/2:ℂ) • constantAction sharp vacuum+shiftedY sharp := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hv:fullAction sharp f z=branchMap sharp (scalarField z) (f z) := by cases sharp <;> rfl
  rw [hv]
  simp only [shiftedY,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,add_apply,smul_apply,sum_apply,
    Module.End.mul_apply]
  change branchMap sharp (scalarField z) (f z)=
    (1/2:ℂ) • branchMap sharp vacuum (f z)+
      ∑a:ScalarIndex,branchMap sharp (scalarBasis a) ((shiftedCoordinate a z:ℂ) • f z)
  rw [show (∑a:ScalarIndex,branchMap sharp (scalarBasis a) ((shiftedCoordinate a z:ℂ) • f z))=
    branchMap sharp (scalarField z-(1/2:ℝ) • vacuum) (f z) from source_columns sharp _ _]
  have he:scalarField z=(1/2:ℝ) • vacuum+(scalarField z-(1/2:ℝ) • vacuum) := by module
  conv_lhs => rw [he,map_add,add_apply,map_smul,smul_apply]
  congr 1
  apply PiLp.ext
  intro word
  norm_num [PiLp.smul_apply,Complex.real_smul]

private theorem finite_column_price {ι:Type*}[Fintype ι]
    (A:ι → H →L[ℂ] H)(x:ι → H) :
    ‖∑i,A i (x i)‖^2 ≤ (∑i,‖A i‖^2)*(∑i,‖x i‖^2) := by
  have h:‖∑i,A i (x i)‖ ≤ ∑i,‖A i‖*‖x i‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>(A i).le_opNorm (x i)))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i=>‖A i‖) (fun i=>‖x i‖))

theorem actual_shifted_Y_price (sharp:Bool)(f:QuantumTest) :
    ‖embed (shiftedY sharp f)‖^2 ≤ coefficientCost sharp*shiftedMoment f := by
  have he:embed (shiftedY sharp f)=
      ∑a:ScalarIndex,constantBounded sharp (scalarBasis a) (embed (shiftedColumn a f)) := by
    simp only [shiftedY,LinearMap.sum_apply,Module.End.mul_apply,map_sum,constant_bounded_core]
  rw [he]
  exact finite_column_price _ _

private theorem source_lapse_positive : 0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

/-- A source-generated positive square feeds the actual mixed pressure with the
literal half-vacuum constant, for both independently generated Y branches. -/
theorem actual_full_Y_pressure_price (sharp:Bool)(f:QuantumTest) :
    ‖embed (fullAction sharp f)‖^2 ≤
      (coefficientCost sharp/sourceTime 0)*pressure f+
      (1/2:ℝ)*‖constantBounded sharp vacuum‖^2*‖embed f‖^2 := by
  have hc:0 ≤ coefficientCost sharp := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hshift:=actual_shifted_Y_price sharp f
  have hpressure:=original_second_pressure_payment f
  have hscalar:0 ≤ SourceClockReflectedForm.scalarForm
      (SourcePhysicalKineticSquare.inverseVolumeAction f) := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hfield:2*sourceTime 0*shiftedMoment f ≤ pressure f := by
    nlinarith only [hpressure,mul_nonneg source_lapse_positive.le hscalar]
  have hmul:=mul_le_mul_of_nonneg_left hfield (div_nonneg hc source_lapse_positive.le)
  have hv:=pow_le_pow_left₀ (norm_nonneg _) ((constantBounded sharp vacuum).le_opNorm (embed f)) 2
  rw [mul_pow,constant_bounded_core] at hv
  have ha:‖embed ((1/2:ℂ) • constantAction sharp vacuum f)‖^2 ≤
      (1/4:ℝ)*‖constantBounded sharp vacuum‖^2*‖embed f‖^2 := by
    simp only [map_smul,norm_smul,mul_pow]
    norm_num
    nlinarith only [hv]
  have hb:=pow_le_pow_left₀ (norm_nonneg _)
    (norm_add_le (embed ((1/2:ℂ) • constantAction sharp vacuum f)) (embed (shiftedY sharp f))) 2
  have hs:=sq_nonneg (‖embed ((1/2:ℂ) • constantAction sharp vacuum f)‖-‖embed (shiftedY sharp f)‖)
  rw [actual_half_vacuum_split,LinearMap.add_apply,LinearMap.smul_apply,map_add]
  have he:(coefficientCost sharp/sourceTime 0)*(2*sourceTime 0*shiftedMoment f)=
    2*coefficientCost sharp*shiftedMoment f := by field_simp [source_lapse_positive.ne']
  rw [he] at hmul
  nlinarith only [ha,hshift,hmul,hb,hs]

/-- The actual first two-resolvent word consumes this precise source positive block.
The pressure itself is not supplied as a budget or assumed to have a tail. -/
theorem actual_two_resolvent_pressure_price (advanced sharp:Bool)(m ell:ℕ)(F:Index)
    (μ:ℝ)(hμ:0 < μ)(g:diagonal.domain)(w:ℝ) :
    let z:=causalFrequency advanced μ w
    let q:=state F z (ActualVectorBulkSourcePrice.causal_nonreal advanced μ hμ w) g
    ‖finiteResolvent F z (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g:H)))‖^2 ≤
      μ⁻¹^2*((coefficientCost sharp/sourceTime 0)*pressure (SourceNativeCutoffContact.thetaAction m ell q)+
        (1/2:ℝ)*‖constantBounded sharp vacuum‖^2*‖embed (SourceNativeCutoffContact.thetaAction m ell q)‖^2) := by
  dsimp only
  have hs:embed (state F (causalFrequency advanced μ w)
      (ActualVectorBulkSourcePrice.causal_nonreal advanced μ hμ w) g)=
      finiteResolvent F (causalFrequency advanced μ w) (g:H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have h:=actual_full_Y_pressure_price sharp (SourceNativeCutoffContact.thetaAction m ell
    (state F (causalFrequency advanced μ w) (ActualVectorBulkSourcePrice.causal_nonreal advanced μ hμ w) g))
  have hi:SourceEscapeSeedTail.actualIncrement sharp m ell
      (finiteResolvent F (causalFrequency advanced μ w) (g:H))=
      embed (fullAction sharp (SourceNativeCutoffContact.thetaAction m ell
        (state F (causalFrequency advanced μ w) (ActualVectorBulkSourcePrice.causal_nonreal advanced μ hμ w) g))) := by
    rw [←hs,SourceCutoffDilationWard.literal_increment_core,(paid_positive_bulk% increment_full)]
  have hb:=(paid_positive_bulk% outer_bound) advanced F μ hμ w
    (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F (causalFrequency advanced μ w) (g:H)))
  rw [hi] at hb ⊢
  exact hb.trans (mul_le_mul_of_nonneg_left h (sq_nonneg _))

end LowEnergy.ActualMixedWardPositivePrice
