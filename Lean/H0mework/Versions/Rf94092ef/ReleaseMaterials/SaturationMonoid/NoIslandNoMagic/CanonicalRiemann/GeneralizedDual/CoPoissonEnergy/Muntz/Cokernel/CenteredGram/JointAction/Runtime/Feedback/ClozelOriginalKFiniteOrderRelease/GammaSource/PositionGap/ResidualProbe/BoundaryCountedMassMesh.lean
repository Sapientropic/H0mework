import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.UnitMesh
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedError
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedMassMesh

open BurnolPhysicalState MeasureTheory Set
open scoped BigOperators

open private BoundaryCountedInverse.normalized mass
  from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedInverse
open private trajectory normalized_read trajectory_continuous
  from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedGenerator
open private mass_source realGap gap_lower tailStart index_pos damping compensation
  from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedContinuousInverse
open private flow flow_trajectory flow_lipschitz speed speed_nonneg amplitude amplitude_pos resolvent_bound
  from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedError

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "U" => burnolMultiplicativeDilation
local notation "R" => burnolDirectRightResolventCLM
local notation "I" => BoundaryCountedContinuousInverse.index

private def radialStep (N : Nat) : ℝ := Real.sqrt (1+(N : ℝ)⁻¹)-1

private theorem step_nonneg (N : Nat) : 0 ≤ radialStep N := by
  unfold radialStep
  apply sub_nonneg.mpr
  have base : (1 : ℝ) ≤ 1+(N : ℝ)⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt base

private theorem radial_square (N : Nat) : (1+radialStep N)^2 = 1+(N : ℝ)⁻¹ := by
  unfold radialStep
  rw [show 1+(Real.sqrt (1+(N : ℝ)⁻¹)-1) = Real.sqrt (1+(N : ℝ)⁻¹) by ring]
  exact Real.sq_sqrt (by positivity)

private theorem radial_bound (N : Nat) : 2*radialStep N ≤ (N : ℝ)⁻¹ := by
  nlinarith only [radial_square N, sq_nonneg (radialStep N)]

private def scaleMass (N : Nat) : ℝ := 2*(N : ℝ)*radialStep N

private theorem scaleMass_nonneg (N : Nat) : 0 ≤ scaleMass N := by
  exact mul_nonneg (by positivity) (step_nonneg N)

private theorem scaleMass_le (N : Nat) (positive : 0 < N) : scaleMass N ≤ 1 := by
  have nPos : (0 : ℝ) < N := by exact_mod_cast positive
  calc
    scaleMass N = (N : ℝ)*(2*radialStep N) := by unfold scaleMass; ring
    _ ≤ (N : ℝ)*(N : ℝ)⁻¹ := mul_le_mul_of_nonneg_left (radial_bound N) nPos.le
    _ = 1 := mul_inv_cancel₀ nPos.ne'

private theorem scaleMass_source (N : Nat) (positive : 0 < N) :
    scaleMass N = Real.sqrt (N : ℝ) * mass N := by
  have nPos : (0 : ℝ) < N := by exact_mod_cast positive
  have edge : Real.sqrt (N : ℝ) * Real.sqrt (1+(N : ℝ)⁻¹) = Real.sqrt ((N : ℝ)+1) := by
    rw [← Real.sqrt_mul nPos.le, mul_add, mul_one, mul_inv_cancel₀ nPos.ne']
  rw [mass_source N positive, ← edge]
  calc
    scaleMass N = 2*(Real.sqrt (N : ℝ))^2*radialStep N := by rw [Real.sq_sqrt nPos.le]; rfl
    _ = _ := by unfold radialStep; ring

private def phase (N : Nat) (u : ℝ) : ℝ := 2 * Real.log (1+radialStep N*u)

private def orbit (N : Nat) (u : ℝ) (value : BurnolL2) : BurnolL2 :=
  U (-phase N u) value

private theorem orbit_continuous (N : Nat) (value : BurnolL2) :
    ContinuousOn (fun u => orbit N u value) (Icc 0 1) := by
  have h : Continuous (fun u : ℝ => 1+radialStep N*u) := continuous_const.add (continuous_const.mul continuous_id)
  have log : ContinuousOn (fun u : ℝ => Real.log (1+radialStep N*u)) (Icc 0 1) :=
    Real.continuousOn_log.comp h.continuousOn (fun u hu => by
      exact (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (step_nonneg N) hu.1)).ne')
  exact (burnolMultiplicativeDilation_stronglyContinuous value).comp_continuousOn (log.const_mul 2).neg

/-- Equal steps in the original square-root mass coordinate consume the full counted compensation. -/
theorem mass_read (N : Nat) (positive : 0 < N) (value : BurnolL2) :
    BoundaryCountedInverse.normalized N positive value =
      scaleMass N • ∫ u : ℝ in (0 : ℝ)..1, orbit N u value := by
  let a := radialStep N
  let root (u : ℝ) := 1+a*u
  let warp (u : ℝ) := (N : ℝ)*(root u^2-1)
  let slope (u : ℝ) := (N : ℝ)*(2*root u*a)
  have nPos : (0 : ℝ) < N := by exact_mod_cast positive
  have nLarge : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have aNonneg : 0 ≤ a := step_nonneg N
  have rootPos (u : ℝ) (nonneg : 0 ≤ u) : 0 < root u :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg aNonneg nonneg)
  have start : warp 0 = 0 := by simp [warp, root]
  have stop : warp 1 = 1 := by
    have square : root 1 ^ 2 = 1+(N : ℝ)⁻¹ := by simpa only [root, mul_one] using radial_square N
    change (N : ℝ)*(root 1^2-1) = 1
    rw [square, add_sub_cancel_left, mul_inv_cancel₀ nPos.ne']
  have ordered : MonotoneOn warp (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    have first : root u ≤ root v := add_le_add le_rfl (mul_le_mul_of_nonneg_left huv aNonneg)
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (pow_le_pow_left₀ (rootPos u hu.1).le first 2) _) nPos.le
  have mapped : MapsTo warp (Icc (0 : ℝ) 1) (Icc 0 1) := by
    intro u hu
    exact ⟨start ▸ ordered (left_mem_Icc.mpr zero_le_one) hu hu.1,
      stop ▸ ordered hu (right_mem_Icc.mpr zero_le_one) hu.2⟩
  have derivative (u : ℝ) : HasDerivAt warp (slope u) u := by
    have linear : HasDerivAt root a u := by
      simpa only [root, id_eq, mul_one] using (((hasDerivAt_id u).const_mul a).const_add 1)
    simpa only [warp, slope, Nat.cast_ofNat, show (2 : Nat)-1=1 by decide, pow_one] using
      (((linear.fun_pow 2).sub_const 1).const_mul (N : ℝ))
  have derivativeCont : Continuous slope := by dsimp only [slope, root]; fun_prop
  have path : ContinuousOn (fun t : ℝ => trajectory value (t/N)) (Icc 0 1) :=
    (trajectory_continuous value).comp (continuous_id.div_const _).continuousOn (fun t inside =>
      ⟨div_nonneg inside.1 nPos.le, (div_le_one nPos).mpr (inside.2.trans nLarge)⟩)
  have image : warp '' uIcc (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIcc_of_le zero_le_one]
    exact mapped.image_subset
  have substitute := intervalIntegral.integral_deriv_smul_comp'
    (fun u (_ : u ∈ uIcc (0 : ℝ) 1) => derivative u) derivativeCont.continuousOn (path.mono image)
  rw [start, stop] at substitute
  rw [normalized_read N positive value, ← substitute, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro u member
  rw [uIcc_of_le zero_le_one] at member
  have rootPositive := rootPos u member.1
  have ratio : 1+warp u/(N : ℝ) = (root u)^2 := by
    dsimp only [warp]
    rw [mul_div_cancel_left₀ _ nPos.ne']
    ring
  have time : Real.log (1+warp u/(N : ℝ)) = phase N u := by
    rw [ratio, Real.log_pow, phase]
    rfl
  have exponent : Real.exp (-phase N u/2) = (root u)⁻¹ := by
    change Real.exp (-(2*Real.log (root u))/2) = _
    rw [show -(2*Real.log (root u))/2 = -Real.log (root u) by ring, Real.exp_neg, Real.exp_log rootPositive]
  change slope u • trajectory value (warp u / N) = _
  rw [flow_trajectory _ (div_nonneg (mapped member).1 nPos.le), time]
  change slope u • ((Real.exp (-phase N u/2) : ℂ) • orbit N u value) = scaleMass N • orbit N u value
  rw [exponent]
  change slope u • ((root u)⁻¹ • orbit N u value) = _
  rw [smul_smul]
  have exactWeight : slope u * (root u)⁻¹ = scaleMass N := by
    change (N : ℝ)*(2*root u*a)*(root u)⁻¹ = 2*(N : ℝ)*a
    field_simp [rootPositive.ne']
  rw [exactWeight]

private def transportSpeed (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  speed coordinate + amplitude coordinate/2

private theorem transportSpeed_nonneg (coordinate : BurnolCompletedMellinCoordinate) :
    0 ≤ transportSpeed coordinate :=
  add_nonneg (speed_nonneg coordinate) (div_nonneg (amplitude_pos coordinate).le (by norm_num))

private theorem dilation_step (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (h : ℝ) (nonneg : 0 ≤ h) :
    ‖U (-h) (R coordinate value)-R coordinate value‖ ≤ h * (transportSpeed coordinate * ‖value‖) := by
  let x := R coordinate value
  let y := U (-h) x
  have loss : 0 ≤ 1-Real.exp (-h/2) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have lossBound : 1-Real.exp (-h/2) ≤ h/2 := by linarith only [Real.add_one_le_exp (-h/2)]
  have diff : y-flow h x = ((1-Real.exp (-h/2) : ℝ) : ℂ) • y := by
    change y-(Real.exp (-h/2) : ℂ) • y = _
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  have bound : ‖y-flow h x‖ ≤ h/2 * (amplitude coordinate * ‖value‖) := by
    rw [diff, norm_smul, Complex.norm_real, Real.norm_of_nonneg loss]
    change (1-Real.exp (-h/2)) * ‖U (-h) x‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul lossBound (resolvent_bound coordinate value) (norm_nonneg x) (by positivity)
  calc
    ‖y-x‖ = ‖(y-flow h x)+(flow h x-x)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖y-flow h x‖ + ‖flow h x-x‖ := norm_add_le _ _
    _ ≤ h/2*(amplitude coordinate*‖value‖) + h*(speed coordinate*‖value‖) :=
      add_le_add bound (flow_lipschitz coordinate value h nonneg)
    _ = _ := by unfold transportSpeed; ring

private theorem phase_gap (N : Nat) (positive : 0 < N) (u v : ℝ)
    (nonneg : 0 ≤ u) (ordered : u ≤ v) :
    0 ≤ phase N v-phase N u ∧ phase N v-phase N u ≤ (v-u)/(N : ℝ) := by
  let a := radialStep N
  let x := 1+a*u
  let y := 1+a*v
  have nPos : (0 : ℝ) < N := by exact_mod_cast positive
  have aNonneg : 0 ≤ a := step_nonneg N
  have xGe : 1 ≤ x := le_add_of_nonneg_right (mul_nonneg aNonneg nonneg)
  have xy : x ≤ y := add_le_add le_rfl (mul_le_mul_of_nonneg_left ordered aNonneg)
  have xPos : 0 < x := zero_lt_one.trans_le xGe
  have yPos : 0 < y := xPos.trans_le xy
  have ratio : 0 < y/x := div_pos yPos xPos
  have logNonneg := Real.log_nonneg ((le_div_iff₀ xPos).mpr (by simpa only [one_mul] using xy))
  have lose : y/x-1 = a*(v-u)/x := by dsimp only [x,y]; field_simp [xPos.ne']; ring
  have small : a*(v-u)/x ≤ a*(v-u) := by
    apply (div_le_iff₀ xPos).mpr
    exact le_mul_of_one_le_right (mul_nonneg aNonneg (sub_nonneg.mpr ordered)) xGe
  have relation : 2*Real.log y-2*Real.log x = 2*Real.log (y/x) := by rw [Real.log_div yPos.ne' xPos.ne']; ring
  change 0 ≤ 2*Real.log y-2*Real.log x ∧ 2*Real.log y-2*Real.log x ≤ _
  rw [relation]
  refine ⟨mul_nonneg (by norm_num) logNonneg, ?_⟩
  calc
    _ ≤ 2*(y/x-1) := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ratio) (by norm_num)
    _ ≤ 2*(a*(v-u)) := by rw [lose]; exact mul_le_mul_of_nonneg_left small (by norm_num)
    _ = 2*a*(v-u) := by ring
    _ ≤ (N : ℝ)⁻¹ * (v-u) := mul_le_mul_of_nonneg_right (radial_bound N) (sub_nonneg.mpr ordered)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

private theorem orbit_lipschitz (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (N : Nat) (positive : 0 < N) (u v : ℝ) (nonneg : 0 ≤ u) (ordered : u ≤ v) :
    ‖orbit N u (R coordinate value)-orbit N v (R coordinate value)‖ ≤
      (transportSpeed coordinate * ‖value‖ / (N : ℝ)) * (v-u) := by
  let x := R coordinate value
  let h := phase N v-phase N u
  have clock := phase_gap N positive u v nonneg ordered
  have paid : orbit N u x - orbit N v x = U (-phase N u) (x-U (-h) x) := by
    rw [orbit, orbit, map_sub, burnolMultiplicativeDilation_add]
    congr 2
    dsimp only [h]
    ring
  change ‖orbit N u x-orbit N v x‖ ≤ _
  rw [paid, LinearIsometryEquiv.norm_map, norm_sub_rev]
  calc
    _ ≤ h*(transportSpeed coordinate*‖value‖) := dilation_step coordinate value h clock.1
    _ ≤ ((v-u)/(N : ℝ))*(transportSpeed coordinate*‖value‖) :=
      mul_le_mul_of_nonneg_right clock.2 (mul_nonneg (transportSpeed_nonneg coordinate) (norm_nonneg _))
    _ = _ := by ring

/-- Finite original dilation word with exactly the original total compensation weight. -/
def meshTail (N mesh : Nat) : End :=
  (N : ℝ) • scaleMass N • SourceGeneratedUnitMesh.average mesh
    (fun u => (U (-phase N u)).toContinuousLinearEquiv.toContinuousLinearMap)

private theorem meshTail_apply (N mesh : Nat) (value : BurnolL2) :
    meshTail N mesh value = (N : ℝ) • scaleMass N •
      SourceGeneratedUnitMesh.average mesh (fun u => orbit N u value) := by
  unfold meshTail SourceGeneratedUnitMesh.average orbit
  simp only [smul_apply, sum_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]

private theorem meshTail_norm (N mesh : Nat) (meshPos : 0 < mesh) :
    ‖meshTail N mesh‖ ≤ (N : ℝ)*scaleMass N := by
  apply (meshTail N mesh).opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) (scaleMass_nonneg N))
  intro value
  rw [meshTail_apply, norm_smul, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (scaleMass_nonneg N), ← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (scaleMass_nonneg N))
  apply SourceGeneratedUnitMesh.average_bound mesh meshPos
  intro j _
  exact (LinearIsometryEquiv.norm_map _ _).le

theorem mesh_margin (coordinate : ℂ) (right : 1/4 < coordinate.re) (n mesh : Nat) (meshPos : 0 < mesh) :
    ‖meshTail (I coordinate n) mesh‖ + (coordinate.re-1/4)/2 ≤ (damping coordinate (I coordinate n)).re := by
  let N := I coordinate n
  have positive : 0 < N := index_pos coordinate n
  have nPos : (0 : ℝ) < N := by exact_mod_cast positive
  have price : 0 < 4*(coordinate.re-1/4) := by linarith
  have afterStart : tailStart coordinate < N := by dsimp only [N, BoundaryCountedContinuousInverse.index]; omega
  have first : (4*(coordinate.re-1/4))⁻¹ ≤ (tailStart coordinate : ℝ) := Nat.le_ceil _
  have after : (4*(coordinate.re-1/4))⁻¹ < (N : ℝ) := first.trans_lt (by exact_mod_cast afterStart)
  have short : (N : ℝ)⁻¹ < 4*(coordinate.re-1/4) := by
    have bound := (inv_lt_inv₀ nPos (inv_pos.mpr price)).mpr after
    rwa [inv_inv] at bound
  have gain := gap_lower N positive
  rw [realGap, ← scaleMass_source N positive] at gain
  have normBound := meshTail_norm N mesh meshPos
  change ‖meshTail N mesh‖ + (coordinate.re-1/4)/2 ≤ (damping coordinate N).re
  simp only [damping, Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.div_ofNat_re, Complex.one_re]
  linarith only [gain, short, normBound]

/-- The finite mesh consumes the original whole R-born orbit with explicit source error. -/
theorem mesh_error (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (N mesh : Nat) (positive : 0 < N) (meshPos : 0 < mesh) :
    ‖compensation N positive (R coordinate value) - meshTail N mesh (R coordinate value)‖ ≤
      transportSpeed coordinate * ‖value‖ / (mesh : ℝ) := by
  let x := R coordinate value
  let L := transportSpeed coordinate * ‖value‖
  have nPos : (0 : ℝ) < N := by exact_mod_cast positive
  have mPos : (0 : ℝ) < mesh := by exact_mod_cast meshPos
  have price : 0 ≤ L := mul_nonneg (transportSpeed_nonneg coordinate) (norm_nonneg value)
  have paid := SourceGeneratedUnitMesh.average_error mesh meshPos (fun u => orbit N u x)
    (orbit_continuous N x) (L/(N : ℝ)) (div_nonneg price nPos.le)
    (fun u v hu _ ordered => orbit_lipschitz coordinate value N positive u v hu.1 ordered)
  change ‖compensation N positive x-meshTail N mesh x‖ ≤ L/(mesh : ℝ)
  have action : compensation N positive x = (N : ℝ) •
      (scaleMass N • ∫ u : ℝ in (0 : ℝ)..1, orbit N u x) := by
    change (N : ℂ) • BoundaryCountedInverse.normalized N positive x = _
    rw [mass_read]
    rfl
  rw [action, meshTail_apply, ← smul_sub, ← smul_sub, norm_smul, norm_smul,
    Real.norm_of_nonneg nPos.le, Real.norm_of_nonneg (scaleMass_nonneg N)]
  calc
    _ ≤ (N : ℝ)*(scaleMass N*((L/(N : ℝ))/(mesh : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left paid (scaleMass_nonneg N)) nPos.le
    _ ≤ (N : ℝ)*(1*((L/(N : ℝ))/(mesh : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (scaleMass_le N positive)
        (div_nonneg (div_nonneg price nPos.le) mPos.le)) nPos.le
    _ = _ := by field_simp

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedMassMesh
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
