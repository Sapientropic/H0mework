import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.TensorSpatial
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.WeakPairing
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatialTransport
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatial

set_option autoImplicit false
open scoped Topology BigOperators ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeResponseConvectionTensor
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowHistoryCreationGeometry (square transport product_fourier)
open NativeWindowStressOseenTest (evaluate)
open NativeWindowStressHeatSource (physical)
open NativeWindowFiniteGramFourier (fourierRead)
open NativeWindowAugmentedGradient (derivative)
open NativeWindowOperatorGreen (laplacian laplacian_pairing)
open NativeWindowHistoryJacobianSpatial (finite_skew finite_square finite_commute)
open NativeResponseTensorPayment (pairTensor)
open NativeWindowHistorySpatialTransport (finite)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private theorem gradient_pair (M : ℕ) (u v : physicalSpace (modes M)) :
    (∑ j : Coordinate,pairing (modes M) (finite M j u) (finite M j v))=
      pairing (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu u) v := by
  have each (j : Coordinate) : pairing (modes M) (finite M j u) (finite M j v)=
      -pairing (modes M) (finite M j (finite M j u)) v := by
    have skew := finite_skew M j (finite M j u) v
    change pairing (modes M) (finite M j (finite M j u)) v=
      -pairing (modes M) (finite M j u) (finite M j v) at skew
    linarith only [skew]
  have summed := congrArg (fun x => pairing (modes M) x v) (finite_square nu M u)
  simp only [map_sum,LinearMap.sum_apply,map_neg,LinearMap.neg_apply] at summed
  simp only [each,Finset.sum_neg_distrib]
  change -(∑ j : Coordinate,pairing (modes M)
    (derivative (modes M) (modes_zero M) (modes_closed M) j
      (derivative (modes M) (modes_zero M) (modes_closed M) j u)) v)=_
  rw [summed,neg_neg]

theorem convection_commutator (M : ℕ) (u z : physicalSpace (modes M)) :
    pairing (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)
      (transport (modes M) (modes_zero M) (modes_closed M) nu u z)=
      -∑ j : Coordinate,pairing (modes M) z
        (transport (modes M) (modes_zero M) (modes_closed M) nu (finite M j u) (finite M j z)) := by
  rw [← gradient_pair,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have leibniz := NativeWindowHistorySpatialTransport.transport_derivative
    (modes M) (modes_zero M) (modes_closed M) nu u z j
  change finite M j (transport _ _ _ nu u z)=
    transport _ _ _ nu (finite M j u) z+transport _ _ _ nu u (finite M j z) at leibniz
  rw [leibniz,map_add]
  have zero := NativeWindowHistoryJacobianForm.transport_skew nu M u (finite M j z) (finite M j z)
  have skew := NativeWindowHistoryJacobianForm.transport_skew nu M (finite M j u) (finite M j z) z
  linarith only [zero,skew]

theorem second_gradient_square (M : ℕ) (z : physicalSpace (modes M)) :
    (∑ j : Coordinate,NativeCommonAdvectorAction.curlPair (modes M) (finite M j z).1 (finite M j z).1)=
      ‖coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)‖^2 := by
  have each (j : Coordinate) : NativeCommonAdvectorAction.curlPair (modes M) (finite M j z).1 (finite M j z).1=
      pairing (modes M) (finite M j z)
        (finite M j (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)) := by
    rw [← laplacian_pairing (modes M) (modes_zero M) (modes_closed M) nu (finite M j z) (finite M j z)]
    exact congrArg (pairing (modes M) (finite M j z)) (finite_commute nu M j z).symm
  rw [show (fun j => NativeCommonAdvectorAction.curlPair (modes M) (finite M j z).1 (finite M j z).1)=
    (fun j => pairing (modes M) (finite M j z)
      (finite M j (laplacian (modes M) (modes_zero M) (modes_closed M) nu z))) from funext each,
    gradient_pair (nu := nu)]
  exact real_inner_self_eq_norm_sq
    (coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu z))

private theorem transport_product_bound (M : ℕ) (u v w : physicalSpace (modes M))
    (eta : ℝ) (positive : 0 < eta) :
    |2*nu.coeff*pairing (modes M) v (transport (modes M) (modes_zero M) (modes_closed M) nu u w)| ≤
      eta*NativeCommonAdvectorAction.curlPair (modes M) w.1 w.1+
        (nu.coeff^2/eta)*(∫ point : NativePhysicalFourier.Torus,square (modes M) u point*square (modes M) v point) := by
  let P := pairing (modes M) v (transport (modes M) (modes_zero M) (modes_closed M) nu u w)
  let S := ∫ point : NativePhysicalFourier.Torus,square (modes M) u point*square (modes M) v point
  let G := NativeCommonAdvectorAction.curlPair (modes M) w.1 w.1
  have bound (c : ℝ) : 2*c*P ≤ c^2*S+G :=
    NativeWindowHistorySchurWeakPairing.transport_young
      (modes M) (modes_zero M) (modes_closed M) nu u v w c
  have upper := mul_le_mul_of_nonneg_left (bound (nu.coeff/eta)) positive.le
  have lower := mul_le_mul_of_nonneg_left (bound (-nu.coeff/eta)) positive.le
  have first : eta*(2*(nu.coeff/eta)*P)=2*nu.coeff*P := by field_simp [positive.ne']
  have last : eta*(2*(-nu.coeff/eta)*P)= -(2*nu.coeff*P) := by field_simp [positive.ne']
  have right : eta*((nu.coeff/eta)^2*S+G)=eta*G+(nu.coeff^2/eta)*S := by field_simp [positive.ne']; ring
  have rightNeg : eta*((-nu.coeff/eta)^2*S+G)=eta*G+(nu.coeff^2/eta)*S := by field_simp [positive.ne']; ring
  rw [first,right] at upper
  rw [last,rightNeg] at lower
  exact abs_le.mpr ⟨by linarith only [lower],upper⟩

theorem convection_tensor_paid (nu : Viscosity) (eta : ℝ) (positive : 0 < eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M, ∀ u z : physicalSpace (modes M),
      |2*nu.coeff*pairing (modes M)
        (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)
        (transport (modes M) (modes_zero M) (modes_closed M) nu u z)| ≤
        eta*‖coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)‖^2+
          C*(∑ j : Coordinate,‖pairTensor M (finite M j u) z‖^2) := by
  refine ⟨9*nu.coeff^2/eta,by positivity,fun M u z => ?_⟩
  have each (j : Coordinate) :
      |2*nu.coeff*pairing (modes M) z
        (transport (modes M) (modes_zero M) (modes_closed M) nu (finite M j u) (finite M j z))| ≤
        eta*NativeCommonAdvectorAction.curlPair (modes M) (finite M j z).1 (finite M j z).1+
          (9*nu.coeff^2/eta)*‖pairTensor M (finite M j u) z‖^2 := by
    have raw := transport_product_bound (nu := nu) M (finite M j u) z (finite M j z) eta positive
    have tensor := mul_le_mul_of_nonneg_left
      (NativeResponseTensorPayment.physical_mixed_square_bound M (finite M j u) z)
      (show 0 ≤ nu.coeff^2/eta by positivity)
    exact (raw.trans (add_le_add le_rfl tensor)).trans_eq (by ring)
  have summed := (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j : Coordinate =>
    2*nu.coeff*pairing (modes M) z
      (transport (modes M) (modes_zero M) (modes_closed M) nu (finite M j u) (finite M j z)))).trans
      (Finset.sum_le_sum fun j _ => each j)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,second_gradient_square (nu := nu)] at summed
  rw [convection_commutator (nu := nu),mul_neg,abs_neg]
  exact summed

theorem convection_heat_paid (nu : Viscosity) (eta : ℝ) (positive : 0 < eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M, ∀ u z : physicalSpace (modes M),
      let L := laplacian (modes M) (modes_zero M) (modes_closed M) nu
      |2*nu.coeff*pairing (modes M) (L z)
        (transport (modes M) (modes_zero M) (modes_closed M) nu u z)|+
        (C/(2*nu.coeff))*(2*inner ℝ (pairTensor M u z)
          (pairTensor M ((-nu.coeff) • L u) z+pairTensor M u (nu.coeff • L z))) ≤
        eta*‖coefficients (modes M) (L z)‖^2+
          C*(∑ j : Coordinate,‖pairTensor M u (finite M j z)‖^2) := by
  obtain ⟨C,C0,paid⟩ := convection_tensor_paid nu eta positive
  refine ⟨C,C0,fun M u z => ?_⟩
  have heat := NativeResponseTensorPayment.opposite_diffusion_square (nu := nu) M u z
  change 2*inner ℝ (pairTensor M u z)
    (pairTensor M ((-nu.coeff) • laplacian (modes M) (modes_zero M) (modes_closed M) nu u) z+
      pairTensor M u (nu.coeff • laplacian (modes M) (modes_zero M) (modes_closed M) nu z)) =
    2*nu.coeff*((∑ j : Coordinate,‖pairTensor M u (finite M j z)‖^2)-
      ∑ j : Coordinate,‖pairTensor M (finite M j u) z‖^2) at heat
  dsimp only
  rw [heat]
  have cancel : C/(2*nu.coeff)*(2*nu.coeff)=C :=
    div_mul_cancel₀ _ (by positivity [nu.coeff_pos])
  rw [← mul_assoc,cancel]
  nlinarith only [paid M u z]

end
end SaturationMonoid.NavierStokes.NativeResponseConvectionTensor
