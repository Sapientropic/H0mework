import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.WorkResidual

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredEnergyAbsorption
open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

private theorem scalar_young (a b delta : ℝ) (positive : 0<delta) :
    a*b≤delta*b^2+a^2/(4*delta) := by
  have identity : delta*b^2+a^2/(4*delta)-a*b=(2*delta*b-a)^2/(4*delta) := by
    field_simp [positive.ne']
    ring
  have square : 0≤(2*delta*b-a)^2/(4*delta) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith only [identity,square]

private theorem word_pair (nu : Viscosity) (M : ℕ) (v : wholePhysical)
    (epsilon : ℝ) (positive : 0<epsilon) :
    inner ℝ v (NativeWindowHistoryAllOrderPrincipal.weight nu M v)≤
      epsilon*‖laplacianFiber nu M v‖^2+
        (1+nu.coeff^2/(4*epsilon))*‖v‖^2 := by
  have pair:=real_inner_le_norm v (laplacianFiber nu M v)
  have scaled:=mul_le_mul_of_nonneg_left pair nu.coeff_pos.le
  have young:=scalar_young (nu.coeff*‖v‖) ‖laplacianFiber nu M v‖ epsilon positive
  have normalized : (nu.coeff*‖v‖)^2/(4*epsilon)=
      (nu.coeff^2/(4*epsilon))*‖v‖^2 := by ring
  rw [normalized] at young
  simp only [NativeWindowHistoryAllOrderPrincipal.weight,add_apply,
    ContinuousLinearMap.id_apply,smul_apply,
    inner_add_right,real_inner_self_eq_norm_sq]
  have scalar : inner ℝ v (nu.coeff • laplacianFiber nu M v)=
      nu.coeff*inner ℝ v (laplacianFiber nu M v) :=
    real_inner_smul_right v (laplacianFiber nu M v) nu.coeff
  rw [scalar]
  nlinarith only [scaled,young]

theorem source_energy_relative_dissipation (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →
      NativeWindowHistoryAllOrderSpatial.energy seed M 1 time≤
        epsilon*NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time+C := by
  obtain ⟨B,B0,mass⟩:=NativeCenteredWordMass.source_word_one_energy_bound seed horizon
  let K:=1+nu.coeff^2/(4*epsilon)
  have K0 : 0≤K:=by dsimp only [K]; positivity
  refine ⟨K*B,mul_nonneg K0 B0,fun M time inside => ?_⟩
  have each:=Finset.sum_le_sum (s := (Finset.univ : Finset (FixedMatterSpatialWordIndex 1)))
    (fun word _ => word_pair nu M (NativeWindowHistoryAllOrderWord.value seed M word.toList time)
      epsilon positive)
  have paid : NativeWindowHistoryAllOrderSpatial.energy seed M 1 time≤
      epsilon*NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time+
        K*NativeWindowHistoryAllOrderWord.energy seed M 1 time := by
    simpa only [NativeWindowHistoryAllOrderSpatial.energy,
      NativeWindowHistoryAllOrderSpatial.dissipation,NativeWindowHistoryAllOrderWord.energy,
      Finset.sum_add_distrib,← Finset.mul_sum,K] using each
  have payment:=mul_le_mul_of_nonneg_left (mass M time inside) K0
  change NativeWindowHistoryAllOrderSpatial.energy seed M 1 time≤
    epsilon*NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time+K*B
  linarith only [paid,payment]

theorem source_quartic_dissipation_gate (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) :
    ∃low : ℕ,∃r C : ℝ,0<r ∧0≤C ∧∀M≥low,∀time∈Icc 0 horizon,
      let l:=laplacianFiber nu M
        (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M))
      (nu.coeff^2/32)*‖l‖^4+
        nu.coeff^2*NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time+
          r*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time≤
            r*NativeWindowHistoryAllOrderSpatial.work seed M 1 time+C := by
  obtain ⟨low,q,C0,q0,C00,gate⟩:=NativeCenteredWorkGate.source_original_work_gate_paid seed horizon
  obtain ⟨A,A0,source⟩:=NativeWindowHistoryAllOrderSpatial.source_generator seed horizon
  obtain ⟨B,B0,mass⟩:=NativeCenteredWordMass.source_word_one_energy_bound seed horizon
  let r:=q+1
  let C:=C0+A*B
  have r0 : 0<r:=by dsimp only [r]; linarith only [q0]
  have C0' : 0≤C:=add_nonneg C00 (mul_nonneg A0 B0)
  refine ⟨low,r,C,r0,C0',fun M above time inside => ?_⟩
  have first:=gate M above time inside
  dsimp only at first
  have second:=source M 1 time inside
  have third:=mul_le_mul_of_nonneg_left (mass M time inside) A0
  dsimp only [r,C]
  nlinarith only [first,second,third]

end
end SaturationMonoid.NavierStokes.NativeCenteredEnergyAbsorption
