import H0mework.NavierStokes.StressResolvent.WholeResolventLimit

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeResolventIdentity

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeFiniteActionResolvent NativeWholeResolvent NativeWholeResolventLimit NativeSourceResolvent
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeEndpointVelocityCarrier

noncomputable section

theorem resolver_identity {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (action : V →ₗ[ℝ] V) (form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (faithful : ∀ value, form value value ≤ 0 → value = 0)
    (dissipative : ∀ value, form value (action value) ≤ 0)
    (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (x : V) :
    t • resolver action form faithful dissipative t ht x -
      s • resolver action form faithful dissipative s hs x =
    (t - s) • resolver action form faithful dissipative t ht
      (resolver action form faithful dissipative s hs x) := by
  apply implicitMap_injective action form faithful dissipative t ht
  simp only [map_sub, map_smul]
  change t • (_ - t • action _) - s • (_ - t • action _) = (t - s) • (_ - t • action _)
  simp only [LinearMap.id_apply]
  rw [resolver_write, resolver_write]
  calc
    _ = t • (resolver action form faithful dissipative s hs x -
        s • action (resolver action form faithful dissipative s hs x)) -
      s • (resolver action form faithful dissipative s hs x -
        t • action (resolver action form faithful dissipative s hs x)) := by rw [resolver_write]
    _ = _ := by module

theorem restrict_embedded (frequencies : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ frequencies)
    (closed : ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.FiniteModeNegClosed frequencies)
    (v : physicalSpace frequencies)
    (physical : puncturedEuclideanize v.1 ∈ wholePhysical) :
    restrictCLM frequencies zeroNotMem closed ⟨puncturedEuclideanize v.1, physical⟩ = v := by
  apply Subtype.ext
  change complexSharpSupportProjection frequencies (wholeVelocity (puncturedEuclideanize v.1)) = v.1
  rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize v.1
    (physical_supported v 0 zeroNotMem)]
  exact complexSharpSupportProjection_eq_self_of_supported frequencies v.1 (physical_supported v)

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem restrict_stage (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (node : TimeNode) (step : ℝ) (nonnegative : 0 ≤ step) (x : wholePhysical) :
    restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index)
      (physicalStage stress pointLe index node step nonnegative x) =
    physicalResolver (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
      (advector stress pointLe index node) (advector_reality stress pointLe index node) step nonnegative
      (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) x) :=
  restrict_embedded _ _ _ _ _

theorem physicalStage_identity (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (node : TimeNode) (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (x : wholePhysical) :
    t • physicalStage stress pointLe index node t ht x -
      s • physicalStage stress pointLe index node s hs x =
    (t - s) • physicalStage stress pointLe index node t ht
      (physicalStage stress pointLe index node s hs x) := by
  apply Subtype.ext
  change t • puncturedEuclideanize (physicalResolver _ _ _ _ _ _ t ht _).1 -
      s • puncturedEuclideanize (physicalResolver _ _ _ _ _ _ s hs _).1 =
    (t - s) • puncturedEuclideanize (physicalResolver _ _ _ _ _ _ t ht
      (restrictCLM _ _ _ (physicalStage stress pointLe index node s hs x))).1
  rw [restrict_stage]
  have finiteIdentity := resolver_identity
    (physicalOperator (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
      (advector stress pointLe index node) (advector_reality stress pointLe index node))
    (pairing (modes stress index)) (pairing_faithful (modes stress index))
    (physicalOperator_dissipative _ _ _ _ _ _) t s ht hs
    (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) x)
  exact congrArg (fun v : physicalSpace (modes stress index) => puncturedEuclideanize v.1) finiteIdentity

theorem operator_identity (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (x : wholePhysical) :
    t • operator stress pointLe node t ht x - s • operator stress pointLe node s hs x =
    (t - s) • operator stress pointLe node t ht (operator stress pointLe node s hs x) := by
  have first := (operator_tendsto stress pointLe node t ht x).const_smul t
  have last := (operator_tendsto stress pointLe node s hs x).const_smul s
  have composed := (moving_input stress pointLe node t ht
    (operator_tendsto stress pointLe node s hs x)).const_smul (t - s)
  apply tendsto_nhds_unique (first.sub last)
  exact composed.congr' (Eventually.of_forall fun index =>
    (physicalStage_identity stress pointLe index node t s ht.le hs.le x).symm)

theorem operator_identity_clm (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    t • operator stress pointLe node t ht - s • operator stress pointLe node s hs =
    (t - s) • (operator stress pointLe node t ht).comp (operator stress pointLe node s hs) := by
  apply ContinuousLinearMap.ext
  intro x
  exact operator_identity stress pointLe node t s ht hs x

theorem operator_commute (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    (operator stress pointLe node t ht).comp (operator stress pointLe node s hs) =
      (operator stress pointLe node s hs).comp (operator stress pointLe node t ht) := by
  by_cases same : t = s
  · subst s
    rfl
  apply ContinuousLinearMap.ext
  intro x
  apply smul_right_injective (M := wholePhysical) (sub_ne_zero.mpr same)
  change (t - s) • operator stress pointLe node t ht (operator stress pointLe node s hs x) =
    (t - s) • operator stress pointLe node s hs (operator stress pointLe node t ht x)
  calc
    _ = t • operator stress pointLe node t ht x - s • operator stress pointLe node s hs x :=
      (operator_identity stress pointLe node t s ht hs x).symm
    _ = -(s • operator stress pointLe node s hs x - t • operator stress pointLe node t ht x) := by module
    _ = -((s - t) • operator stress pointLe node s hs (operator stress pointLe node t ht x)) :=
      congrArg Neg.neg (operator_identity stress pointLe node s t hs ht x)
    _ = _ := by module

end
end SaturationMonoid.NavierStokes.NativeWholeResolventIdentity
