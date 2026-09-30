import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Hamiltonian
import H0mework.Physics.LowEnergy.FullQuantum.ScalarGreen.Grading

/-! The source exterior grading survives arbitrary spatial native gauge fields and their exact resolvents. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open StageNineCurrentCoframeMatterTemporalPrincipal DiracExteriorMatterAction Triangular
open StageNineHolonomicField StageNineP286GaugeConnectionVariation
open ScalarGreen
noncomputable section

theorem freeValue_six (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0<damping) :
    Commute (operator MixedSymbol.degreeSix) (freeValue point momentum energy damping) :=
  operator_commute _ _ (grade_freeResolvent 0 actual point momentum (Retarded.spectralParameter energy damping)
    (Retarded.sourceFree_regular point momentum energy damping positive))

theorem freeR_six (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) (field : FullMatterL2) :
    six (freeR point energy damping positive field)=freeR point energy damping positive (six field) := by
  apply fourier.injective
  rw [six_fourier]
  apply Lp.ext
  filter_upwards [six_ae (fourier (freeR point energy damping positive field)),
    freeR_fourier_ae point energy damping positive field,
    freeR_fourier_ae point energy damping positive (six field),six_ae (fourier field)]
    with frequency outer left right inner
  rw [outer,left,right,six_fourier,inner]
  exact congrArg (fun A : FiberOperators => A (fourier field frequency))
    (freeValue_six point (physicalMomentum frequency) energy damping positive).eq

theorem gaugeMap_six (gauge : P286GaugeOneForm) :
    Commute (operator MixedSymbol.degreeSix) (gaugeMap gauge) := by
  have spatial : Commute (grade 0) (YangMills.Response.Forcing.spatialInsertion actual (fun _ => gauge) 0) := by
    apply Commute.smul_right
    apply Commute.sum_right
    intro j _
    exact (grade_spin 0 _).mul_right (grade_gauge 0 _)
  have insertion : Commute (grade 0) (YangMills.Response.Forcing.insertion actual (fun _ => gauge) 0) := by
    apply LinearMap.ext
    intro v
    have temporal (w : DiracExteriorMatterCarrier) :=
      LinearMap.congr_fun (grade_principal_inverse 0 actual 0).eq w
    have localSpatial := LinearMap.congr_fun spatial.eq v
    have gaugePart := LinearMap.congr_fun (grade_gauge 0
      (StageNineP286GaugeConnectionVariation.p286GaugeConnectionMotherVariation (fun _ => gauge) 0 0)).eq v
    simp only [Module.End.mul_apply] at temporal localSpatial gaugePart
    change grade 0 (-currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0)
      (YangMills.Response.Forcing.spatialInsertion actual (fun _ => gauge) 0 v)-
      diracExteriorMotherLieAction _ v)=_
    rw [map_sub,map_neg,temporal,localSpatial,gaugePart]
    rfl
  exact operator_commute _ _ (insertion.smul_right Complex.I)

theorem gaugePotential_six (profile : GaugeProfile) (field : FullMatterL2) :
    six (gaugePotential profile field)=gaugePotential profile (six field) := by
  apply Lp.ext
  filter_upwards [six_ae (gaugePotential profile field),gaugePotential_ae profile field,
    gaugePotential_ae profile (six field),six_ae field] with x outer left right inner
  rw [outer,left,right,inner]
  have identity := congrArg (fun A : FiberOperators => A (field x)) (gaugeMap_six (profile x)).eq
  simpa only [mul_apply_eq_comp] using identity

theorem nativeR_six (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) (field : FullMatterL2) :
    six (nativeR point energy damping positive profile parameter field)=
      nativeR point energy damping positive profile parameter (six field) := by
  apply gaugeR_unique point energy damping positive _ (gaugePotential_selfAdjoint profile) parameter
  have solved := gaugeR_solves point energy damping positive _ (gaugePotential_selfAdjoint profile) parameter field
  change nativeR point energy damping positive profile parameter field=freeR point energy damping positive
    (field+(parameter : ℂ) • gaugePotential profile (nativeR point energy damping positive profile parameter field)) at solved
  have projected := congrArg six solved
  change six (nativeR point energy damping positive profile parameter field)=freeR point energy damping positive
    (six field+(parameter : ℂ) • gaugePotential profile (six (nativeR point energy damping positive profile parameter field)))
  simpa only [freeR_six,map_add,map_smul,gaugePotential_six] using projected

theorem inversePrincipal_six (point : BasePoint) (field : FullMatterL2) :
    six (inversePrincipal point field)=inversePrincipal point (six field) := by
  apply Lp.ext
  filter_upwards [six_ae (inversePrincipal point field),six_ae field,
    (operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))).coeFn_compLpL field,
    (operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))).coeFn_compLpL (six field)]
    with x outer inner left right
  erw [outer,left,right,inner]
  exact congrArg (fun A : FiberOperators => A (field x))
    (operator_commute _ _ (grade_principal_inverse 0 actual point)).eq

def gaugeG (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) : PerturbedGreen.SpatialOperators :=
  Complex.I • (nativeR point energy damping positive profile parameter).comp (inversePrincipal point)

theorem gaugeG_six (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) (field : FullMatterL2) :
    six (gaugeG point energy damping positive profile parameter field)=
      gaugeG point energy damping positive profile parameter (six field) := by
  change six (Complex.I • nativeR point energy damping positive profile parameter (inversePrincipal point field))=_
  rw [map_smul,nativeR_six,inversePrincipal_six]
  rfl

theorem two_scalar_insertions_zero (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (profile : GaugeProfile) (parameter : ℝ) (first second : ScalarProfile) (field : FullMatterL2) :
    potential first (gaugeG point energy damping positive profile parameter (potential second field))=0 := by
  have projected := gaugeG_six point energy damping positive profile parameter (potential second field)
  rw [six_potential] at projected
  have killed := potential_six first (gaugeG point energy damping positive profile parameter (potential second field))
  rw [projected] at killed
  exact killed

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
