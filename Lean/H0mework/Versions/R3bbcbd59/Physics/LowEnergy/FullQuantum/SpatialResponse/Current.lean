import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.SpatialResponse.Readback

/-! The original volume and native Dirac vertex generate the real driven-current derivative with both independent legs. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialResponse
open FullSpace GaugeGreen ScalarGreen PerturbedGreen YangMills.FullPairing
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
noncomputable section
attribute [local irreducible] fullG family

def volumeWeight : ℂ := ((|(actual.coframe 0).det| : ℝ) : ℂ)

def complexCurrent (energy damping : ℝ) (positive : 0<damping)
    (gauge direction probe : GaugeProfile) (scalar scalarDirection scalarProbe : ScalarProfile)
    (dual source : FullMatterL2) (epsilon : ℝ) : ℂ :=
  volumeWeight*inner ℂ ((family energy damping positive gauge direction scalar scalarDirection epsilon).adjoint dual)
    (variation probe scalarProbe (family energy damping positive gauge direction scalar scalarDirection epsilon source))

def physicalCurrent (energy damping : ℝ) (positive : 0<damping)
    (gauge direction probe : GaugeProfile) (scalar scalarDirection scalarProbe : ScalarProfile)
    (dual source : FullMatterL2) (epsilon : ℝ) : ℝ :=
  (complexCurrent energy damping positive gauge direction probe scalar scalarDirection scalarProbe dual source epsilon).re

theorem native_vertex_ae (probe : GaugeProfile) (scalarProbe : ScalarProfile) (field : FullMatterL2) :
    variation probe scalarProbe field=ᵐ[volume] fun x =>
      operator (PerturbedGreen.insertion actual (gaugeField probe) (fun _ => 0) (PerturbedGreen.spatialPoint x)) (field x)+
      operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (scalarProbe x))) (field x) := by
  filter_upwards [rawGauge_ae probe field,potential_ae scalarProbe field,
    Lp.coeFn_add (rawGauge 0 probe field) (potential scalarProbe field)] with x gaugeRead scalarRead added
  simp only [Pi.add_apply] at added
  change (rawGauge 0 probe field+potential scalarProbe field) x=_
  rw [added,gaugeRead,scalarRead]

theorem complexCurrent_native (energy damping : ℝ) (positive : 0<damping)
    (gauge direction probe : GaugeProfile) (scalar scalarDirection scalarProbe : ScalarProfile)
    (dual source : FullMatterL2) (epsilon : ℝ) :
    let primal := family energy damping positive gauge direction scalar scalarDirection epsilon source
    let conjugate := (family energy damping positive gauge direction scalar scalarDirection epsilon).adjoint dual
    complexCurrent energy damping positive gauge direction probe scalar scalarDirection scalarProbe dual source epsilon=
      volumeWeight*(∫ x, inner ℂ (conjugate x)
        (operator (PerturbedGreen.insertion actual (gaugeField probe) (fun _ => 0) (PerturbedGreen.spatialPoint x))
          (primal x)+
        operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (scalarProbe x))) (primal x))) := by
  dsimp only
  unfold complexCurrent
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [native_vertex_ae probe scalarProbe
    (family energy damping positive gauge direction scalar scalarDirection epsilon source)] with x read
  rw [read]

theorem physicalCurrent_derivative (energy damping : ℝ) (positive : 0<damping)
    (gauge direction probe : GaugeProfile) (scalar scalarDirection scalarProbe : ScalarProfile)
    (dual source : FullMatterL2) :
    let G := fullG 0 energy damping positive gauge 1 scalar
    let V := variation direction scalarDirection
    let B := variation probe scalarProbe
    HasDerivAt (physicalCurrent energy damping positive gauge direction probe scalar scalarDirection scalarProbe dual source)
      ((volumeWeight*bilinearRead dual source (-(G*V*G)*B*G+G*B*(-(G*V*G)))).re) 0 := by
  dsimp only
  have differentiated := (independent_current_derivative energy damping positive gauge direction scalar scalarDirection
    (variation probe scalarProbe) dual source).const_mul volumeWeight
  have realPart := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 differentiated
  exact realPart

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialResponse
