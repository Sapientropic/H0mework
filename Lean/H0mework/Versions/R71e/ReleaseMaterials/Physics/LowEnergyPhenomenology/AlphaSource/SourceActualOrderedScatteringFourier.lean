import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargedRestPole

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedScatteringFourierReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage10
open Stage9DEF.Compatibility DiracExteriorMatterAction YangMills.FullPairing FullQuantum FullSpace FullQuantum.PerturbedGreen
open PreparationPhysicalJointGeneratorEnergyReturn PreparationPhysicalChargedScatteringPoleReturn
open PreparationPhysicalChargedPacketQuantumReturn PreparationVacuumElectromagneticIdentity
open Electromagnetic.CanonicalCoframe MeasureTheory Filter
open scoped InnerProductSpace BigOperators Matrix

/-- The original ordered interior retains full252 propagation between the two field insertions. -/
def sourceOrderedInterior (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    SpatialOperators :=
  spatialFlow 0 (-time)*(shiftCoefficients A shift i).compLpL 2 volume*
    shiftFlow shift (time-age)*(B j).compLpL 2 volume*spatialFlow 0 age

def sourceOrderedFiber (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ)
    (i j : Fin 4) (p : Fin 3→ℝ) : FiberOperators :=
  evolution actual 0 p (-time)*shiftCoefficients A shift i*
    evolution actual 0 (fun axis=>p axis+shift axis) (time-age)*B j*evolution actual 0 p age

private theorem constant_fourier_ae (A : FiberOperators) (field : FullMatterL2) :
    fourier (A.compLpL 2 volume field)=ᵐ[volume] fun k=>A (fourier field k) := by
  rw [GaugeGreen.constant_fourier]
  exact A.coeFn_compLpL _

theorem sourceOrderedInterior_fourier (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ)
    (i j : Fin 4) (field : FullMatterL2) :
    fourier (sourceOrderedInterior A B shift time age i j field)=ᵐ[volume]
      fun k=>sourceOrderedFiber A B shift time age i j (physicalMomentum k) (fourier field k) := by
  let right:=spatialFlow 0 age field
  let force:=(B j).compLpL 2 volume right
  let propagated:=shiftFlow shift (time-age) force
  let reader:=(shiftCoefficients A shift i).compLpL 2 volume propagated
  filter_upwards [spatialFlow_fourier_ae 0 (-time) reader,
    constant_fourier_ae (shiftCoefficients A shift i) propagated,
    shiftFlow_fourier shift (time-age) force,constant_fourier_ae (B j) right,
    spatialFlow_fourier_ae 0 age field] with k outer first middle second initial
  change fourier (spatialFlow 0 (-time) reader) k=_
  rw [outer,first,middle,second,initial]
  rfl

/-- The integrand keeps the actual prepared external legs and all original time and momentum ordering. -/
def sourceActualOrderedIntegrand (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) (k : Position) : ℂ :=
  inner ℂ (sourceActualCoordinateMomentum i (physicalMomentum k) •
    fourier (sourceChargedFilteredPacket sideL edgeL) k)
      (sourceOrderedFiber A B shift time age i j (physicalMomentum k)
        (sourceActualCoordinateMomentum j (physicalMomentum k) •
          fourier (sourceChargedFilteredPacket sideR edgeR) k))

private theorem ordered_integrand_source (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    (fun k=>inner ℂ (fourier (coordinateLeg i (sourceActualScatteringInput sideL edgeL)) k)
      (fourier (sourceOrderedInterior A B shift time age i j
        (coordinateLeg j (sourceActualScatteringInput sideR edgeR))) k))=ᵐ[volume]
          sourceActualOrderedIntegrand sideL edgeL sideR edgeR A B shift time age i j := by
  filter_upwards [sourceActualScatteringCoordinateLeg_fourier sideL edgeL i,
    sourceActualScatteringCoordinateLeg_fourier sideR edgeR j,
    sourceOrderedInterior_fourier A B shift time age i j (coordinateLeg j (sourceActualScatteringInput sideR edgeR))]
      with k left right interior
  rw [left,interior,right]
  rfl

theorem sourceActualOrderedIntegrand_integrable (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    Integrable (sourceActualOrderedIntegrand sideL edgeL sideR edgeR A B shift time age i j) volume :=
  (L2.integrable_inner (𝕜:=ℂ) _ _).congr (ordered_integrand_source sideL edgeL sideR edgeR A B shift time age i j)

theorem sourcePreparedOrderedCAR_fourier (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    sourcePreparedOrderedCAR sideL edgeL sideR edgeR A B shift time age i j=
      ∫k,sourceActualOrderedIntegrand sideL edgeL sideR edgeR A B shift time age i j k := by
  rw [sourcePreparedOrderedCAR_source]
  change inner ℂ (sourceActualScatteringInput sideL edgeL)
    ((coordinateLeg i).adjoint (sourceOrderedInterior A B shift time age i j
      (coordinateLeg j (sourceActualScatteringInput sideR edgeR))))=_
  rw [ContinuousLinearMap.adjoint_inner_right,←fourier.inner_map_map,L2.inner_def]
  exact integral_congr_ae (ordered_integrand_source sideL edgeL sideR edgeR A B shift time age i j)

/-- The two complete source spectra remain inside one integrable expression, including every cross term. -/
def sourceActualOrderedPoleIntegrand (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) (k : Position) : ℂ :=
  ∑left : RestStateIndex,∑right : RestStateIndex,
    star (sourceActualCoordinateMomentum i (physicalMomentum k)*sourceActualPreparedPoleWeight sideL edgeL k left)*
      (sourceActualCoordinateMomentum j (physicalMomentum k)*sourceActualPreparedPoleWeight sideR edgeR k right)*
        inner ℂ (naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) left)))
          (sourceOrderedFiber A B shift time age i j (physicalMomentum k)
            (naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) right))))

theorem sourceActualOrderedIntegrand_poles (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    sourceActualOrderedIntegrand sideL edgeL sideR edgeR A B shift time age i j=ᵐ[volume]
      sourceActualOrderedPoleIntegrand sideL edgeL sideR edgeR A B shift time age i j := by
  filter_upwards [sourceActualFilteredPacket_poles sideL edgeL,sourceActualFilteredPacket_poles sideR edgeR]
    with k left right
  simp only [sourceActualOrderedIntegrand,left,right,Finset.smul_sum,map_sum,map_smul,smul_smul,
    sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply,sourceActualOrderedPoleIntegrand,mul_assoc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro leftState _
  apply Finset.sum_congr rfl
  intro rightState _
  ring

theorem sourceActualOrderedPoleIntegrand_integrable (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    Integrable (sourceActualOrderedPoleIntegrand sideL edgeL sideR edgeR A B shift time age i j) volume :=
  (sourceActualOrderedIntegrand_integrable sideL edgeL sideR edgeR A B shift time age i j).congr
    (sourceActualOrderedIntegrand_poles sideL edgeL sideR edgeR A B shift time age i j)

theorem sourcePreparedOrderedCAR_poles (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    sourcePreparedOrderedCAR sideL edgeL sideR edgeR A B shift time age i j=
      ∫k,sourceActualOrderedPoleIntegrand sideL edgeL sideR edgeR A B shift time age i j k := by
  rw [sourcePreparedOrderedCAR_fourier]
  exact integral_congr_ae (sourceActualOrderedIntegrand_poles sideL edgeL sideR edgeR A B shift time age i j)

end LowEnergy.PreparationPhysicalChargedScatteringFourierReturn
