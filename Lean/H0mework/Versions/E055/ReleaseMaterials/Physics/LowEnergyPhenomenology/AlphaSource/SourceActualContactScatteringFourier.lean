import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualOrderedScatteringFourier

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedScatteringFourierReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage10 Stage9DEF.Compatibility
open DiracExteriorMatterAction YangMills.FullPairing FullQuantum FullSpace FullQuantum.PerturbedGreen
open PreparationPhysicalJointGeneratorEnergyReturn PreparationPhysicalChargedScatteringPoleReturn
open PreparationPhysicalChargedPacketQuantumReturn PreparationVacuumElectromagneticIdentity
open Electromagnetic.CanonicalCoframe MeasureTheory Filter
open scoped InnerProductSpace BigOperators Matrix

/-- Direct contact retains the original full mixed density and shell coefficients outside the age integral. -/
def sourceContactInterior (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) : SpatialOperators :=
  spatialFlow 0 (-time)*(C j).compLpL 2 volume*spatialFlow 0 time

def sourceContactFiber (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) (p : Fin 3→ℝ) : FiberOperators :=
  evolution actual 0 p (-time)*C j*evolution actual 0 p time

private theorem contact_fourier (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) (field : FullMatterL2) :
    fourier (sourceContactInterior C time j field)=ᵐ[volume]
      fun k=>sourceContactFiber C time j (physicalMomentum k) (fourier field k) := by
  let propagated:=spatialFlow 0 time field
  have inserted : fourier ((C j).compLpL 2 volume propagated)=ᵐ[volume]
      fun k=>C j (fourier propagated k) := by
    rw [GaugeGreen.constant_fourier]
    exact (C j).coeFn_compLpL _
  filter_upwards [spatialFlow_fourier_ae 0 (-time) ((C j).compLpL 2 volume propagated),
    inserted,spatialFlow_fourier_ae 0 time field] with k outer middle initial
  change fourier (spatialFlow 0 (-time) ((C j).compLpL 2 volume propagated)) k=_
  rw [outer,middle,initial]
  rfl

def sourceActualContactIntegrand (sideL edgeL sideR edgeR : Fin 2)
    (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) (k : Position) : ℂ :=
  inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
    (sourceContactFiber C time j (physicalMomentum k)
      (sourceActualCoordinateMomentum j (physicalMomentum k) •
        fourier (sourceChargedFilteredPacket sideR edgeR) k))

private theorem contact_integrand_source (sideL edgeL sideR edgeR : Fin 2)
    (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) :
    (fun k=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
      (fourier (sourceContactInterior C time j (coordinateLeg j (sourceActualScatteringInput sideR edgeR))) k))=ᵐ[volume]
        sourceActualContactIntegrand sideL edgeL sideR edgeR C time j := by
  filter_upwards [contact_fourier C time j (coordinateLeg j (sourceActualScatteringInput sideR edgeR)),
    sourceActualScatteringCoordinateLeg_fourier sideR edgeR j] with k contact right
  rw [contact,right]
  rfl

theorem sourceActualContactIntegrand_integrable (sideL edgeL sideR edgeR : Fin 2)
    (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) :
    Integrable (sourceActualContactIntegrand sideL edgeL sideR edgeR C time j) volume :=
  (L2.integrable_inner (𝕜:=ℂ) _ _).congr (contact_integrand_source sideL edgeL sideR edgeR C time j)

theorem sourcePreparedContactRead_fourier (sideL edgeL sideR edgeR : Fin 2)
    (C : Fin 4→FiberOperators) (time : ℝ) :
    sourceActualScatteringRead sideL edgeL sideR edgeR (contactWord C time)=
      ∑j : Fin 4,∫k,sourceActualContactIntegrand sideL edgeL sideR edgeR C time j k := by
  rw [sourceActualScatteringRead_source,contactWord]
  simp only [sum_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  change inner ℂ (sourceActualScatteringInput sideL edgeL)
    ((coordinateLeg 0).adjoint (sourceContactInterior C time j
      (coordinateLeg j (sourceActualScatteringInput sideR edgeR))))=_
  rw [ContinuousLinearMap.adjoint_inner_right,sourceActualScatteringInput_return,←fourier.inner_map_map,L2.inner_def]
  exact integral_congr_ae (contact_integrand_source sideL edgeL sideR edgeR C time j)

def sourceActualContactPoleIntegrand (sideL edgeL sideR edgeR : Fin 2)
    (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) (k : Position) : ℂ :=
  ∑left : RestStateIndex,∑right : RestStateIndex,
    star (sourceActualPreparedPoleWeight sideL edgeL k left)*
      (sourceActualCoordinateMomentum j (physicalMomentum k)*sourceActualPreparedPoleWeight sideR edgeR k right)*
        inner ℂ (naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) left)))
          (sourceContactFiber C time j (physicalMomentum k)
            (naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) right))))

theorem sourceActualContactIntegrand_poles (sideL edgeL sideR edgeR : Fin 2)
    (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) :
    sourceActualContactIntegrand sideL edgeL sideR edgeR C time j=ᵐ[volume]
      sourceActualContactPoleIntegrand sideL edgeL sideR edgeR C time j := by
  filter_upwards [sourceActualFilteredPacket_poles sideL edgeL,sourceActualFilteredPacket_poles sideR edgeR]
    with k left right
  simp only [sourceActualContactIntegrand,left,right,Finset.smul_sum,map_sum,map_smul,smul_smul,
    sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply,sourceActualContactPoleIntegrand,mul_assoc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro leftState _
  apply Finset.sum_congr rfl
  intro rightState _
  ring

theorem sourceActualContactPoleIntegrand_integrable (sideL edgeL sideR edgeR : Fin 2)
    (C : Fin 4→FiberOperators) (time : ℝ) (j : Fin 4) :
    Integrable (sourceActualContactPoleIntegrand sideL edgeL sideR edgeR C time j) volume :=
  (sourceActualContactIntegrand_integrable sideL edgeL sideR edgeR C time j).congr
    (sourceActualContactIntegrand_poles sideL edgeL sideR edgeR C time j)

theorem sourcePreparedContactRead_poles (sideL edgeL sideR edgeR : Fin 2)
    (C : Fin 4→FiberOperators) (time : ℝ) :
    sourceActualScatteringRead sideL edgeL sideR edgeR (contactWord C time)=
      ∑j : Fin 4,∫k,sourceActualContactPoleIntegrand sideL edgeL sideR edgeR C time j k := by
  rw [sourcePreparedContactRead_fourier]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_congr_ae (sourceActualContactIntegrand_poles sideL edgeL sideR edgeR C time j)

/-- Both original frequency branches and the direct full contact consume the same actual two preparations. -/
theorem sourcePreparedScatteringPair_poles (sideL edgeL sideR edgeR : Fin 2)
    (A B : TransferPair) (shift : Fin 3→ℝ) (time age : ℝ) :
    sourcePreparedScatteringPair sideL edgeL sideR edgeR A B shift time age=
      (Complex.I*((∑i : Fin 4,∑j : Fin 4,∫k,sourceActualOrderedPoleIntegrand sideL edgeL sideR edgeR
        (shiftCoefficients (adjointCoefficients (complexFrequencyCoefficients B.negative)) shift)
        (realReaderCoefficients A shift) (-shift) age time i j k)-
        ∑i : Fin 4,∑j : Fin 4,∫k,sourceActualOrderedPoleIntegrand sideL edgeL sideR edgeR
          (realReaderCoefficients A shift) (complexFrequencyCoefficients B.positive) shift time age i j k),
        ∑j : Fin 4,∫k,sourceActualContactPoleIntegrand sideL edgeL sideR edgeR (realMixedCoefficients A B) time j k) := by
  rw [sourcePreparedScatteringPair_fullCAR]
  simp only [sourcePreparedOrderedCAR_poles]
  congr 1
  rw [←sourceActualScatteringRead_source,fieldMixedContact,sourcePreparedContactRead_poles]

end LowEnergy.PreparationPhysicalChargedScatteringFourierReturn
