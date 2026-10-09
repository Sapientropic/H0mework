import H0mework.Physics.LowEnergy.PacketFieldTime.Pole

/-! The existing source PacketField.spectrum and spatially reconstructed field have a
genuine strong L² derivative with a continuous L² velocity. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFieldTime
open FullQuantum FullSpace PacketPairResponse PacketField PacketFourier LightCausal DrivenInteraction
noncomputable section
variable {ι : Type*} [Fintype ι]
attribute [local irreducible] poleLift phasePacket PacketField.spectrum

def spectralVelocity (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) : FieldSpace FullMatterL2 :=
  -(∑ sign : Bool, poleLift circleY circleZ numerator sign row (branchSpeed energy damping positive sign time))

theorem spectralVelocity_ae (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) :
    spectralVelocity circleY circleZ numerator energy damping positive time row=ᵐ[volume]
      physicalBand (fun point => -(∑ sign : Bool, poleColumn circleY circleZ numerator sign point row •
        ((growthSign sign*(thetaRate (bandMomentum point) : ℂ)) • branchOnBand energy damping positive sign time point+
          phasePacket energy damping positive (bandShift point) time))) :=
  polePair_ae circleY circleZ numerator row (fun sign => branchSpeed energy damping positive sign time)

attribute [local irreducible] branchCurve branchSpeed

theorem lifted_branch_derivative (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (sign : Bool) (time : ℝ) (row : ι) :
    HasDerivAt (fun t => poleLift circleY circleZ numerator sign row (branchCurve energy damping positive sign t))
      (poleLift circleY circleZ numerator sign row (branchSpeed energy damping positive sign time)) time :=
  ((poleLift circleY circleZ numerator sign row).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    time (branchCurve_derivative energy damping positive sign time)

theorem spectrum_derivative (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) :
    HasDerivAt (fun t => PacketField.spectrum circleY circleZ numerator energy damping positive t row)
      (spectralVelocity circleY circleZ numerator energy damping positive time row) time := by
  have generated : HasDerivAt
      (fun t => -(∑ sign : Bool, poleLift circleY circleZ numerator sign row (branchCurve energy damping positive sign t)))
      (-(∑ sign : Bool, poleLift circleY circleZ numerator sign row (branchSpeed energy damping positive sign time))) time :=
    (HasDerivAt.fun_sum (u := Finset.univ) (fun sign _ =>
      lifted_branch_derivative circleY circleZ numerator energy damping positive sign time row)).neg
  exact generated.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    spectrum_as_lift circleY circleZ numerator energy damping positive t row)

theorem spectralVelocity_continuous (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (row : ι) :
    Continuous (fun t => spectralVelocity circleY circleZ numerator energy damping positive t row) := by
  unfold spectralVelocity
  exact (continuous_finsetSum _ (fun sign _ =>
    (poleLift circleY circleZ numerator sign row).continuous.comp
      (branchSpeed_continuous energy damping positive sign))).neg

def reconstructedVelocity (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) : FieldSpace FullMatterL2 :=
  spatialFourier (spectralVelocity circleY circleZ numerator energy damping positive time row)

theorem reconstructedField_derivative (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) :
    HasDerivAt (fun t => reconstructedField circleY circleZ numerator energy damping positive t row)
      (reconstructedVelocity circleY circleZ numerator energy damping positive time row) time := by
  let readback : FieldSpace FullMatterL2 →L[ℝ] FieldSpace FullMatterL2 :=
    ((spatialFourier : FieldSpace FullMatterL2 ≃ₗᵢ[ℂ] FieldSpace FullMatterL2).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  exact readback.hasFDerivAt.comp_hasDerivAt time
    (spectrum_derivative circleY circleZ numerator energy damping positive time row)

theorem reconstructedVelocity_continuous (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (row : ι) :
    Continuous (fun t => reconstructedVelocity circleY circleZ numerator energy damping positive t row) :=
  spatialFourier.continuous.comp (spectralVelocity_continuous circleY circleZ numerator energy damping positive row)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFieldTime
