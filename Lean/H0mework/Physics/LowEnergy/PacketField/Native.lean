import H0mework.Physics.LowEnergy.PacketField.Counting
import H0mework.Physics.LowEnergy.PacketField.Alignment
import H0mework.Physics.LowEnergy.PacketPairResponse.Source

/-! The primitive source-table pairing is consumed by the actual reconstructed
L² field, its local quadratic current and the same certified band response. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace PacketPairResponse Filter Topology
noncomputable section
attribute [local irreducible] retardedField reconstructedField
variable {ι : Type*} [Fintype ι]

theorem reconstructedField_response (current : Matrix ι ι ℝ)
    (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (sourcePairing : ∀ point : LightBand, point.val≠0 → ∀ first second : Bool,
      contractedPair current (fun sign => poleColumn circleY circleZ numerator sign point) first second=
        ((if first=second then bandCoupling true point else bandCoupling false point : ℝ) : ℂ))
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    localQuadratic current (reconstructedField circleY circleZ numerator energy damping positive time)=
      bandResponse energy damping positive time := by
  rw [reconstructedField_current,← forwardFeedback_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [band_nonzero_ae] with point nonzero
  unfold retardedField
  exact quadraticDensity_fourGram current (fun sign => poleColumn circleY circleZ numerator sign point)
    (bandCoupling true point) (bandCoupling false point) (sourcePairing point nonzero)
    (fun sign => branchOnBand energy damping positive sign time point)

theorem reconstructedField_limit (current : Matrix ι ι ℝ)
    (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (sourcePairing : ∀ point : LightBand, point.val≠0 → ∀ first second : Bool,
      contractedPair current (fun sign => poleColumn circleY circleZ numerator sign point) first second=
        ((if first=second then bandCoupling true point else bandCoupling false point : ℝ) : ℂ))
    (energy damping : ℝ) (positive : 0 < damping) :
    Tendsto (fun time : ℝ =>
      localQuadratic current (reconstructedField circleY circleZ numerator energy damping positive time)/time^2)
      (𝓝[≠] 0) (𝓝 (bandLeading energy damping positive)) := by
  simp_rw [reconstructedField_response current circleY circleZ numerator sourcePairing]
  exact bandResponse_limit energy damping positive

theorem reconstructedField_source (current : Matrix ι ι ℝ)
    (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (sourcePairing : ∀ point : LightBand, point.val≠0 → ∀ first second : Bool,
      contractedPair current (fun sign => poleColumn circleY circleZ numerator sign point) first second=
        ((if first=second then bandCoupling true point else bandCoupling false point : ℝ) : ℂ))
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    localQuadratic current (reconstructedField circleY circleZ numerator energy damping positive time)=
      fourierDensity*∫ point : LightBand, sourceFourFeedback (bandCoupling true point) (bandCoupling false point)
        energy damping positive (bandShift point) time ∂bandMeasure := by
  rw [reconstructedField_response current circleY circleZ numerator sourcePairing,bandResponse_source]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
