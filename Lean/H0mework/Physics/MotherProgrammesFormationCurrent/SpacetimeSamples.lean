import H0mework.Physics.MotherDescription.Carrier
import H0mework.Physics.MotherProgrammesFormationCurrent.Current

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholeSpacetimeMaterial

open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Revision
open Stage9CU.Fields Topology

noncomputable section

abbrev RationalPoint := Fin 4 → ℚ

def rationalPoint (point : RationalPoint) : BasePoint :=
  WithLp.toLp 2 (fun direction => (point direction : ℝ))

theorem rationalPoint_dense : IsDenseInducing rationalPoint := by
  have cast : IsDenseInducing (fun point : RationalPoint => fun i => (point i : ℝ)) :=
    ⟨Topology.IsInducing.piMap (fun _ => Rat.isEmbedding_coe_real.isInducing),
      DenseRange.piMap (fun _ : Fin 4 => Rat.denseRange_cast)⟩
  have coordinates : IsDenseInducing (fun point : Fin 4 → ℝ => WithLp.toLp 2 point) :=
    ⟨(PiLp.homeomorph 2 (fun _ : Fin 4 => ℝ)).symm.isInducing,
      (PiLp.homeomorph 2 (fun _ : Fin 4 => ℝ)).symm.surjective.denseRange⟩
  exact ⟨coordinates.isInducing.comp cast.isInducing,
    coordinates.dense.comp cast.dense coordinates.continuous⟩

abbrev Query := Coordinate × RationalPoint
noncomputable instance : Encodable Query := Encodable.ofCountable Query

/-- The original constructor and all nine fields on the fixed rational spacetime grid. -/
def samples (current : SpinPair.Current) : ℕ → ℝ
  | 0 => if Recognition.isRunning current then 1 else 0
  | address + 1 => match Encodable.decode (α := Query) address with
    | none => 0
    | some query => realCoordinate (Recognition.wholeField current) query.1 (rationalPoint query.2)

theorem samples_at (current : SpinPair.Current) (coordinate : Coordinate) (point : RationalPoint) :
    samples current (Encodable.encode (coordinate, point) + 1) =
      realCoordinate (Recognition.wholeField current) coordinate (rationalPoint point) := by
  simp only [samples, Encodable.encodek]

theorem samples_injective : Function.Injective samples := by
  intro left right same
  apply Recognition.reverseFaithful
  · have tag := congrFun same 0
    cases leftTag : Recognition.isRunning left <;>
      cases rightTag : Recognition.isRunning right <;> simp_all [samples]
  · intro coordinate point
    have sampled : (fun q => realCoordinate (Recognition.wholeField left) coordinate (rationalPoint q)) =
        fun q => realCoordinate (Recognition.wholeField right) coordinate (rationalPoint q) := by
      funext q
      exact (samples_at left coordinate q).symm.trans
        ((congrFun same (Encodable.encode (coordinate, q) + 1)).trans (samples_at right coordinate q))
    have restoredLeft := rationalPoint_dense.extend_unique
      (fun _ => rfl) (realCoordinate_continuous (WholeDescription.smooth left) coordinate)
    have restoredRight := rationalPoint_dense.extend_unique
      (fun _ => rfl) (realCoordinate_continuous (WholeDescription.smooth right) coordinate)
    rw [sampled] at restoredLeft
    exact congrFun (restoredLeft.symm.trans restoredRight) point

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholeSpacetimeMaterial
