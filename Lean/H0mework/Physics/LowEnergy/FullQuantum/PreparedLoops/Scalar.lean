import H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer

/-! The raw independent-dual scalar force and reader retain the same one-way arrow in the common transfer carrier. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops
open ClosedLoops CoframeResponse Triangular
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open StageNineHolonomicField StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
noncomputable section

def scalarForce (point : BasePoint) (scalar : ScalarCoordinateCarrier) : Mother :=
  temporalForce actual point (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm scalar))

def scalarReader (point : BasePoint) (scalar : ScalarCoordinateCarrier) : Mother :=
  (-1 : ℂ) • (boundaryWeight actual point*scalarForce point scalar)

theorem scalarForce_arrow (point : BasePoint) (scalar : ScalarCoordinateCarrier) : Arrow (scalarForce point scalar) :=
  (Arrow.diagonal_left (grade_principal_inverse 0 actual point) (original_scalar_vertex scalar)).smul (-Complex.I)

theorem scalarReader_arrow (point : BasePoint) (scalar : ScalarCoordinateCarrier) : Arrow (scalarReader point scalar) :=
  (Arrow.diagonal_left (boundary_grade actual point) (scalarForce_arrow point scalar)).smul (-1)

theorem transferRead_scalar_force_zero (point : BasePoint) (scalar : ScalarCoordinateCarrier)
    (B B0 Rplus Rplus0 Rminus Rminus0 : Mother) (reader : Expansion B B0)
    (plus : Expansion Rplus Rplus0) (minus : Expansion Rminus Rminus0) :
    transferRead point (scalarForce point scalar) B Rplus Rminus=0 := by
  rw [transferRead_generated,
    arrow_prepared_zero point _ ((reader.mul plus).arrow_left (scalarForce_arrow point scalar)),
    arrow_prepared_zero point _ (Expansion.arrow_right (Expansion.arrow_right (scalarForce_arrow point scalar) minus) reader),
    sub_self]

theorem transferRead_scalar_reader_zero (point : BasePoint) (scalar : ScalarCoordinateCarrier)
    (T T0 Rplus Rplus0 Rminus Rminus0 : Mother) (force : Expansion T T0)
    (plus : Expansion Rplus Rplus0) (minus : Expansion Rminus Rminus0) :
    transferRead point T (scalarReader point scalar) Rplus Rminus=0 := by
  rw [transferRead_generated,
    arrow_prepared_zero point _ (Expansion.arrow_right (Expansion.arrow_right (scalarReader_arrow point scalar) plus) force),
    arrow_prepared_zero point _ ((force.mul minus).arrow_left (scalarReader_arrow point scalar)),sub_self]

theorem source_scalar_gauge_transfer_zero (point : BasePoint) (scalar : ScalarCoordinateCarrier)
    (readerDirection : LorentzianIndex) (readerData : SU7MotherLieAlgebra.P286LieBlockData)
    (plus minus : SourceStep) :
    transferRead point (scalarForce point scalar) (sourceReader point readerDirection readerData)
      (fullResolvent actual point plus.momentum (Retarded.spectralParameter plus.energy plus.damping))
      (fullResolvent actual point minus.momentum (Retarded.spectralParameter minus.energy minus.damping))=0 :=
  transferRead_scalar_force_zero point scalar _ _ _ _ _ _
    (Expansion.refl _ (sourceReader_grade point readerDirection readerData))
    (source_resolvent actual point plus.momentum _ (plus.regular point).2)
    (source_resolvent actual point minus.momentum _ (minus.regular point).2)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops
