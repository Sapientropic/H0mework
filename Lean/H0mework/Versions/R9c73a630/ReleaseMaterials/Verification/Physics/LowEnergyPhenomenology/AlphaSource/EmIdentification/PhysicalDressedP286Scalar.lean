import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalDressedScalarColumns
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalDressedScalarSkew
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMDressedPreparedRead
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterNativeCarrier
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointPhaseAction
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourcePreparation

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
noncomputable section

namespace LowEnergy.DressedColourY

open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstGaugeBackgroundReturn
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussFockLift
open GaussComposite Electromagnetic.Identification
open CanonicalGradedCurrent GaussQuantumMultiplier CanonicalGradedSpatialSource GaussDensityCore
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction Stage9C.Material.SpinPair
open SU7ExteriorMatterRepresentation StageNineExteriorMotherLieRepresentation
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286LinkedActiveScalarPairingSkew
open PreparationPhysicalDressedSpinChargeReturn
open GaussComposite.PhysicalEMGaugeRealization GaussComposite.PhysicalEMVoltage
open GaussComposite.PhysicalEMDressedCharacter GaussComposite.PhysicalEMDressedPreparedRead
open GaussComposite.ActualDressedSourcePreparation
open NamedMatterWedgeQt NamedColorQtNext
open DressedColourYScalarColumns DressedColourYScalarRows
open scoped BigOperators ContDiff InnerProductSpace Matrix

attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _

/-- The unsigned coordinate recognizer: the degree-four exterior basis maps
to the Euclidean single under the declared scalar chart. -/
private theorem scalar_coord_symm_single (I : ScalarBasisIndex) :
    scalarCoordinateEquiv.symm (EuclideanSpace.single I (1 : ℂ)) =
      su7ExteriorBasis 4 I := by
  apply (su7ExteriorBasis 4).repr.injective
  ext candidate
  simp [scalarCoordinateEquiv]

private theorem scalar_coord_basis (I : ScalarBasisIndex) :
    scalarCoordinateEquiv (su7ExteriorBasis 4 I) =
      EuclideanSpace.single I (1 : ℂ) := by
  rw [← scalar_coord_symm_single I]
  exact LinearEquiv.apply_symm_apply _ _

/-- The signed scalar basis vector read in the Euclidean scalar carrier. -/
private def signedCoordinate (channel : Fin 2) (c : Fin 3) : ScalarCoordinateCarrier :=
  scalarCoordinateEquiv (signedScalarBasis channel c)

private theorem signed_coordinate_eq (channel : Fin 2) (c : Fin 3) :
    signedCoordinate channel c =
      (if c = 1 then (-1 : ℂ) else 1) •
        EuclideanSpace.single (Composite.scalarBasis channel c) 1 := by
  unfold signedCoordinate signedScalarBasis
  rw [ite_smul, apply_ite scalarCoordinateEquiv, map_smul, map_smul,
    scalar_coord_basis, ← ite_smul]

/-- The scalar coefficient is the inner product against the signed basis. -/
private theorem coefficient_eq_inner (channel : Fin 2) (c : Fin 3)
    (phi : ScalarCoordinateCarrier) :
    scalarCoefficient channel c phi =
      inner ℂ (signedCoordinate channel c) phi := by
  have coord_eval : scalarCoefficient channel c phi =
      (if c = 1 then (-1 : ℂ) else 1) * phi (Composite.scalarBasis channel c) := by
    change (if c = 1 then (-1 : ℂ) else 1) •
        (su7ExteriorBasis 4).coord (Composite.scalarBasis channel c)
          (scalarCoordinateEquiv.symm phi) = _
    rw [smul_eq_mul]
    congr 1
    simp [scalarCoordinateEquiv]
  rw [coord_eval, signed_coordinate_eq, inner_smul_left,
    EuclideanSpace.inner_single_left]
  split_ifs <;> simp

/-- The signed column law transported to the Euclidean scalar carrier. -/
private theorem signed_coordinate_column (data : P286LieBlockData)
    (channel : Fin 2) (c : Fin 3) :
    scalarMotherLieAction (p286LieBlockEmbed data) (signedCoordinate channel c) =
      -(∑ d : Fin 3, ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) c d) •
        signedCoordinate channel d) := by
  unfold scalarMotherLieAction signedCoordinate
  rw [LinearEquiv.symm_apply_apply, scalar_signed_column, map_neg, map_sum]
  simp_rw [map_smul]

/-- The complex skew-adjointness of the P286 colour block reads
`conj A_{c,d} = -A_{d,c}`. -/
private theorem colour_conjugate (data : P286LieBlockData) (c d : Fin 3) :
    star ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) c d) =
      -((data.1 : Matrix (Fin 3) (Fin 3) ℂ) d c) := by
  have skewed := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M d c)
    (specialUnitaryLieMatrix_star data.1)
  simpa [Matrix.star_apply, Matrix.neg_apply] using skewed

/-- The general P286 scalar row law: the coefficient of the varied scalar is
the conjugate-transposed colour-matrix action on coefficients, using the
original block data of any native Lie direction. -/
theorem scalar_action_row (a : NativeLie) (channel : Fin 2) (c : Fin 3)
    (phi : ScalarCoordinateCarrier) :
    scalarCoefficient channel c
        (scalarMotherLieAction (p286LieBlockEmbed (nativeData a)) phi) =
      -(∑ d : Fin 3, (nativeData a).1.val d c * scalarCoefficient channel d phi) := by
  have skewed := scalar_action_complex_skew (p286LieBlockEmbed (nativeData a))
    (signedCoordinate channel c) phi
  have hrow : inner ℂ (signedCoordinate channel c)
        (scalarMotherLieAction (p286LieBlockEmbed (nativeData a)) phi) =
      -inner ℂ (scalarMotherLieAction (p286LieBlockEmbed (nativeData a))
        (signedCoordinate channel c)) phi :=
    eq_neg_of_add_eq_zero_right skewed
  rw [coefficient_eq_inner, hrow, signed_coordinate_column, inner_neg_left,
    neg_neg, sum_inner]
  simp_rw [inner_smul_left]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [starRingEnd_apply, ← coefficient_eq_inner,
    colour_conjugate (nativeData a) c d, neg_mul]

end LowEnergy.DressedColourY
