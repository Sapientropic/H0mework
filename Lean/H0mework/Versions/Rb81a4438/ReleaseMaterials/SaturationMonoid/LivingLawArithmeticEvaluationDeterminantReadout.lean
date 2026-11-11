import H0mework.Realization.Determinant.LatticeTrivialization

/-!
# Determinant-line readout authority

This compatibility entry exports exactly the root-generated chain:

`RootGeneratedCofinalQuadraticEvaluationAt`
→ `RootGeneratedPolarizedPairingAt`
→ `RootGeneratedLatticeDeterminantTrivializationAt`.

Its mathematical realization first generates the pairing-induced map on the
scalar extension of the integral lattice and then the top-exterior-line
trivialization. A matrix and scalar regulator occur only after a consumer
installs a frame through
`RootGeneratedLatticeDeterminantTrivializationRealizationAt.installedFrameMatrix`
and `regulatorCoordinate`.

The former caller-owned `entryExposure`/`algebra → Matrix.det` adapter has
been deleted. Keeping it in a legacy namespace would still leave a second,
lower determinant mouth callable and would fail the arithmetic deletion test.
This module intentionally defines no parallel determinant API.
-/

set_option autoImplicit false
