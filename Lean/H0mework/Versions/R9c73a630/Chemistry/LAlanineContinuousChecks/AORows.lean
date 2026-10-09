import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOB0
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOB1
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOB2
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOB3
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOB4
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOB5
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOB6
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOB7
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOB8

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks

open Lean Elab Tactic SourceRectangle SourceSignedEvaluator SourceGroupCache

elab "closeCalculatedAORow " basis:num mode:ident : tactic => do
  let goals ← getGoals
  unless goals.length == 20 do throwError "complete source jet row required"
  let prefixName := "SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks.AOChecks."
  for (goal, j) in goals.zipIdx do
    let name := (prefixName ++ s!"ao_{basis.getNat}_{j}_{mode.getId.toString}").toName
    goal.assign (Lean.mkConst name)
  setGoals []

theorem cachedAORow0 (j : Jet) : calculatedAO j 0 = groupCachedOrbital cachedExp cachedPoly 0 j := by
  fin_cases j
  closeCalculatedAORow 0 computed

theorem reportedAORow0 (j : Jet) : calculatedAO j 0 = reportedAO j 0 := by
  fin_cases j
  closeCalculatedAORow 0 reported

theorem cachedAORow1 (j : Jet) : calculatedAO j 1 = groupCachedOrbital cachedExp cachedPoly 1 j := by
  fin_cases j
  closeCalculatedAORow 1 computed

theorem reportedAORow1 (j : Jet) : calculatedAO j 1 = reportedAO j 1 := by
  fin_cases j
  closeCalculatedAORow 1 reported

theorem cachedAORow2 (j : Jet) : calculatedAO j 2 = groupCachedOrbital cachedExp cachedPoly 2 j := by
  fin_cases j
  closeCalculatedAORow 2 computed

theorem reportedAORow2 (j : Jet) : calculatedAO j 2 = reportedAO j 2 := by
  fin_cases j
  closeCalculatedAORow 2 reported

theorem cachedAORow3 (j : Jet) : calculatedAO j 3 = groupCachedOrbital cachedExp cachedPoly 3 j := by
  fin_cases j
  closeCalculatedAORow 3 computed

theorem reportedAORow3 (j : Jet) : calculatedAO j 3 = reportedAO j 3 := by
  fin_cases j
  closeCalculatedAORow 3 reported

theorem cachedAORow4 (j : Jet) : calculatedAO j 4 = groupCachedOrbital cachedExp cachedPoly 4 j := by
  fin_cases j
  closeCalculatedAORow 4 computed

theorem reportedAORow4 (j : Jet) : calculatedAO j 4 = reportedAO j 4 := by
  fin_cases j
  closeCalculatedAORow 4 reported

theorem cachedAORow5 (j : Jet) : calculatedAO j 5 = groupCachedOrbital cachedExp cachedPoly 5 j := by
  fin_cases j
  closeCalculatedAORow 5 computed

theorem reportedAORow5 (j : Jet) : calculatedAO j 5 = reportedAO j 5 := by
  fin_cases j
  closeCalculatedAORow 5 reported

theorem cachedAORow6 (j : Jet) : calculatedAO j 6 = groupCachedOrbital cachedExp cachedPoly 6 j := by
  fin_cases j
  closeCalculatedAORow 6 computed

theorem reportedAORow6 (j : Jet) : calculatedAO j 6 = reportedAO j 6 := by
  fin_cases j
  closeCalculatedAORow 6 reported

theorem cachedAORow7 (j : Jet) : calculatedAO j 7 = groupCachedOrbital cachedExp cachedPoly 7 j := by
  fin_cases j
  closeCalculatedAORow 7 computed

theorem reportedAORow7 (j : Jet) : calculatedAO j 7 = reportedAO j 7 := by
  fin_cases j
  closeCalculatedAORow 7 reported

theorem cachedAORow8 (j : Jet) : calculatedAO j 8 = groupCachedOrbital cachedExp cachedPoly 8 j := by
  fin_cases j
  closeCalculatedAORow 8 computed

theorem reportedAORow8 (j : Jet) : calculatedAO j 8 = reportedAO j 8 := by
  fin_cases j
  closeCalculatedAORow 8 reported

theorem cachedAORow9 (j : Jet) : calculatedAO j 9 = groupCachedOrbital cachedExp cachedPoly 9 j := by
  fin_cases j
  closeCalculatedAORow 9 computed

theorem reportedAORow9 (j : Jet) : calculatedAO j 9 = reportedAO j 9 := by
  fin_cases j
  closeCalculatedAORow 9 reported

theorem cachedAORow10 (j : Jet) : calculatedAO j 10 = groupCachedOrbital cachedExp cachedPoly 10 j := by
  fin_cases j
  closeCalculatedAORow 10 computed

theorem reportedAORow10 (j : Jet) : calculatedAO j 10 = reportedAO j 10 := by
  fin_cases j
  closeCalculatedAORow 10 reported

theorem cachedAORow11 (j : Jet) : calculatedAO j 11 = groupCachedOrbital cachedExp cachedPoly 11 j := by
  fin_cases j
  closeCalculatedAORow 11 computed

theorem reportedAORow11 (j : Jet) : calculatedAO j 11 = reportedAO j 11 := by
  fin_cases j
  closeCalculatedAORow 11 reported

theorem cachedAORow12 (j : Jet) : calculatedAO j 12 = groupCachedOrbital cachedExp cachedPoly 12 j := by
  fin_cases j
  closeCalculatedAORow 12 computed

theorem reportedAORow12 (j : Jet) : calculatedAO j 12 = reportedAO j 12 := by
  fin_cases j
  closeCalculatedAORow 12 reported

theorem cachedAORow13 (j : Jet) : calculatedAO j 13 = groupCachedOrbital cachedExp cachedPoly 13 j := by
  fin_cases j
  closeCalculatedAORow 13 computed

theorem reportedAORow13 (j : Jet) : calculatedAO j 13 = reportedAO j 13 := by
  fin_cases j
  closeCalculatedAORow 13 reported

theorem cachedAORow14 (j : Jet) : calculatedAO j 14 = groupCachedOrbital cachedExp cachedPoly 14 j := by
  fin_cases j
  closeCalculatedAORow 14 computed

theorem reportedAORow14 (j : Jet) : calculatedAO j 14 = reportedAO j 14 := by
  fin_cases j
  closeCalculatedAORow 14 reported

theorem cachedAORow15 (j : Jet) : calculatedAO j 15 = groupCachedOrbital cachedExp cachedPoly 15 j := by
  fin_cases j
  closeCalculatedAORow 15 computed

theorem reportedAORow15 (j : Jet) : calculatedAO j 15 = reportedAO j 15 := by
  fin_cases j
  closeCalculatedAORow 15 reported

theorem cachedAORow16 (j : Jet) : calculatedAO j 16 = groupCachedOrbital cachedExp cachedPoly 16 j := by
  fin_cases j
  closeCalculatedAORow 16 computed

theorem reportedAORow16 (j : Jet) : calculatedAO j 16 = reportedAO j 16 := by
  fin_cases j
  closeCalculatedAORow 16 reported

theorem cachedAORow17 (j : Jet) : calculatedAO j 17 = groupCachedOrbital cachedExp cachedPoly 17 j := by
  fin_cases j
  closeCalculatedAORow 17 computed

theorem reportedAORow17 (j : Jet) : calculatedAO j 17 = reportedAO j 17 := by
  fin_cases j
  closeCalculatedAORow 17 reported

theorem cachedAORow18 (j : Jet) : calculatedAO j 18 = groupCachedOrbital cachedExp cachedPoly 18 j := by
  fin_cases j
  closeCalculatedAORow 18 computed

theorem reportedAORow18 (j : Jet) : calculatedAO j 18 = reportedAO j 18 := by
  fin_cases j
  closeCalculatedAORow 18 reported

theorem cachedAORow19 (j : Jet) : calculatedAO j 19 = groupCachedOrbital cachedExp cachedPoly 19 j := by
  fin_cases j
  closeCalculatedAORow 19 computed

theorem reportedAORow19 (j : Jet) : calculatedAO j 19 = reportedAO j 19 := by
  fin_cases j
  closeCalculatedAORow 19 reported

theorem cachedAORow20 (j : Jet) : calculatedAO j 20 = groupCachedOrbital cachedExp cachedPoly 20 j := by
  fin_cases j
  closeCalculatedAORow 20 computed

theorem reportedAORow20 (j : Jet) : calculatedAO j 20 = reportedAO j 20 := by
  fin_cases j
  closeCalculatedAORow 20 reported

theorem cachedAORow21 (j : Jet) : calculatedAO j 21 = groupCachedOrbital cachedExp cachedPoly 21 j := by
  fin_cases j
  closeCalculatedAORow 21 computed

theorem reportedAORow21 (j : Jet) : calculatedAO j 21 = reportedAO j 21 := by
  fin_cases j
  closeCalculatedAORow 21 reported

theorem cachedAORow22 (j : Jet) : calculatedAO j 22 = groupCachedOrbital cachedExp cachedPoly 22 j := by
  fin_cases j
  closeCalculatedAORow 22 computed

theorem reportedAORow22 (j : Jet) : calculatedAO j 22 = reportedAO j 22 := by
  fin_cases j
  closeCalculatedAORow 22 reported

theorem cachedAORow23 (j : Jet) : calculatedAO j 23 = groupCachedOrbital cachedExp cachedPoly 23 j := by
  fin_cases j
  closeCalculatedAORow 23 computed

theorem reportedAORow23 (j : Jet) : calculatedAO j 23 = reportedAO j 23 := by
  fin_cases j
  closeCalculatedAORow 23 reported

theorem cachedAORow24 (j : Jet) : calculatedAO j 24 = groupCachedOrbital cachedExp cachedPoly 24 j := by
  fin_cases j
  closeCalculatedAORow 24 computed

theorem reportedAORow24 (j : Jet) : calculatedAO j 24 = reportedAO j 24 := by
  fin_cases j
  closeCalculatedAORow 24 reported

theorem cachedAORow25 (j : Jet) : calculatedAO j 25 = groupCachedOrbital cachedExp cachedPoly 25 j := by
  fin_cases j
  closeCalculatedAORow 25 computed

theorem reportedAORow25 (j : Jet) : calculatedAO j 25 = reportedAO j 25 := by
  fin_cases j
  closeCalculatedAORow 25 reported

theorem cachedAORow26 (j : Jet) : calculatedAO j 26 = groupCachedOrbital cachedExp cachedPoly 26 j := by
  fin_cases j
  closeCalculatedAORow 26 computed

theorem reportedAORow26 (j : Jet) : calculatedAO j 26 = reportedAO j 26 := by
  fin_cases j
  closeCalculatedAORow 26 reported

theorem cachedAORow27 (j : Jet) : calculatedAO j 27 = groupCachedOrbital cachedExp cachedPoly 27 j := by
  fin_cases j
  closeCalculatedAORow 27 computed

theorem reportedAORow27 (j : Jet) : calculatedAO j 27 = reportedAO j 27 := by
  fin_cases j
  closeCalculatedAORow 27 reported

theorem cachedAORow28 (j : Jet) : calculatedAO j 28 = groupCachedOrbital cachedExp cachedPoly 28 j := by
  fin_cases j
  closeCalculatedAORow 28 computed

theorem reportedAORow28 (j : Jet) : calculatedAO j 28 = reportedAO j 28 := by
  fin_cases j
  closeCalculatedAORow 28 reported

theorem cachedAORow29 (j : Jet) : calculatedAO j 29 = groupCachedOrbital cachedExp cachedPoly 29 j := by
  fin_cases j
  closeCalculatedAORow 29 computed

theorem reportedAORow29 (j : Jet) : calculatedAO j 29 = reportedAO j 29 := by
  fin_cases j
  closeCalculatedAORow 29 reported

theorem cachedAORow30 (j : Jet) : calculatedAO j 30 = groupCachedOrbital cachedExp cachedPoly 30 j := by
  fin_cases j
  closeCalculatedAORow 30 computed

theorem reportedAORow30 (j : Jet) : calculatedAO j 30 = reportedAO j 30 := by
  fin_cases j
  closeCalculatedAORow 30 reported

theorem cachedAORow31 (j : Jet) : calculatedAO j 31 = groupCachedOrbital cachedExp cachedPoly 31 j := by
  fin_cases j
  closeCalculatedAORow 31 computed

theorem reportedAORow31 (j : Jet) : calculatedAO j 31 = reportedAO j 31 := by
  fin_cases j
  closeCalculatedAORow 31 reported

theorem cachedAORow32 (j : Jet) : calculatedAO j 32 = groupCachedOrbital cachedExp cachedPoly 32 j := by
  fin_cases j
  closeCalculatedAORow 32 computed

theorem reportedAORow32 (j : Jet) : calculatedAO j 32 = reportedAO j 32 := by
  fin_cases j
  closeCalculatedAORow 32 reported

theorem cachedAORow33 (j : Jet) : calculatedAO j 33 = groupCachedOrbital cachedExp cachedPoly 33 j := by
  fin_cases j
  closeCalculatedAORow 33 computed

theorem reportedAORow33 (j : Jet) : calculatedAO j 33 = reportedAO j 33 := by
  fin_cases j
  closeCalculatedAORow 33 reported

theorem cachedAORow34 (j : Jet) : calculatedAO j 34 = groupCachedOrbital cachedExp cachedPoly 34 j := by
  fin_cases j
  closeCalculatedAORow 34 computed

theorem reportedAORow34 (j : Jet) : calculatedAO j 34 = reportedAO j 34 := by
  fin_cases j
  closeCalculatedAORow 34 reported

theorem cachedAORow35 (j : Jet) : calculatedAO j 35 = groupCachedOrbital cachedExp cachedPoly 35 j := by
  fin_cases j
  closeCalculatedAORow 35 computed

theorem reportedAORow35 (j : Jet) : calculatedAO j 35 = reportedAO j 35 := by
  fin_cases j
  closeCalculatedAORow 35 reported

theorem cachedAORow36 (j : Jet) : calculatedAO j 36 = groupCachedOrbital cachedExp cachedPoly 36 j := by
  fin_cases j
  closeCalculatedAORow 36 computed

theorem reportedAORow36 (j : Jet) : calculatedAO j 36 = reportedAO j 36 := by
  fin_cases j
  closeCalculatedAORow 36 reported

theorem cachedAORow37 (j : Jet) : calculatedAO j 37 = groupCachedOrbital cachedExp cachedPoly 37 j := by
  fin_cases j
  closeCalculatedAORow 37 computed

theorem reportedAORow37 (j : Jet) : calculatedAO j 37 = reportedAO j 37 := by
  fin_cases j
  closeCalculatedAORow 37 reported

theorem cachedAORow38 (j : Jet) : calculatedAO j 38 = groupCachedOrbital cachedExp cachedPoly 38 j := by
  fin_cases j
  closeCalculatedAORow 38 computed

theorem reportedAORow38 (j : Jet) : calculatedAO j 38 = reportedAO j 38 := by
  fin_cases j
  closeCalculatedAORow 38 reported

theorem cachedAORow39 (j : Jet) : calculatedAO j 39 = groupCachedOrbital cachedExp cachedPoly 39 j := by
  fin_cases j
  closeCalculatedAORow 39 computed

theorem reportedAORow39 (j : Jet) : calculatedAO j 39 = reportedAO j 39 := by
  fin_cases j
  closeCalculatedAORow 39 reported

theorem cachedAORow40 (j : Jet) : calculatedAO j 40 = groupCachedOrbital cachedExp cachedPoly 40 j := by
  fin_cases j
  closeCalculatedAORow 40 computed

theorem reportedAORow40 (j : Jet) : calculatedAO j 40 = reportedAO j 40 := by
  fin_cases j
  closeCalculatedAORow 40 reported

theorem cachedAORow41 (j : Jet) : calculatedAO j 41 = groupCachedOrbital cachedExp cachedPoly 41 j := by
  fin_cases j
  closeCalculatedAORow 41 computed

theorem reportedAORow41 (j : Jet) : calculatedAO j 41 = reportedAO j 41 := by
  fin_cases j
  closeCalculatedAORow 41 reported

theorem cachedAORow42 (j : Jet) : calculatedAO j 42 = groupCachedOrbital cachedExp cachedPoly 42 j := by
  fin_cases j
  closeCalculatedAORow 42 computed

theorem reportedAORow42 (j : Jet) : calculatedAO j 42 = reportedAO j 42 := by
  fin_cases j
  closeCalculatedAORow 42 reported

theorem cachedAORow43 (j : Jet) : calculatedAO j 43 = groupCachedOrbital cachedExp cachedPoly 43 j := by
  fin_cases j
  closeCalculatedAORow 43 computed

theorem reportedAORow43 (j : Jet) : calculatedAO j 43 = reportedAO j 43 := by
  fin_cases j
  closeCalculatedAORow 43 reported

theorem cachedAORow44 (j : Jet) : calculatedAO j 44 = groupCachedOrbital cachedExp cachedPoly 44 j := by
  fin_cases j
  closeCalculatedAORow 44 computed

theorem reportedAORow44 (j : Jet) : calculatedAO j 44 = reportedAO j 44 := by
  fin_cases j
  closeCalculatedAORow 44 reported

theorem cachedAORow45 (j : Jet) : calculatedAO j 45 = groupCachedOrbital cachedExp cachedPoly 45 j := by
  fin_cases j
  closeCalculatedAORow 45 computed

theorem reportedAORow45 (j : Jet) : calculatedAO j 45 = reportedAO j 45 := by
  fin_cases j
  closeCalculatedAORow 45 reported

theorem cachedAORow46 (j : Jet) : calculatedAO j 46 = groupCachedOrbital cachedExp cachedPoly 46 j := by
  fin_cases j
  closeCalculatedAORow 46 computed

theorem reportedAORow46 (j : Jet) : calculatedAO j 46 = reportedAO j 46 := by
  fin_cases j
  closeCalculatedAORow 46 reported

theorem cachedAORow47 (j : Jet) : calculatedAO j 47 = groupCachedOrbital cachedExp cachedPoly 47 j := by
  fin_cases j
  closeCalculatedAORow 47 computed

theorem reportedAORow47 (j : Jet) : calculatedAO j 47 = reportedAO j 47 := by
  fin_cases j
  closeCalculatedAORow 47 reported

theorem cachedAORow48 (j : Jet) : calculatedAO j 48 = groupCachedOrbital cachedExp cachedPoly 48 j := by
  fin_cases j
  closeCalculatedAORow 48 computed

theorem reportedAORow48 (j : Jet) : calculatedAO j 48 = reportedAO j 48 := by
  fin_cases j
  closeCalculatedAORow 48 reported

theorem cachedAORow49 (j : Jet) : calculatedAO j 49 = groupCachedOrbital cachedExp cachedPoly 49 j := by
  fin_cases j
  closeCalculatedAORow 49 computed

theorem reportedAORow49 (j : Jet) : calculatedAO j 49 = reportedAO j 49 := by
  fin_cases j
  closeCalculatedAORow 49 reported

theorem cachedAORow50 (j : Jet) : calculatedAO j 50 = groupCachedOrbital cachedExp cachedPoly 50 j := by
  fin_cases j
  closeCalculatedAORow 50 computed

theorem reportedAORow50 (j : Jet) : calculatedAO j 50 = reportedAO j 50 := by
  fin_cases j
  closeCalculatedAORow 50 reported

theorem cachedAORow51 (j : Jet) : calculatedAO j 51 = groupCachedOrbital cachedExp cachedPoly 51 j := by
  fin_cases j
  closeCalculatedAORow 51 computed

theorem reportedAORow51 (j : Jet) : calculatedAO j 51 = reportedAO j 51 := by
  fin_cases j
  closeCalculatedAORow 51 reported

theorem cachedAORow52 (j : Jet) : calculatedAO j 52 = groupCachedOrbital cachedExp cachedPoly 52 j := by
  fin_cases j
  closeCalculatedAORow 52 computed

theorem reportedAORow52 (j : Jet) : calculatedAO j 52 = reportedAO j 52 := by
  fin_cases j
  closeCalculatedAORow 52 reported

theorem cachedAORow53 (j : Jet) : calculatedAO j 53 = groupCachedOrbital cachedExp cachedPoly 53 j := by
  fin_cases j
  closeCalculatedAORow 53 computed

theorem reportedAORow53 (j : Jet) : calculatedAO j 53 = reportedAO j 53 := by
  fin_cases j
  closeCalculatedAORow 53 reported

theorem cachedAORow54 (j : Jet) : calculatedAO j 54 = groupCachedOrbital cachedExp cachedPoly 54 j := by
  fin_cases j
  closeCalculatedAORow 54 computed

theorem reportedAORow54 (j : Jet) : calculatedAO j 54 = reportedAO j 54 := by
  fin_cases j
  closeCalculatedAORow 54 reported

theorem cachedAORow55 (j : Jet) : calculatedAO j 55 = groupCachedOrbital cachedExp cachedPoly 55 j := by
  fin_cases j
  closeCalculatedAORow 55 computed

theorem reportedAORow55 (j : Jet) : calculatedAO j 55 = reportedAO j 55 := by
  fin_cases j
  closeCalculatedAORow 55 reported

theorem cachedAORow56 (j : Jet) : calculatedAO j 56 = groupCachedOrbital cachedExp cachedPoly 56 j := by
  fin_cases j
  closeCalculatedAORow 56 computed

theorem reportedAORow56 (j : Jet) : calculatedAO j 56 = reportedAO j 56 := by
  fin_cases j
  closeCalculatedAORow 56 reported

theorem cachedAORow57 (j : Jet) : calculatedAO j 57 = groupCachedOrbital cachedExp cachedPoly 57 j := by
  fin_cases j
  closeCalculatedAORow 57 computed

theorem reportedAORow57 (j : Jet) : calculatedAO j 57 = reportedAO j 57 := by
  fin_cases j
  closeCalculatedAORow 57 reported

theorem cachedAORow58 (j : Jet) : calculatedAO j 58 = groupCachedOrbital cachedExp cachedPoly 58 j := by
  fin_cases j
  closeCalculatedAORow 58 computed

theorem reportedAORow58 (j : Jet) : calculatedAO j 58 = reportedAO j 58 := by
  fin_cases j
  closeCalculatedAORow 58 reported

theorem cachedAORow59 (j : Jet) : calculatedAO j 59 = groupCachedOrbital cachedExp cachedPoly 59 j := by
  fin_cases j
  closeCalculatedAORow 59 computed

theorem reportedAORow59 (j : Jet) : calculatedAO j 59 = reportedAO j 59 := by
  fin_cases j
  closeCalculatedAORow 59 reported

theorem cachedAORow60 (j : Jet) : calculatedAO j 60 = groupCachedOrbital cachedExp cachedPoly 60 j := by
  fin_cases j
  closeCalculatedAORow 60 computed

theorem reportedAORow60 (j : Jet) : calculatedAO j 60 = reportedAO j 60 := by
  fin_cases j
  closeCalculatedAORow 60 reported

theorem cachedAORow61 (j : Jet) : calculatedAO j 61 = groupCachedOrbital cachedExp cachedPoly 61 j := by
  fin_cases j
  closeCalculatedAORow 61 computed

theorem reportedAORow61 (j : Jet) : calculatedAO j 61 = reportedAO j 61 := by
  fin_cases j
  closeCalculatedAORow 61 reported

theorem cachedAORow62 (j : Jet) : calculatedAO j 62 = groupCachedOrbital cachedExp cachedPoly 62 j := by
  fin_cases j
  closeCalculatedAORow 62 computed

theorem reportedAORow62 (j : Jet) : calculatedAO j 62 = reportedAO j 62 := by
  fin_cases j
  closeCalculatedAORow 62 reported

theorem cachedAORow63 (j : Jet) : calculatedAO j 63 = groupCachedOrbital cachedExp cachedPoly 63 j := by
  fin_cases j
  closeCalculatedAORow 63 computed

theorem reportedAORow63 (j : Jet) : calculatedAO j 63 = reportedAO j 63 := by
  fin_cases j
  closeCalculatedAORow 63 reported

theorem cachedAORow64 (j : Jet) : calculatedAO j 64 = groupCachedOrbital cachedExp cachedPoly 64 j := by
  fin_cases j
  closeCalculatedAORow 64 computed

theorem reportedAORow64 (j : Jet) : calculatedAO j 64 = reportedAO j 64 := by
  fin_cases j
  closeCalculatedAORow 64 reported

theorem cachedAORow65 (j : Jet) : calculatedAO j 65 = groupCachedOrbital cachedExp cachedPoly 65 j := by
  fin_cases j
  closeCalculatedAORow 65 computed

theorem reportedAORow65 (j : Jet) : calculatedAO j 65 = reportedAO j 65 := by
  fin_cases j
  closeCalculatedAORow 65 reported

theorem cachedAORow66 (j : Jet) : calculatedAO j 66 = groupCachedOrbital cachedExp cachedPoly 66 j := by
  fin_cases j
  closeCalculatedAORow 66 computed

theorem reportedAORow66 (j : Jet) : calculatedAO j 66 = reportedAO j 66 := by
  fin_cases j
  closeCalculatedAORow 66 reported

theorem cachedAORow67 (j : Jet) : calculatedAO j 67 = groupCachedOrbital cachedExp cachedPoly 67 j := by
  fin_cases j
  closeCalculatedAORow 67 computed

theorem reportedAORow67 (j : Jet) : calculatedAO j 67 = reportedAO j 67 := by
  fin_cases j
  closeCalculatedAORow 67 reported

theorem cachedAORow68 (j : Jet) : calculatedAO j 68 = groupCachedOrbital cachedExp cachedPoly 68 j := by
  fin_cases j
  closeCalculatedAORow 68 computed

theorem reportedAORow68 (j : Jet) : calculatedAO j 68 = reportedAO j 68 := by
  fin_cases j
  closeCalculatedAORow 68 reported

theorem cachedAORow69 (j : Jet) : calculatedAO j 69 = groupCachedOrbital cachedExp cachedPoly 69 j := by
  fin_cases j
  closeCalculatedAORow 69 computed

theorem reportedAORow69 (j : Jet) : calculatedAO j 69 = reportedAO j 69 := by
  fin_cases j
  closeCalculatedAORow 69 reported

theorem cachedAORow70 (j : Jet) : calculatedAO j 70 = groupCachedOrbital cachedExp cachedPoly 70 j := by
  fin_cases j
  closeCalculatedAORow 70 computed

theorem reportedAORow70 (j : Jet) : calculatedAO j 70 = reportedAO j 70 := by
  fin_cases j
  closeCalculatedAORow 70 reported

theorem cachedAORow71 (j : Jet) : calculatedAO j 71 = groupCachedOrbital cachedExp cachedPoly 71 j := by
  fin_cases j
  closeCalculatedAORow 71 computed

theorem reportedAORow71 (j : Jet) : calculatedAO j 71 = reportedAO j 71 := by
  fin_cases j
  closeCalculatedAORow 71 reported

theorem cachedAORow72 (j : Jet) : calculatedAO j 72 = groupCachedOrbital cachedExp cachedPoly 72 j := by
  fin_cases j
  closeCalculatedAORow 72 computed

theorem reportedAORow72 (j : Jet) : calculatedAO j 72 = reportedAO j 72 := by
  fin_cases j
  closeCalculatedAORow 72 reported

theorem cachedAORow73 (j : Jet) : calculatedAO j 73 = groupCachedOrbital cachedExp cachedPoly 73 j := by
  fin_cases j
  closeCalculatedAORow 73 computed

theorem reportedAORow73 (j : Jet) : calculatedAO j 73 = reportedAO j 73 := by
  fin_cases j
  closeCalculatedAORow 73 reported

theorem cachedAORow74 (j : Jet) : calculatedAO j 74 = groupCachedOrbital cachedExp cachedPoly 74 j := by
  fin_cases j
  closeCalculatedAORow 74 computed

theorem reportedAORow74 (j : Jet) : calculatedAO j 74 = reportedAO j 74 := by
  fin_cases j
  closeCalculatedAORow 74 reported

theorem cachedAORow75 (j : Jet) : calculatedAO j 75 = groupCachedOrbital cachedExp cachedPoly 75 j := by
  fin_cases j
  closeCalculatedAORow 75 computed

theorem reportedAORow75 (j : Jet) : calculatedAO j 75 = reportedAO j 75 := by
  fin_cases j
  closeCalculatedAORow 75 reported

theorem cachedAORow76 (j : Jet) : calculatedAO j 76 = groupCachedOrbital cachedExp cachedPoly 76 j := by
  fin_cases j
  closeCalculatedAORow 76 computed

theorem reportedAORow76 (j : Jet) : calculatedAO j 76 = reportedAO j 76 := by
  fin_cases j
  closeCalculatedAORow 76 reported

theorem cachedAORow77 (j : Jet) : calculatedAO j 77 = groupCachedOrbital cachedExp cachedPoly 77 j := by
  fin_cases j
  closeCalculatedAORow 77 computed

theorem reportedAORow77 (j : Jet) : calculatedAO j 77 = reportedAO j 77 := by
  fin_cases j
  closeCalculatedAORow 77 reported

theorem cachedAORow78 (j : Jet) : calculatedAO j 78 = groupCachedOrbital cachedExp cachedPoly 78 j := by
  fin_cases j
  closeCalculatedAORow 78 computed

theorem reportedAORow78 (j : Jet) : calculatedAO j 78 = reportedAO j 78 := by
  fin_cases j
  closeCalculatedAORow 78 reported

theorem cachedAORow79 (j : Jet) : calculatedAO j 79 = groupCachedOrbital cachedExp cachedPoly 79 j := by
  fin_cases j
  closeCalculatedAORow 79 computed

theorem reportedAORow79 (j : Jet) : calculatedAO j 79 = reportedAO j 79 := by
  fin_cases j
  closeCalculatedAORow 79 reported

theorem cachedAORow80 (j : Jet) : calculatedAO j 80 = groupCachedOrbital cachedExp cachedPoly 80 j := by
  fin_cases j
  closeCalculatedAORow 80 computed

theorem reportedAORow80 (j : Jet) : calculatedAO j 80 = reportedAO j 80 := by
  fin_cases j
  closeCalculatedAORow 80 reported

theorem cachedAORow81 (j : Jet) : calculatedAO j 81 = groupCachedOrbital cachedExp cachedPoly 81 j := by
  fin_cases j
  closeCalculatedAORow 81 computed

theorem reportedAORow81 (j : Jet) : calculatedAO j 81 = reportedAO j 81 := by
  fin_cases j
  closeCalculatedAORow 81 reported

theorem cachedAORow82 (j : Jet) : calculatedAO j 82 = groupCachedOrbital cachedExp cachedPoly 82 j := by
  fin_cases j
  closeCalculatedAORow 82 computed

theorem reportedAORow82 (j : Jet) : calculatedAO j 82 = reportedAO j 82 := by
  fin_cases j
  closeCalculatedAORow 82 reported

theorem cachedAORow83 (j : Jet) : calculatedAO j 83 = groupCachedOrbital cachedExp cachedPoly 83 j := by
  fin_cases j
  closeCalculatedAORow 83 computed

theorem reportedAORow83 (j : Jet) : calculatedAO j 83 = reportedAO j 83 := by
  fin_cases j
  closeCalculatedAORow 83 reported

theorem cachedAORow84 (j : Jet) : calculatedAO j 84 = groupCachedOrbital cachedExp cachedPoly 84 j := by
  fin_cases j
  closeCalculatedAORow 84 computed

theorem reportedAORow84 (j : Jet) : calculatedAO j 84 = reportedAO j 84 := by
  fin_cases j
  closeCalculatedAORow 84 reported

theorem cachedAORow85 (j : Jet) : calculatedAO j 85 = groupCachedOrbital cachedExp cachedPoly 85 j := by
  fin_cases j
  closeCalculatedAORow 85 computed

theorem reportedAORow85 (j : Jet) : calculatedAO j 85 = reportedAO j 85 := by
  fin_cases j
  closeCalculatedAORow 85 reported

theorem cachedAORow86 (j : Jet) : calculatedAO j 86 = groupCachedOrbital cachedExp cachedPoly 86 j := by
  fin_cases j
  closeCalculatedAORow 86 computed

theorem reportedAORow86 (j : Jet) : calculatedAO j 86 = reportedAO j 86 := by
  fin_cases j
  closeCalculatedAORow 86 reported

theorem cachedAORow87 (j : Jet) : calculatedAO j 87 = groupCachedOrbital cachedExp cachedPoly 87 j := by
  fin_cases j
  closeCalculatedAORow 87 computed

theorem reportedAORow87 (j : Jet) : calculatedAO j 87 = reportedAO j 87 := by
  fin_cases j
  closeCalculatedAORow 87 reported

theorem cachedAORow88 (j : Jet) : calculatedAO j 88 = groupCachedOrbital cachedExp cachedPoly 88 j := by
  fin_cases j
  closeCalculatedAORow 88 computed

theorem reportedAORow88 (j : Jet) : calculatedAO j 88 = reportedAO j 88 := by
  fin_cases j
  closeCalculatedAORow 88 reported

theorem cachedAORow89 (j : Jet) : calculatedAO j 89 = groupCachedOrbital cachedExp cachedPoly 89 j := by
  fin_cases j
  closeCalculatedAORow 89 computed

theorem reportedAORow89 (j : Jet) : calculatedAO j 89 = reportedAO j 89 := by
  fin_cases j
  closeCalculatedAORow 89 reported

theorem cachedAORow90 (j : Jet) : calculatedAO j 90 = groupCachedOrbital cachedExp cachedPoly 90 j := by
  fin_cases j
  closeCalculatedAORow 90 computed

theorem reportedAORow90 (j : Jet) : calculatedAO j 90 = reportedAO j 90 := by
  fin_cases j
  closeCalculatedAORow 90 reported

theorem cachedAORow91 (j : Jet) : calculatedAO j 91 = groupCachedOrbital cachedExp cachedPoly 91 j := by
  fin_cases j
  closeCalculatedAORow 91 computed

theorem reportedAORow91 (j : Jet) : calculatedAO j 91 = reportedAO j 91 := by
  fin_cases j
  closeCalculatedAORow 91 reported

theorem cachedAORow92 (j : Jet) : calculatedAO j 92 = groupCachedOrbital cachedExp cachedPoly 92 j := by
  fin_cases j
  closeCalculatedAORow 92 computed

theorem reportedAORow92 (j : Jet) : calculatedAO j 92 = reportedAO j 92 := by
  fin_cases j
  closeCalculatedAORow 92 reported

theorem cachedAORow93 (j : Jet) : calculatedAO j 93 = groupCachedOrbital cachedExp cachedPoly 93 j := by
  fin_cases j
  closeCalculatedAORow 93 computed

theorem reportedAORow93 (j : Jet) : calculatedAO j 93 = reportedAO j 93 := by
  fin_cases j
  closeCalculatedAORow 93 reported

theorem cachedAORow94 (j : Jet) : calculatedAO j 94 = groupCachedOrbital cachedExp cachedPoly 94 j := by
  fin_cases j
  closeCalculatedAORow 94 computed

theorem reportedAORow94 (j : Jet) : calculatedAO j 94 = reportedAO j 94 := by
  fin_cases j
  closeCalculatedAORow 94 reported

theorem cachedAORow95 (j : Jet) : calculatedAO j 95 = groupCachedOrbital cachedExp cachedPoly 95 j := by
  fin_cases j
  closeCalculatedAORow 95 computed

theorem reportedAORow95 (j : Jet) : calculatedAO j 95 = reportedAO j 95 := by
  fin_cases j
  closeCalculatedAORow 95 reported

theorem cachedAORow96 (j : Jet) : calculatedAO j 96 = groupCachedOrbital cachedExp cachedPoly 96 j := by
  fin_cases j
  closeCalculatedAORow 96 computed

theorem reportedAORow96 (j : Jet) : calculatedAO j 96 = reportedAO j 96 := by
  fin_cases j
  closeCalculatedAORow 96 reported

theorem cachedAORow97 (j : Jet) : calculatedAO j 97 = groupCachedOrbital cachedExp cachedPoly 97 j := by
  fin_cases j
  closeCalculatedAORow 97 computed

theorem reportedAORow97 (j : Jet) : calculatedAO j 97 = reportedAO j 97 := by
  fin_cases j
  closeCalculatedAORow 97 reported

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks
