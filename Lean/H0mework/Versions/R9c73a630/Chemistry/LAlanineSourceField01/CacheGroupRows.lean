import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField01.CacheB0
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField01.CacheB1
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField01.CacheB2
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField01.CacheB3
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField01.CacheB4
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField01.CacheB5
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField01.CacheB6
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField01.CacheB7

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.Field1

open Lean Elab Tactic SourceRectangle SourceSignedEvaluator

elab "closeLowGroupRelative " group:num : tactic => do
  let goals ← getGoals
  unless goals.length == 3 do throwError "source axis census"
  let base := (← getCurrNamespace) ++ `Checks
  for (goal,a) in goals.zipIdx do
    goal.assign (Lean.mkConst (base ++ Name.mkSimple s!"relative_{group.getNat}_{a}"))
  setGoals []

elab "closeLowGroupPolynomial " group:num : tactic => do
  let goals ← getGoals
  unless goals.length == 27 do throwError "source low polynomial census"
  let base := (← getCurrNamespace) ++ `Checks
  for (goal,i) in goals.zipIdx do
    goal.assign (Lean.mkConst (base ++ Name.mkSimple s!"poly_{group.getNat}_{i/9}_{(i/3)%3}_{i%3}"))
  setGoals []

theorem relativeRow0 (axis : Fin 3) : cachedRelative 0 axis = sourceRelative 0 axis := by
  fin_cases axis
  closeLowGroupRelative 0

theorem polynomialRow0 (axis power order : Fin 3) :
    cachedPoly 0 axis power order = sourcePolyFromRelative 0 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 0

theorem relativeRow1 (axis : Fin 3) : cachedRelative 1 axis = sourceRelative 1 axis := by
  fin_cases axis
  closeLowGroupRelative 1

theorem polynomialRow1 (axis power order : Fin 3) :
    cachedPoly 1 axis power order = sourcePolyFromRelative 1 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 1

theorem relativeRow2 (axis : Fin 3) : cachedRelative 2 axis = sourceRelative 2 axis := by
  fin_cases axis
  closeLowGroupRelative 2

theorem polynomialRow2 (axis power order : Fin 3) :
    cachedPoly 2 axis power order = sourcePolyFromRelative 2 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 2

theorem relativeRow3 (axis : Fin 3) : cachedRelative 3 axis = sourceRelative 3 axis := by
  fin_cases axis
  closeLowGroupRelative 3

theorem polynomialRow3 (axis power order : Fin 3) :
    cachedPoly 3 axis power order = sourcePolyFromRelative 3 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 3

theorem relativeRow4 (axis : Fin 3) : cachedRelative 4 axis = sourceRelative 4 axis := by
  fin_cases axis
  closeLowGroupRelative 4

theorem polynomialRow4 (axis power order : Fin 3) :
    cachedPoly 4 axis power order = sourcePolyFromRelative 4 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 4

theorem relativeRow5 (axis : Fin 3) : cachedRelative 5 axis = sourceRelative 5 axis := by
  fin_cases axis
  closeLowGroupRelative 5

theorem polynomialRow5 (axis power order : Fin 3) :
    cachedPoly 5 axis power order = sourcePolyFromRelative 5 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 5

theorem relativeRow6 (axis : Fin 3) : cachedRelative 6 axis = sourceRelative 6 axis := by
  fin_cases axis
  closeLowGroupRelative 6

theorem polynomialRow6 (axis power order : Fin 3) :
    cachedPoly 6 axis power order = sourcePolyFromRelative 6 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 6

theorem relativeRow7 (axis : Fin 3) : cachedRelative 7 axis = sourceRelative 7 axis := by
  fin_cases axis
  closeLowGroupRelative 7

theorem polynomialRow7 (axis power order : Fin 3) :
    cachedPoly 7 axis power order = sourcePolyFromRelative 7 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 7

theorem relativeRow8 (axis : Fin 3) : cachedRelative 8 axis = sourceRelative 8 axis := by
  fin_cases axis
  closeLowGroupRelative 8

theorem polynomialRow8 (axis power order : Fin 3) :
    cachedPoly 8 axis power order = sourcePolyFromRelative 8 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 8

theorem relativeRow9 (axis : Fin 3) : cachedRelative 9 axis = sourceRelative 9 axis := by
  fin_cases axis
  closeLowGroupRelative 9

theorem polynomialRow9 (axis power order : Fin 3) :
    cachedPoly 9 axis power order = sourcePolyFromRelative 9 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 9

theorem relativeRow10 (axis : Fin 3) : cachedRelative 10 axis = sourceRelative 10 axis := by
  fin_cases axis
  closeLowGroupRelative 10

theorem polynomialRow10 (axis power order : Fin 3) :
    cachedPoly 10 axis power order = sourcePolyFromRelative 10 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 10

theorem relativeRow11 (axis : Fin 3) : cachedRelative 11 axis = sourceRelative 11 axis := by
  fin_cases axis
  closeLowGroupRelative 11

theorem polynomialRow11 (axis power order : Fin 3) :
    cachedPoly 11 axis power order = sourcePolyFromRelative 11 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 11

theorem relativeRow12 (axis : Fin 3) : cachedRelative 12 axis = sourceRelative 12 axis := by
  fin_cases axis
  closeLowGroupRelative 12

theorem polynomialRow12 (axis power order : Fin 3) :
    cachedPoly 12 axis power order = sourcePolyFromRelative 12 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 12

theorem relativeRow13 (axis : Fin 3) : cachedRelative 13 axis = sourceRelative 13 axis := by
  fin_cases axis
  closeLowGroupRelative 13

theorem polynomialRow13 (axis power order : Fin 3) :
    cachedPoly 13 axis power order = sourcePolyFromRelative 13 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 13

theorem relativeRow14 (axis : Fin 3) : cachedRelative 14 axis = sourceRelative 14 axis := by
  fin_cases axis
  closeLowGroupRelative 14

theorem polynomialRow14 (axis power order : Fin 3) :
    cachedPoly 14 axis power order = sourcePolyFromRelative 14 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 14

theorem relativeRow15 (axis : Fin 3) : cachedRelative 15 axis = sourceRelative 15 axis := by
  fin_cases axis
  closeLowGroupRelative 15

theorem polynomialRow15 (axis power order : Fin 3) :
    cachedPoly 15 axis power order = sourcePolyFromRelative 15 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 15

theorem relativeRow16 (axis : Fin 3) : cachedRelative 16 axis = sourceRelative 16 axis := by
  fin_cases axis
  closeLowGroupRelative 16

theorem polynomialRow16 (axis power order : Fin 3) :
    cachedPoly 16 axis power order = sourcePolyFromRelative 16 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 16

theorem relativeRow17 (axis : Fin 3) : cachedRelative 17 axis = sourceRelative 17 axis := by
  fin_cases axis
  closeLowGroupRelative 17

theorem polynomialRow17 (axis power order : Fin 3) :
    cachedPoly 17 axis power order = sourcePolyFromRelative 17 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 17

theorem relativeRow18 (axis : Fin 3) : cachedRelative 18 axis = sourceRelative 18 axis := by
  fin_cases axis
  closeLowGroupRelative 18

theorem polynomialRow18 (axis power order : Fin 3) :
    cachedPoly 18 axis power order = sourcePolyFromRelative 18 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 18

theorem relativeRow19 (axis : Fin 3) : cachedRelative 19 axis = sourceRelative 19 axis := by
  fin_cases axis
  closeLowGroupRelative 19

theorem polynomialRow19 (axis power order : Fin 3) :
    cachedPoly 19 axis power order = sourcePolyFromRelative 19 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 19

theorem relativeRow20 (axis : Fin 3) : cachedRelative 20 axis = sourceRelative 20 axis := by
  fin_cases axis
  closeLowGroupRelative 20

theorem polynomialRow20 (axis power order : Fin 3) :
    cachedPoly 20 axis power order = sourcePolyFromRelative 20 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 20

theorem relativeRow21 (axis : Fin 3) : cachedRelative 21 axis = sourceRelative 21 axis := by
  fin_cases axis
  closeLowGroupRelative 21

theorem polynomialRow21 (axis power order : Fin 3) :
    cachedPoly 21 axis power order = sourcePolyFromRelative 21 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 21

theorem relativeRow22 (axis : Fin 3) : cachedRelative 22 axis = sourceRelative 22 axis := by
  fin_cases axis
  closeLowGroupRelative 22

theorem polynomialRow22 (axis power order : Fin 3) :
    cachedPoly 22 axis power order = sourcePolyFromRelative 22 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 22

theorem relativeRow23 (axis : Fin 3) : cachedRelative 23 axis = sourceRelative 23 axis := by
  fin_cases axis
  closeLowGroupRelative 23

theorem polynomialRow23 (axis power order : Fin 3) :
    cachedPoly 23 axis power order = sourcePolyFromRelative 23 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 23

theorem relativeRow24 (axis : Fin 3) : cachedRelative 24 axis = sourceRelative 24 axis := by
  fin_cases axis
  closeLowGroupRelative 24

theorem polynomialRow24 (axis power order : Fin 3) :
    cachedPoly 24 axis power order = sourcePolyFromRelative 24 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 24

theorem relativeRow25 (axis : Fin 3) : cachedRelative 25 axis = sourceRelative 25 axis := by
  fin_cases axis
  closeLowGroupRelative 25

theorem polynomialRow25 (axis power order : Fin 3) :
    cachedPoly 25 axis power order = sourcePolyFromRelative 25 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 25

theorem relativeRow26 (axis : Fin 3) : cachedRelative 26 axis = sourceRelative 26 axis := by
  fin_cases axis
  closeLowGroupRelative 26

theorem polynomialRow26 (axis power order : Fin 3) :
    cachedPoly 26 axis power order = sourcePolyFromRelative 26 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 26

theorem relativeRow27 (axis : Fin 3) : cachedRelative 27 axis = sourceRelative 27 axis := by
  fin_cases axis
  closeLowGroupRelative 27

theorem polynomialRow27 (axis power order : Fin 3) :
    cachedPoly 27 axis power order = sourcePolyFromRelative 27 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 27

theorem relativeRow28 (axis : Fin 3) : cachedRelative 28 axis = sourceRelative 28 axis := by
  fin_cases axis
  closeLowGroupRelative 28

theorem polynomialRow28 (axis power order : Fin 3) :
    cachedPoly 28 axis power order = sourcePolyFromRelative 28 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 28

theorem relativeRow29 (axis : Fin 3) : cachedRelative 29 axis = sourceRelative 29 axis := by
  fin_cases axis
  closeLowGroupRelative 29

theorem polynomialRow29 (axis power order : Fin 3) :
    cachedPoly 29 axis power order = sourcePolyFromRelative 29 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 29

theorem relativeRow30 (axis : Fin 3) : cachedRelative 30 axis = sourceRelative 30 axis := by
  fin_cases axis
  closeLowGroupRelative 30

theorem polynomialRow30 (axis power order : Fin 3) :
    cachedPoly 30 axis power order = sourcePolyFromRelative 30 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 30

theorem relativeRow31 (axis : Fin 3) : cachedRelative 31 axis = sourceRelative 31 axis := by
  fin_cases axis
  closeLowGroupRelative 31

theorem polynomialRow31 (axis power order : Fin 3) :
    cachedPoly 31 axis power order = sourcePolyFromRelative 31 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 31

theorem relativeRow32 (axis : Fin 3) : cachedRelative 32 axis = sourceRelative 32 axis := by
  fin_cases axis
  closeLowGroupRelative 32

theorem polynomialRow32 (axis power order : Fin 3) :
    cachedPoly 32 axis power order = sourcePolyFromRelative 32 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 32

theorem relativeRow33 (axis : Fin 3) : cachedRelative 33 axis = sourceRelative 33 axis := by
  fin_cases axis
  closeLowGroupRelative 33

theorem polynomialRow33 (axis power order : Fin 3) :
    cachedPoly 33 axis power order = sourcePolyFromRelative 33 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 33

theorem relativeRow34 (axis : Fin 3) : cachedRelative 34 axis = sourceRelative 34 axis := by
  fin_cases axis
  closeLowGroupRelative 34

theorem polynomialRow34 (axis power order : Fin 3) :
    cachedPoly 34 axis power order = sourcePolyFromRelative 34 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 34

theorem relativeRow35 (axis : Fin 3) : cachedRelative 35 axis = sourceRelative 35 axis := by
  fin_cases axis
  closeLowGroupRelative 35

theorem polynomialRow35 (axis power order : Fin 3) :
    cachedPoly 35 axis power order = sourcePolyFromRelative 35 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 35

theorem relativeRow36 (axis : Fin 3) : cachedRelative 36 axis = sourceRelative 36 axis := by
  fin_cases axis
  closeLowGroupRelative 36

theorem polynomialRow36 (axis power order : Fin 3) :
    cachedPoly 36 axis power order = sourcePolyFromRelative 36 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 36

theorem relativeRow37 (axis : Fin 3) : cachedRelative 37 axis = sourceRelative 37 axis := by
  fin_cases axis
  closeLowGroupRelative 37

theorem polynomialRow37 (axis power order : Fin 3) :
    cachedPoly 37 axis power order = sourcePolyFromRelative 37 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 37

theorem relativeRow38 (axis : Fin 3) : cachedRelative 38 axis = sourceRelative 38 axis := by
  fin_cases axis
  closeLowGroupRelative 38

theorem polynomialRow38 (axis power order : Fin 3) :
    cachedPoly 38 axis power order = sourcePolyFromRelative 38 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 38

theorem relativeRow39 (axis : Fin 3) : cachedRelative 39 axis = sourceRelative 39 axis := by
  fin_cases axis
  closeLowGroupRelative 39

theorem polynomialRow39 (axis power order : Fin 3) :
    cachedPoly 39 axis power order = sourcePolyFromRelative 39 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 39

theorem relativeRow40 (axis : Fin 3) : cachedRelative 40 axis = sourceRelative 40 axis := by
  fin_cases axis
  closeLowGroupRelative 40

theorem polynomialRow40 (axis power order : Fin 3) :
    cachedPoly 40 axis power order = sourcePolyFromRelative 40 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 40

theorem relativeRow41 (axis : Fin 3) : cachedRelative 41 axis = sourceRelative 41 axis := by
  fin_cases axis
  closeLowGroupRelative 41

theorem polynomialRow41 (axis power order : Fin 3) :
    cachedPoly 41 axis power order = sourcePolyFromRelative 41 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 41

theorem relativeRow42 (axis : Fin 3) : cachedRelative 42 axis = sourceRelative 42 axis := by
  fin_cases axis
  closeLowGroupRelative 42

theorem polynomialRow42 (axis power order : Fin 3) :
    cachedPoly 42 axis power order = sourcePolyFromRelative 42 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 42

theorem relativeRow43 (axis : Fin 3) : cachedRelative 43 axis = sourceRelative 43 axis := by
  fin_cases axis
  closeLowGroupRelative 43

theorem polynomialRow43 (axis power order : Fin 3) :
    cachedPoly 43 axis power order = sourcePolyFromRelative 43 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 43

theorem relativeRow44 (axis : Fin 3) : cachedRelative 44 axis = sourceRelative 44 axis := by
  fin_cases axis
  closeLowGroupRelative 44

theorem polynomialRow44 (axis power order : Fin 3) :
    cachedPoly 44 axis power order = sourcePolyFromRelative 44 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 44

theorem relativeRow45 (axis : Fin 3) : cachedRelative 45 axis = sourceRelative 45 axis := by
  fin_cases axis
  closeLowGroupRelative 45

theorem polynomialRow45 (axis power order : Fin 3) :
    cachedPoly 45 axis power order = sourcePolyFromRelative 45 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 45

theorem relativeRow46 (axis : Fin 3) : cachedRelative 46 axis = sourceRelative 46 axis := by
  fin_cases axis
  closeLowGroupRelative 46

theorem polynomialRow46 (axis power order : Fin 3) :
    cachedPoly 46 axis power order = sourcePolyFromRelative 46 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 46

theorem relativeRow47 (axis : Fin 3) : cachedRelative 47 axis = sourceRelative 47 axis := by
  fin_cases axis
  closeLowGroupRelative 47

theorem polynomialRow47 (axis power order : Fin 3) :
    cachedPoly 47 axis power order = sourcePolyFromRelative 47 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 47

theorem relativeRow48 (axis : Fin 3) : cachedRelative 48 axis = sourceRelative 48 axis := by
  fin_cases axis
  closeLowGroupRelative 48

theorem polynomialRow48 (axis power order : Fin 3) :
    cachedPoly 48 axis power order = sourcePolyFromRelative 48 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 48

theorem relativeRow49 (axis : Fin 3) : cachedRelative 49 axis = sourceRelative 49 axis := by
  fin_cases axis
  closeLowGroupRelative 49

theorem polynomialRow49 (axis power order : Fin 3) :
    cachedPoly 49 axis power order = sourcePolyFromRelative 49 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 49

theorem relativeRow50 (axis : Fin 3) : cachedRelative 50 axis = sourceRelative 50 axis := by
  fin_cases axis
  closeLowGroupRelative 50

theorem polynomialRow50 (axis power order : Fin 3) :
    cachedPoly 50 axis power order = sourcePolyFromRelative 50 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 50

theorem relativeRow51 (axis : Fin 3) : cachedRelative 51 axis = sourceRelative 51 axis := by
  fin_cases axis
  closeLowGroupRelative 51

theorem polynomialRow51 (axis power order : Fin 3) :
    cachedPoly 51 axis power order = sourcePolyFromRelative 51 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 51

theorem relativeRow52 (axis : Fin 3) : cachedRelative 52 axis = sourceRelative 52 axis := by
  fin_cases axis
  closeLowGroupRelative 52

theorem polynomialRow52 (axis power order : Fin 3) :
    cachedPoly 52 axis power order = sourcePolyFromRelative 52 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 52

theorem relativeRow53 (axis : Fin 3) : cachedRelative 53 axis = sourceRelative 53 axis := by
  fin_cases axis
  closeLowGroupRelative 53

theorem polynomialRow53 (axis power order : Fin 3) :
    cachedPoly 53 axis power order = sourcePolyFromRelative 53 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 53

theorem relativeRow54 (axis : Fin 3) : cachedRelative 54 axis = sourceRelative 54 axis := by
  fin_cases axis
  closeLowGroupRelative 54

theorem polynomialRow54 (axis power order : Fin 3) :
    cachedPoly 54 axis power order = sourcePolyFromRelative 54 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 54

theorem relativeRow55 (axis : Fin 3) : cachedRelative 55 axis = sourceRelative 55 axis := by
  fin_cases axis
  closeLowGroupRelative 55

theorem polynomialRow55 (axis power order : Fin 3) :
    cachedPoly 55 axis power order = sourcePolyFromRelative 55 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 55

theorem relativeRow56 (axis : Fin 3) : cachedRelative 56 axis = sourceRelative 56 axis := by
  fin_cases axis
  closeLowGroupRelative 56

theorem polynomialRow56 (axis power order : Fin 3) :
    cachedPoly 56 axis power order = sourcePolyFromRelative 56 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 56

theorem relativeRow57 (axis : Fin 3) : cachedRelative 57 axis = sourceRelative 57 axis := by
  fin_cases axis
  closeLowGroupRelative 57

theorem polynomialRow57 (axis power order : Fin 3) :
    cachedPoly 57 axis power order = sourcePolyFromRelative 57 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 57

theorem relativeRow58 (axis : Fin 3) : cachedRelative 58 axis = sourceRelative 58 axis := by
  fin_cases axis
  closeLowGroupRelative 58

theorem polynomialRow58 (axis power order : Fin 3) :
    cachedPoly 58 axis power order = sourcePolyFromRelative 58 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 58

theorem relativeRow59 (axis : Fin 3) : cachedRelative 59 axis = sourceRelative 59 axis := by
  fin_cases axis
  closeLowGroupRelative 59

theorem polynomialRow59 (axis power order : Fin 3) :
    cachedPoly 59 axis power order = sourcePolyFromRelative 59 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 59

theorem relativeRow60 (axis : Fin 3) : cachedRelative 60 axis = sourceRelative 60 axis := by
  fin_cases axis
  closeLowGroupRelative 60

theorem polynomialRow60 (axis power order : Fin 3) :
    cachedPoly 60 axis power order = sourcePolyFromRelative 60 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 60

theorem relativeRow61 (axis : Fin 3) : cachedRelative 61 axis = sourceRelative 61 axis := by
  fin_cases axis
  closeLowGroupRelative 61

theorem polynomialRow61 (axis power order : Fin 3) :
    cachedPoly 61 axis power order = sourcePolyFromRelative 61 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 61

theorem relativeRow62 (axis : Fin 3) : cachedRelative 62 axis = sourceRelative 62 axis := by
  fin_cases axis
  closeLowGroupRelative 62

theorem polynomialRow62 (axis power order : Fin 3) :
    cachedPoly 62 axis power order = sourcePolyFromRelative 62 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 62

theorem relativeRow63 (axis : Fin 3) : cachedRelative 63 axis = sourceRelative 63 axis := by
  fin_cases axis
  closeLowGroupRelative 63

theorem polynomialRow63 (axis power order : Fin 3) :
    cachedPoly 63 axis power order = sourcePolyFromRelative 63 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 63

theorem relativeRow64 (axis : Fin 3) : cachedRelative 64 axis = sourceRelative 64 axis := by
  fin_cases axis
  closeLowGroupRelative 64

theorem polynomialRow64 (axis power order : Fin 3) :
    cachedPoly 64 axis power order = sourcePolyFromRelative 64 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 64

theorem relativeRow65 (axis : Fin 3) : cachedRelative 65 axis = sourceRelative 65 axis := by
  fin_cases axis
  closeLowGroupRelative 65

theorem polynomialRow65 (axis power order : Fin 3) :
    cachedPoly 65 axis power order = sourcePolyFromRelative 65 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 65

theorem relativeRow66 (axis : Fin 3) : cachedRelative 66 axis = sourceRelative 66 axis := by
  fin_cases axis
  closeLowGroupRelative 66

theorem polynomialRow66 (axis power order : Fin 3) :
    cachedPoly 66 axis power order = sourcePolyFromRelative 66 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 66

theorem relativeRow67 (axis : Fin 3) : cachedRelative 67 axis = sourceRelative 67 axis := by
  fin_cases axis
  closeLowGroupRelative 67

theorem polynomialRow67 (axis power order : Fin 3) :
    cachedPoly 67 axis power order = sourcePolyFromRelative 67 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 67

theorem relativeRow68 (axis : Fin 3) : cachedRelative 68 axis = sourceRelative 68 axis := by
  fin_cases axis
  closeLowGroupRelative 68

theorem polynomialRow68 (axis power order : Fin 3) :
    cachedPoly 68 axis power order = sourcePolyFromRelative 68 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 68

theorem relativeRow69 (axis : Fin 3) : cachedRelative 69 axis = sourceRelative 69 axis := by
  fin_cases axis
  closeLowGroupRelative 69

theorem polynomialRow69 (axis power order : Fin 3) :
    cachedPoly 69 axis power order = sourcePolyFromRelative 69 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 69

theorem relativeRow70 (axis : Fin 3) : cachedRelative 70 axis = sourceRelative 70 axis := by
  fin_cases axis
  closeLowGroupRelative 70

theorem polynomialRow70 (axis power order : Fin 3) :
    cachedPoly 70 axis power order = sourcePolyFromRelative 70 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 70

theorem relativeRow71 (axis : Fin 3) : cachedRelative 71 axis = sourceRelative 71 axis := by
  fin_cases axis
  closeLowGroupRelative 71

theorem polynomialRow71 (axis power order : Fin 3) :
    cachedPoly 71 axis power order = sourcePolyFromRelative 71 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 71

theorem relativeRow72 (axis : Fin 3) : cachedRelative 72 axis = sourceRelative 72 axis := by
  fin_cases axis
  closeLowGroupRelative 72

theorem polynomialRow72 (axis power order : Fin 3) :
    cachedPoly 72 axis power order = sourcePolyFromRelative 72 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 72

theorem relativeRow73 (axis : Fin 3) : cachedRelative 73 axis = sourceRelative 73 axis := by
  fin_cases axis
  closeLowGroupRelative 73

theorem polynomialRow73 (axis power order : Fin 3) :
    cachedPoly 73 axis power order = sourcePolyFromRelative 73 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 73

theorem relativeRow74 (axis : Fin 3) : cachedRelative 74 axis = sourceRelative 74 axis := by
  fin_cases axis
  closeLowGroupRelative 74

theorem polynomialRow74 (axis power order : Fin 3) :
    cachedPoly 74 axis power order = sourcePolyFromRelative 74 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 74

theorem relativeRow75 (axis : Fin 3) : cachedRelative 75 axis = sourceRelative 75 axis := by
  fin_cases axis
  closeLowGroupRelative 75

theorem polynomialRow75 (axis power order : Fin 3) :
    cachedPoly 75 axis power order = sourcePolyFromRelative 75 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 75

theorem relativeRow76 (axis : Fin 3) : cachedRelative 76 axis = sourceRelative 76 axis := by
  fin_cases axis
  closeLowGroupRelative 76

theorem polynomialRow76 (axis power order : Fin 3) :
    cachedPoly 76 axis power order = sourcePolyFromRelative 76 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 76

theorem relativeRow77 (axis : Fin 3) : cachedRelative 77 axis = sourceRelative 77 axis := by
  fin_cases axis
  closeLowGroupRelative 77

theorem polynomialRow77 (axis power order : Fin 3) :
    cachedPoly 77 axis power order = sourcePolyFromRelative 77 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 77

theorem relativeRow78 (axis : Fin 3) : cachedRelative 78 axis = sourceRelative 78 axis := by
  fin_cases axis
  closeLowGroupRelative 78

theorem polynomialRow78 (axis power order : Fin 3) :
    cachedPoly 78 axis power order = sourcePolyFromRelative 78 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 78

theorem relativeRow79 (axis : Fin 3) : cachedRelative 79 axis = sourceRelative 79 axis := by
  fin_cases axis
  closeLowGroupRelative 79

theorem polynomialRow79 (axis power order : Fin 3) :
    cachedPoly 79 axis power order = sourcePolyFromRelative 79 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 79

theorem relativeRow80 (axis : Fin 3) : cachedRelative 80 axis = sourceRelative 80 axis := by
  fin_cases axis
  closeLowGroupRelative 80

theorem polynomialRow80 (axis power order : Fin 3) :
    cachedPoly 80 axis power order = sourcePolyFromRelative 80 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 80

theorem relativeRow81 (axis : Fin 3) : cachedRelative 81 axis = sourceRelative 81 axis := by
  fin_cases axis
  closeLowGroupRelative 81

theorem polynomialRow81 (axis power order : Fin 3) :
    cachedPoly 81 axis power order = sourcePolyFromRelative 81 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 81

theorem relativeRow82 (axis : Fin 3) : cachedRelative 82 axis = sourceRelative 82 axis := by
  fin_cases axis
  closeLowGroupRelative 82

theorem polynomialRow82 (axis power order : Fin 3) :
    cachedPoly 82 axis power order = sourcePolyFromRelative 82 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 82

theorem relativeRow83 (axis : Fin 3) : cachedRelative 83 axis = sourceRelative 83 axis := by
  fin_cases axis
  closeLowGroupRelative 83

theorem polynomialRow83 (axis power order : Fin 3) :
    cachedPoly 83 axis power order = sourcePolyFromRelative 83 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 83

theorem relativeRow84 (axis : Fin 3) : cachedRelative 84 axis = sourceRelative 84 axis := by
  fin_cases axis
  closeLowGroupRelative 84

theorem polynomialRow84 (axis power order : Fin 3) :
    cachedPoly 84 axis power order = sourcePolyFromRelative 84 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 84

theorem relativeRow85 (axis : Fin 3) : cachedRelative 85 axis = sourceRelative 85 axis := by
  fin_cases axis
  closeLowGroupRelative 85

theorem polynomialRow85 (axis power order : Fin 3) :
    cachedPoly 85 axis power order = sourcePolyFromRelative 85 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 85

theorem relativeRow86 (axis : Fin 3) : cachedRelative 86 axis = sourceRelative 86 axis := by
  fin_cases axis
  closeLowGroupRelative 86

theorem polynomialRow86 (axis power order : Fin 3) :
    cachedPoly 86 axis power order = sourcePolyFromRelative 86 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 86

theorem relativeRow87 (axis : Fin 3) : cachedRelative 87 axis = sourceRelative 87 axis := by
  fin_cases axis
  closeLowGroupRelative 87

theorem polynomialRow87 (axis power order : Fin 3) :
    cachedPoly 87 axis power order = sourcePolyFromRelative 87 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 87

theorem relativeRow88 (axis : Fin 3) : cachedRelative 88 axis = sourceRelative 88 axis := by
  fin_cases axis
  closeLowGroupRelative 88

theorem polynomialRow88 (axis power order : Fin 3) :
    cachedPoly 88 axis power order = sourcePolyFromRelative 88 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 88

theorem relativeRow89 (axis : Fin 3) : cachedRelative 89 axis = sourceRelative 89 axis := by
  fin_cases axis
  closeLowGroupRelative 89

theorem polynomialRow89 (axis power order : Fin 3) :
    cachedPoly 89 axis power order = sourcePolyFromRelative 89 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 89

theorem relativeRow90 (axis : Fin 3) : cachedRelative 90 axis = sourceRelative 90 axis := by
  fin_cases axis
  closeLowGroupRelative 90

theorem polynomialRow90 (axis power order : Fin 3) :
    cachedPoly 90 axis power order = sourcePolyFromRelative 90 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 90

theorem relativeRow91 (axis : Fin 3) : cachedRelative 91 axis = sourceRelative 91 axis := by
  fin_cases axis
  closeLowGroupRelative 91

theorem polynomialRow91 (axis power order : Fin 3) :
    cachedPoly 91 axis power order = sourcePolyFromRelative 91 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 91

theorem relativeRow92 (axis : Fin 3) : cachedRelative 92 axis = sourceRelative 92 axis := by
  fin_cases axis
  closeLowGroupRelative 92

theorem polynomialRow92 (axis power order : Fin 3) :
    cachedPoly 92 axis power order = sourcePolyFromRelative 92 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 92

theorem relativeRow93 (axis : Fin 3) : cachedRelative 93 axis = sourceRelative 93 axis := by
  fin_cases axis
  closeLowGroupRelative 93

theorem polynomialRow93 (axis power order : Fin 3) :
    cachedPoly 93 axis power order = sourcePolyFromRelative 93 axis power order := by
  fin_cases axis <;> fin_cases power <;> fin_cases order
  closeLowGroupPolynomial 93

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.Field1
