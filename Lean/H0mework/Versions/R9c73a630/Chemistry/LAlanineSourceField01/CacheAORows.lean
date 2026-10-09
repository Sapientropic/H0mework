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

elab "closeLowAORow " basis:num : tactic => do
  let goals ← getGoals
  unless goals.length == 10 do throwError "source low-jet census"
  let base := (← getCurrNamespace) ++ `Checks
  for (goal,j) in goals.zipIdx do
    goal.assign (Lean.mkConst (base ++ Name.mkSimple s!"ao_{basis.getNat}_{j}"))
  setGoals []

theorem aoRowComputed0 (j : LowJet) : calculatedAO j 0 = sourceAO j 0 := by
  fin_cases j
  closeLowAORow 0

theorem aoRowComputed1 (j : LowJet) : calculatedAO j 1 = sourceAO j 1 := by
  fin_cases j
  closeLowAORow 1

theorem aoRowComputed2 (j : LowJet) : calculatedAO j 2 = sourceAO j 2 := by
  fin_cases j
  closeLowAORow 2

theorem aoRowComputed3 (j : LowJet) : calculatedAO j 3 = sourceAO j 3 := by
  fin_cases j
  closeLowAORow 3

theorem aoRowComputed4 (j : LowJet) : calculatedAO j 4 = sourceAO j 4 := by
  fin_cases j
  closeLowAORow 4

theorem aoRowComputed5 (j : LowJet) : calculatedAO j 5 = sourceAO j 5 := by
  fin_cases j
  closeLowAORow 5

theorem aoRowComputed6 (j : LowJet) : calculatedAO j 6 = sourceAO j 6 := by
  fin_cases j
  closeLowAORow 6

theorem aoRowComputed7 (j : LowJet) : calculatedAO j 7 = sourceAO j 7 := by
  fin_cases j
  closeLowAORow 7

theorem aoRowComputed8 (j : LowJet) : calculatedAO j 8 = sourceAO j 8 := by
  fin_cases j
  closeLowAORow 8

theorem aoRowComputed9 (j : LowJet) : calculatedAO j 9 = sourceAO j 9 := by
  fin_cases j
  closeLowAORow 9

theorem aoRowComputed10 (j : LowJet) : calculatedAO j 10 = sourceAO j 10 := by
  fin_cases j
  closeLowAORow 10

theorem aoRowComputed11 (j : LowJet) : calculatedAO j 11 = sourceAO j 11 := by
  fin_cases j
  closeLowAORow 11

theorem aoRowComputed12 (j : LowJet) : calculatedAO j 12 = sourceAO j 12 := by
  fin_cases j
  closeLowAORow 12

theorem aoRowComputed13 (j : LowJet) : calculatedAO j 13 = sourceAO j 13 := by
  fin_cases j
  closeLowAORow 13

theorem aoRowComputed14 (j : LowJet) : calculatedAO j 14 = sourceAO j 14 := by
  fin_cases j
  closeLowAORow 14

theorem aoRowComputed15 (j : LowJet) : calculatedAO j 15 = sourceAO j 15 := by
  fin_cases j
  closeLowAORow 15

theorem aoRowComputed16 (j : LowJet) : calculatedAO j 16 = sourceAO j 16 := by
  fin_cases j
  closeLowAORow 16

theorem aoRowComputed17 (j : LowJet) : calculatedAO j 17 = sourceAO j 17 := by
  fin_cases j
  closeLowAORow 17

theorem aoRowComputed18 (j : LowJet) : calculatedAO j 18 = sourceAO j 18 := by
  fin_cases j
  closeLowAORow 18

theorem aoRowComputed19 (j : LowJet) : calculatedAO j 19 = sourceAO j 19 := by
  fin_cases j
  closeLowAORow 19

theorem aoRowComputed20 (j : LowJet) : calculatedAO j 20 = sourceAO j 20 := by
  fin_cases j
  closeLowAORow 20

theorem aoRowComputed21 (j : LowJet) : calculatedAO j 21 = sourceAO j 21 := by
  fin_cases j
  closeLowAORow 21

theorem aoRowComputed22 (j : LowJet) : calculatedAO j 22 = sourceAO j 22 := by
  fin_cases j
  closeLowAORow 22

theorem aoRowComputed23 (j : LowJet) : calculatedAO j 23 = sourceAO j 23 := by
  fin_cases j
  closeLowAORow 23

theorem aoRowComputed24 (j : LowJet) : calculatedAO j 24 = sourceAO j 24 := by
  fin_cases j
  closeLowAORow 24

theorem aoRowComputed25 (j : LowJet) : calculatedAO j 25 = sourceAO j 25 := by
  fin_cases j
  closeLowAORow 25

theorem aoRowComputed26 (j : LowJet) : calculatedAO j 26 = sourceAO j 26 := by
  fin_cases j
  closeLowAORow 26

theorem aoRowComputed27 (j : LowJet) : calculatedAO j 27 = sourceAO j 27 := by
  fin_cases j
  closeLowAORow 27

theorem aoRowComputed28 (j : LowJet) : calculatedAO j 28 = sourceAO j 28 := by
  fin_cases j
  closeLowAORow 28

theorem aoRowComputed29 (j : LowJet) : calculatedAO j 29 = sourceAO j 29 := by
  fin_cases j
  closeLowAORow 29

theorem aoRowComputed30 (j : LowJet) : calculatedAO j 30 = sourceAO j 30 := by
  fin_cases j
  closeLowAORow 30

theorem aoRowComputed31 (j : LowJet) : calculatedAO j 31 = sourceAO j 31 := by
  fin_cases j
  closeLowAORow 31

theorem aoRowComputed32 (j : LowJet) : calculatedAO j 32 = sourceAO j 32 := by
  fin_cases j
  closeLowAORow 32

theorem aoRowComputed33 (j : LowJet) : calculatedAO j 33 = sourceAO j 33 := by
  fin_cases j
  closeLowAORow 33

theorem aoRowComputed34 (j : LowJet) : calculatedAO j 34 = sourceAO j 34 := by
  fin_cases j
  closeLowAORow 34

theorem aoRowComputed35 (j : LowJet) : calculatedAO j 35 = sourceAO j 35 := by
  fin_cases j
  closeLowAORow 35

theorem aoRowComputed36 (j : LowJet) : calculatedAO j 36 = sourceAO j 36 := by
  fin_cases j
  closeLowAORow 36

theorem aoRowComputed37 (j : LowJet) : calculatedAO j 37 = sourceAO j 37 := by
  fin_cases j
  closeLowAORow 37

theorem aoRowComputed38 (j : LowJet) : calculatedAO j 38 = sourceAO j 38 := by
  fin_cases j
  closeLowAORow 38

theorem aoRowComputed39 (j : LowJet) : calculatedAO j 39 = sourceAO j 39 := by
  fin_cases j
  closeLowAORow 39

theorem aoRowComputed40 (j : LowJet) : calculatedAO j 40 = sourceAO j 40 := by
  fin_cases j
  closeLowAORow 40

theorem aoRowComputed41 (j : LowJet) : calculatedAO j 41 = sourceAO j 41 := by
  fin_cases j
  closeLowAORow 41

theorem aoRowComputed42 (j : LowJet) : calculatedAO j 42 = sourceAO j 42 := by
  fin_cases j
  closeLowAORow 42

theorem aoRowComputed43 (j : LowJet) : calculatedAO j 43 = sourceAO j 43 := by
  fin_cases j
  closeLowAORow 43

theorem aoRowComputed44 (j : LowJet) : calculatedAO j 44 = sourceAO j 44 := by
  fin_cases j
  closeLowAORow 44

theorem aoRowComputed45 (j : LowJet) : calculatedAO j 45 = sourceAO j 45 := by
  fin_cases j
  closeLowAORow 45

theorem aoRowComputed46 (j : LowJet) : calculatedAO j 46 = sourceAO j 46 := by
  fin_cases j
  closeLowAORow 46

theorem aoRowComputed47 (j : LowJet) : calculatedAO j 47 = sourceAO j 47 := by
  fin_cases j
  closeLowAORow 47

theorem aoRowComputed48 (j : LowJet) : calculatedAO j 48 = sourceAO j 48 := by
  fin_cases j
  closeLowAORow 48

theorem aoRowComputed49 (j : LowJet) : calculatedAO j 49 = sourceAO j 49 := by
  fin_cases j
  closeLowAORow 49

theorem aoRowComputed50 (j : LowJet) : calculatedAO j 50 = sourceAO j 50 := by
  fin_cases j
  closeLowAORow 50

theorem aoRowComputed51 (j : LowJet) : calculatedAO j 51 = sourceAO j 51 := by
  fin_cases j
  closeLowAORow 51

theorem aoRowComputed52 (j : LowJet) : calculatedAO j 52 = sourceAO j 52 := by
  fin_cases j
  closeLowAORow 52

theorem aoRowComputed53 (j : LowJet) : calculatedAO j 53 = sourceAO j 53 := by
  fin_cases j
  closeLowAORow 53

theorem aoRowComputed54 (j : LowJet) : calculatedAO j 54 = sourceAO j 54 := by
  fin_cases j
  closeLowAORow 54

theorem aoRowComputed55 (j : LowJet) : calculatedAO j 55 = sourceAO j 55 := by
  fin_cases j
  closeLowAORow 55

theorem aoRowComputed56 (j : LowJet) : calculatedAO j 56 = sourceAO j 56 := by
  fin_cases j
  closeLowAORow 56

theorem aoRowComputed57 (j : LowJet) : calculatedAO j 57 = sourceAO j 57 := by
  fin_cases j
  closeLowAORow 57

theorem aoRowComputed58 (j : LowJet) : calculatedAO j 58 = sourceAO j 58 := by
  fin_cases j
  closeLowAORow 58

theorem aoRowComputed59 (j : LowJet) : calculatedAO j 59 = sourceAO j 59 := by
  fin_cases j
  closeLowAORow 59

theorem aoRowComputed60 (j : LowJet) : calculatedAO j 60 = sourceAO j 60 := by
  fin_cases j
  closeLowAORow 60

theorem aoRowComputed61 (j : LowJet) : calculatedAO j 61 = sourceAO j 61 := by
  fin_cases j
  closeLowAORow 61

theorem aoRowComputed62 (j : LowJet) : calculatedAO j 62 = sourceAO j 62 := by
  fin_cases j
  closeLowAORow 62

theorem aoRowComputed63 (j : LowJet) : calculatedAO j 63 = sourceAO j 63 := by
  fin_cases j
  closeLowAORow 63

theorem aoRowComputed64 (j : LowJet) : calculatedAO j 64 = sourceAO j 64 := by
  fin_cases j
  closeLowAORow 64

theorem aoRowComputed65 (j : LowJet) : calculatedAO j 65 = sourceAO j 65 := by
  fin_cases j
  closeLowAORow 65

theorem aoRowComputed66 (j : LowJet) : calculatedAO j 66 = sourceAO j 66 := by
  fin_cases j
  closeLowAORow 66

theorem aoRowComputed67 (j : LowJet) : calculatedAO j 67 = sourceAO j 67 := by
  fin_cases j
  closeLowAORow 67

theorem aoRowComputed68 (j : LowJet) : calculatedAO j 68 = sourceAO j 68 := by
  fin_cases j
  closeLowAORow 68

theorem aoRowComputed69 (j : LowJet) : calculatedAO j 69 = sourceAO j 69 := by
  fin_cases j
  closeLowAORow 69

theorem aoRowComputed70 (j : LowJet) : calculatedAO j 70 = sourceAO j 70 := by
  fin_cases j
  closeLowAORow 70

theorem aoRowComputed71 (j : LowJet) : calculatedAO j 71 = sourceAO j 71 := by
  fin_cases j
  closeLowAORow 71

theorem aoRowComputed72 (j : LowJet) : calculatedAO j 72 = sourceAO j 72 := by
  fin_cases j
  closeLowAORow 72

theorem aoRowComputed73 (j : LowJet) : calculatedAO j 73 = sourceAO j 73 := by
  fin_cases j
  closeLowAORow 73

theorem aoRowComputed74 (j : LowJet) : calculatedAO j 74 = sourceAO j 74 := by
  fin_cases j
  closeLowAORow 74

theorem aoRowComputed75 (j : LowJet) : calculatedAO j 75 = sourceAO j 75 := by
  fin_cases j
  closeLowAORow 75

theorem aoRowComputed76 (j : LowJet) : calculatedAO j 76 = sourceAO j 76 := by
  fin_cases j
  closeLowAORow 76

theorem aoRowComputed77 (j : LowJet) : calculatedAO j 77 = sourceAO j 77 := by
  fin_cases j
  closeLowAORow 77

theorem aoRowComputed78 (j : LowJet) : calculatedAO j 78 = sourceAO j 78 := by
  fin_cases j
  closeLowAORow 78

theorem aoRowComputed79 (j : LowJet) : calculatedAO j 79 = sourceAO j 79 := by
  fin_cases j
  closeLowAORow 79

theorem aoRowComputed80 (j : LowJet) : calculatedAO j 80 = sourceAO j 80 := by
  fin_cases j
  closeLowAORow 80

theorem aoRowComputed81 (j : LowJet) : calculatedAO j 81 = sourceAO j 81 := by
  fin_cases j
  closeLowAORow 81

theorem aoRowComputed82 (j : LowJet) : calculatedAO j 82 = sourceAO j 82 := by
  fin_cases j
  closeLowAORow 82

theorem aoRowComputed83 (j : LowJet) : calculatedAO j 83 = sourceAO j 83 := by
  fin_cases j
  closeLowAORow 83

theorem aoRowComputed84 (j : LowJet) : calculatedAO j 84 = sourceAO j 84 := by
  fin_cases j
  closeLowAORow 84

theorem aoRowComputed85 (j : LowJet) : calculatedAO j 85 = sourceAO j 85 := by
  fin_cases j
  closeLowAORow 85

theorem aoRowComputed86 (j : LowJet) : calculatedAO j 86 = sourceAO j 86 := by
  fin_cases j
  closeLowAORow 86

theorem aoRowComputed87 (j : LowJet) : calculatedAO j 87 = sourceAO j 87 := by
  fin_cases j
  closeLowAORow 87

theorem aoRowComputed88 (j : LowJet) : calculatedAO j 88 = sourceAO j 88 := by
  fin_cases j
  closeLowAORow 88

theorem aoRowComputed89 (j : LowJet) : calculatedAO j 89 = sourceAO j 89 := by
  fin_cases j
  closeLowAORow 89

theorem aoRowComputed90 (j : LowJet) : calculatedAO j 90 = sourceAO j 90 := by
  fin_cases j
  closeLowAORow 90

theorem aoRowComputed91 (j : LowJet) : calculatedAO j 91 = sourceAO j 91 := by
  fin_cases j
  closeLowAORow 91

theorem aoRowComputed92 (j : LowJet) : calculatedAO j 92 = sourceAO j 92 := by
  fin_cases j
  closeLowAORow 92

theorem aoRowComputed93 (j : LowJet) : calculatedAO j 93 = sourceAO j 93 := by
  fin_cases j
  closeLowAORow 93

theorem aoRowComputed94 (j : LowJet) : calculatedAO j 94 = sourceAO j 94 := by
  fin_cases j
  closeLowAORow 94

theorem aoRowComputed95 (j : LowJet) : calculatedAO j 95 = sourceAO j 95 := by
  fin_cases j
  closeLowAORow 95

theorem aoRowComputed96 (j : LowJet) : calculatedAO j 96 = sourceAO j 96 := by
  fin_cases j
  closeLowAORow 96

theorem aoRowComputed97 (j : LowJet) : calculatedAO j 97 = sourceAO j 97 := by
  fin_cases j
  closeLowAORow 97

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.Field1
