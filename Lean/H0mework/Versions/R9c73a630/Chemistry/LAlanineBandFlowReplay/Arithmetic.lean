import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell00
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell01
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell02
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell03
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell04
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell05
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell06
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell07
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell08
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell09
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell10
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell11
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell12
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell13
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell14
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell15
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell16
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell17
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell18
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell19
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell20
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell21
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell22
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell23
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell24
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell25
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell26
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell27
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell28
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell29
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell30
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell31
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.Consumer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandReplay

open WholeBandSource SourceGaussianModel SourceSignedEvaluator IntervalParameterMap TrueTubeTrace
noncomputable section

theorem all_row_arithmetic (c : FullBandCell) (d : Direction) (i : Step) :
    RowArithmetic c d i := by
  fin_cases c
  · exact cellArithmetic0 d i
  · exact cellArithmetic1 d i
  · exact cellArithmetic2 d i
  · exact cellArithmetic3 d i
  · exact cellArithmetic4 d i
  · exact cellArithmetic5 d i
  · exact cellArithmetic6 d i
  · exact cellArithmetic7 d i
  · exact cellArithmetic8 d i
  · exact cellArithmetic9 d i
  · exact cellArithmetic10 d i
  · exact cellArithmetic11 d i
  · exact cellArithmetic12 d i
  · exact cellArithmetic13 d i
  · exact cellArithmetic14 d i
  · exact cellArithmetic15 d i
  · exact cellArithmetic16 d i
  · exact cellArithmetic17 d i
  · exact cellArithmetic18 d i
  · exact cellArithmetic19 d i
  · exact cellArithmetic20 d i
  · exact cellArithmetic21 d i
  · exact cellArithmetic22 d i
  · exact cellArithmetic23 d i
  · exact cellArithmetic24 d i
  · exact cellArithmetic25 d i
  · exact cellArithmetic26 d i
  · exact cellArithmetic27 d i
  · exact cellArithmetic28 d i
  · exact cellArithmetic29 d i
  · exact cellArithmetic30 d i
  · exact cellArithmetic31 d i

theorem endpoint_next_initial (c : FullBandCell) (d : Direction) (i : Fin 15) :
    endpointBox c d i.castSucc = initialBox c d i.succ := by
  fin_cases c
  · exact cellAdjacency0 d i
  · exact cellAdjacency1 d i
  · exact cellAdjacency2 d i
  · exact cellAdjacency3 d i
  · exact cellAdjacency4 d i
  · exact cellAdjacency5 d i
  · exact cellAdjacency6 d i
  · exact cellAdjacency7 d i
  · exact cellAdjacency8 d i
  · exact cellAdjacency9 d i
  · exact cellAdjacency10 d i
  · exact cellAdjacency11 d i
  · exact cellAdjacency12 d i
  · exact cellAdjacency13 d i
  · exact cellAdjacency14 d i
  · exact cellAdjacency15 d i
  · exact cellAdjacency16 d i
  · exact cellAdjacency17 d i
  · exact cellAdjacency18 d i
  · exact cellAdjacency19 d i
  · exact cellAdjacency20 d i
  · exact cellAdjacency21 d i
  · exact cellAdjacency22 d i
  · exact cellAdjacency23 d i
  · exact cellAdjacency24 d i
  · exact cellAdjacency25 d i
  · exact cellAdjacency26 d i
  · exact cellAdjacency27 d i
  · exact cellAdjacency28 d i
  · exact cellAdjacency29 d i
  · exact cellAdjacency30 d i
  · exact cellAdjacency31 d i

theorem common_initial (c : FullBandCell) : initialBox c 0 0 = initialBox c 1 0 := by
  fin_cases c
  · exact cellInitial0
  · exact cellInitial1
  · exact cellInitial2
  · exact cellInitial3
  · exact cellInitial4
  · exact cellInitial5
  · exact cellInitial6
  · exact cellInitial7
  · exact cellInitial8
  · exact cellInitial9
  · exact cellInitial10
  · exact cellInitial11
  · exact cellInitial12
  · exact cellInitial13
  · exact cellInitial14
  · exact cellInitial15
  · exact cellInitial16
  · exact cellInitial17
  · exact cellInitial18
  · exact cellInitial19
  · exact cellInitial20
  · exact cellInitial21
  · exact cellInitial22
  · exact cellInitial23
  · exact cellInitial24
  · exact cellInitial25
  · exact cellInitial26
  · exact cellInitial27
  · exact cellInitial28
  · exact cellInitial29
  · exact cellInitial30
  · exact cellInitial31

theorem time_step (c : FullBandCell) (d : Direction) (i : Step) :
    elapsedStart c d i = sign d * i.val * stepSize ∧
      elapsedStop c d i = sign d * (i.val + 1) * stepSize :=
  ⟨(all_row_arithmetic c d i).time_start, (all_row_arithmetic c d i).time_stop⟩

theorem time_next_start (c : FullBandCell) (d : Direction) (i : Fin 15) :
    elapsedStop c d i.castSucc = elapsedStart c d i.succ := by
  rw [(time_step c d i.castSucc).2, (time_step c d i.succ).1]
  simp

theorem time_endpoints (c : FullBandCell) (d : Direction) :
    elapsedStart c d 0 = 0 ∧ elapsedStop c d 15 = sign d / 2 := by
  have step_value : stepSize = 1/32 :=
    WholeBandSource.source_step_and_sign.1.trans TrueTubeChecks.step_value
  rw [(time_step c d 0).1, (time_step c d 15).2]
  norm_num [step_value, div_eq_mul_inv, mul_assoc]

theorem steps_from_source_fields (c : FullBandCell) (d : Direction) (i : Step)
    (initialField : ∀ x, InRectangle (callBox (initialCallAt c d i)) x →
      FieldHolds (recordedCallField (initialCallAt c d i)) x)
    (tubeField : ∀ x, InRectangle (callBox (tubeCallAt c d i)) x →
      FieldHolds (recordedCallField (tubeCallAt c d i)) x) : LocalStepLaw c d i :=
  step_from_arithmetic_and_fields c d i (all_row_arithmetic c d i) initialField tubeField

end
end LAlanine40K2025.BasinRefinement.WholeBandReplay
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
