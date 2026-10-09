import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B177
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B178

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4257_pa : Scalar.QComplex := ((999998599775687351538343041915 : Int)/10^30,(-1673453514343555819244955839 : Int)/10^30)
theorem v4257_pa_checked : Scalar.distance (sourceCoefficient 66 67 1 0) v4257_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4257_pb : Scalar.QComplex := ((-722057573773937352452183 : Int)/10^30,(-431476916772682468786959663 : Int)/10^30)
theorem v4257_pb_checked : Scalar.distance (sourceCoefficient 66 67 1 1) v4257_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4257_pg : Scalar.QComplex := ((-93086299548335181228248 : Int)/10^30,(155775813237479479483 : Int)/10^30)
theorem v4257_pg_checked : Scalar.distance (sourceCoefficient 66 67 1 2) v4257_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4257_mb : Scalar.QComplex := ((-1094402451094783333929848 : Int)/10^30,(-431476133010940984065045740 : Int)/10^30)
theorem v4257_mb_checked : Scalar.distance (sourceCoefficient 66 67 3 1) v4257_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4257_mg : Scalar.QComplex := ((-93086130460540663570924 : Int)/10^30,(236105039293937616967 : Int)/10^30)
theorem v4257_mg_checked : Scalar.distance (sourceCoefficient 66 67 3 2) v4257_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4257_upper : Scalar.QComplex := ((999994222166289832798730887793 : Int)/10^30,(-3399357885979647803070070973 : Int)/10^30)
theorem v4257_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 67 5) 1) 14) v4257_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4257 : Material (66 : Basis) (67 : Basis) where
  plus := ![v4257_pa,v4257_pb,v4257_pg]
  minus := ![(Primitive.Addresses.material4257 1).one,v4257_mb,v4257_mg]
  upper := v4257_upper
  lower := (Primitive.Addresses.material4257 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4257_pa_checked.trans (by decide +kernel)
    · exact v4257_pb_checked.trans (by decide +kernel)
    · exact v4257_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 67 Primitive.Addresses.material4257
    · exact v4257_mb_checked.trans (by decide +kernel)
    · exact v4257_mg_checked.trans (by decide +kernel)
  upper_error := v4257_upper_checked
  lower_error := reuse_lower_error 66 67 Primitive.Addresses.material4257

def v4258_pa : Scalar.QComplex := ((999998516303835907047565090711 : Int)/10^30,(-1722611426535769129802083441 : Int)/10^30)
theorem v4258_pa_checked : Scalar.distance (sourceCoefficient 66 68 1 0) v4258_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4258_pb : Scalar.QComplex := ((-743268107202274227295316 : Int)/10^30,(-431476880373985564126871682 : Int)/10^30)
theorem v4258_pb_checked : Scalar.distance (sourceCoefficient 66 68 1 1) v4258_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4258_pg : Scalar.QComplex := ((-93086291736981797916166 : Int)/10^30,(160351747713239981100 : Int)/10^30)
theorem v4258_pg_checked : Scalar.distance (sourceCoefficient 66 68 1 2) v4258_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4258_mb : Scalar.QComplex := ((-1115612945215033151869575 : Int)/10^30,(-431476078308522570612288301 : Int)/10^30)
theorem v4258_mb_checked : Scalar.distance (sourceCoefficient 66 68 3 1) v4258_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4258_mg : Scalar.QComplex := ((-93086118700364828639667 : Int)/10^30,(240680965325022423220 : Int)/10^30)
theorem v4258_mg_checked : Scalar.distance (sourceCoefficient 66 68 3 2) v4258_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4258_upper : Scalar.QComplex := ((999994053852465837023034055855 : Int)/10^30,(-3448515580892082311346430901 : Int)/10^30)
theorem v4258_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 68 5) 1) 14) v4258_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4258 : Material (66 : Basis) (68 : Basis) where
  plus := ![v4258_pa,v4258_pb,v4258_pg]
  minus := ![(Primitive.Addresses.material4258 1).one,v4258_mb,v4258_mg]
  upper := v4258_upper
  lower := (Primitive.Addresses.material4258 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4258_pa_checked.trans (by decide +kernel)
    · exact v4258_pb_checked.trans (by decide +kernel)
    · exact v4258_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 68 Primitive.Addresses.material4258
    · exact v4258_mb_checked.trans (by decide +kernel)
    · exact v4258_mg_checked.trans (by decide +kernel)
  upper_error := v4258_upper_checked
  lower_error := reuse_lower_error 66 68 Primitive.Addresses.material4258

def v4259_pa : Scalar.QComplex := ((999998478800425067988544468714 : Int)/10^30,(-1744246781798916244665258181 : Int)/10^30)
theorem v4259_pa_checked : Scalar.distance (sourceCoefficient 66 69 1 0) v4259_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4259_pb : Scalar.QComplex := ((-752603276161821729238611 : Int)/10^30,(-431476863913629927838947351 : Int)/10^30)
theorem v4259_pb_checked : Scalar.distance (sourceCoefficient 66 69 1 1) v4259_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4259_pg : Scalar.QComplex := ((-93086288215884042379551 : Int)/10^30,(162365705640804526129 : Int)/10^30)
theorem v4259_pg_checked : Scalar.distance (sourceCoefficient 66 69 1 2) v4259_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4259_mb : Scalar.QComplex := ((-1124948096494125044656813 : Int)/10^30,(-431476053792342691580005243 : Int)/10^30)
theorem v4259_mb_checked : Scalar.distance (sourceCoefficient 66 69 3 1) v4259_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4259_mg : Scalar.QComplex := ((-93086113441313397978384 : Int)/10^30,(242694919464149610721 : Int)/10^30)
theorem v4259_mg_checked : Scalar.distance (sourceCoefficient 66 69 3 2) v4259_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4259_upper : Scalar.QComplex := ((999993979008450414794435074118 : Int)/10^30,(-3470150839204424403747806676 : Int)/10^30)
theorem v4259_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 69 5) 1) 14) v4259_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4259 : Material (66 : Basis) (69 : Basis) where
  plus := ![v4259_pa,v4259_pb,v4259_pg]
  minus := ![(Primitive.Addresses.material4259 1).one,v4259_mb,v4259_mg]
  upper := v4259_upper
  lower := (Primitive.Addresses.material4259 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4259_pa_checked.trans (by decide +kernel)
    · exact v4259_pb_checked.trans (by decide +kernel)
    · exact v4259_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 69 Primitive.Addresses.material4259
    · exact v4259_mb_checked.trans (by decide +kernel)
    · exact v4259_mg_checked.trans (by decide +kernel)
  upper_error := v4259_upper_checked
  lower_error := reuse_lower_error 66 69 Primitive.Addresses.material4259

def v4260_pa : Scalar.QComplex := ((999998453875089611335249720350 : Int)/10^30,(-1758478726136626020286590703 : Int)/10^30)
theorem v4260_pa_checked : Scalar.distance (sourceCoefficient 66 70 1 0) v4260_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4260_pb : Scalar.QComplex := ((-758744039826698909585031 : Int)/10^30,(-431476852939014378120978513 : Int)/10^30)
theorem v4260_pb_checked : Scalar.distance (sourceCoefficient 66 70 1 1) v4260_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4260_pg : Scalar.QComplex := ((-93086285871953763838097 : Int)/10^30,(163690506486872736038 : Int)/10^30)
theorem v4260_pg_checked : Scalar.distance (sourceCoefficient 66 70 1 2) v4260_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4260_mb : Scalar.QComplex := ((-1131088848401916324735020 : Int)/10^30,(-431476037518528755152678779 : Int)/10^30)
theorem v4260_mb_checked : Scalar.distance (sourceCoefficient 66 70 3 1) v4260_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4260_mg : Scalar.QComplex := ((-93086109954140528847602 : Int)/10^30,(244019717794227655568 : Int)/10^30)
theorem v4260_mg_checked : Scalar.distance (sourceCoefficient 66 70 3 2) v4260_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4260_upper : Scalar.QComplex := ((999993929520107266517999022916 : Int)/10^30,(-3484382719326457100555441648 : Int)/10^30)
theorem v4260_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 70 5) 1) 14) v4260_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4260 : Material (66 : Basis) (70 : Basis) where
  plus := ![v4260_pa,v4260_pb,v4260_pg]
  minus := ![(Primitive.Addresses.material4260 1).one,v4260_mb,v4260_mg]
  upper := v4260_upper
  lower := (Primitive.Addresses.material4260 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4260_pa_checked.trans (by decide +kernel)
    · exact v4260_pb_checked.trans (by decide +kernel)
    · exact v4260_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 70 Primitive.Addresses.material4260
    · exact v4260_mb_checked.trans (by decide +kernel)
    · exact v4260_mg_checked.trans (by decide +kernel)
  upper_error := v4260_upper_checked
  lower_error := reuse_lower_error 66 70 Primitive.Addresses.material4260

def v4261_pa : Scalar.QComplex := ((999998410861618578664100064348 : Int)/10^30,(-1782771504563015078664578537 : Int)/10^30)
theorem v4261_pa_checked : Scalar.distance (sourceCoefficient 66 71 1 0) v4261_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4261_pb : Scalar.QComplex := ((-769225826828284359736030 : Int)/10^30,(-431476833937026515735918447 : Int)/10^30)
theorem v4261_pb_checked : Scalar.distance (sourceCoefficient 66 71 1 1) v4261_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4261_pg : Scalar.QComplex := ((-93086281820235786664854 : Int)/10^30,(165951834415268127889 : Int)/10^30)
theorem v4261_pg_checked : Scalar.distance (sourceCoefficient 66 71 1 2) v4261_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4261_mb : Scalar.QComplex := ((-1141570615102793725390228 : Int)/10^30,(-431476009471237867869927953 : Int)/10^30)
theorem v4261_mb_checked : Scalar.distance (sourceCoefficient 66 71 3 1) v4261_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4261_mg : Scalar.QComplex := ((-93086103950999904538089 : Int)/10^30,(246281041384177180189 : Int)/10^30)
theorem v4261_mg_checked : Scalar.distance (sourceCoefficient 66 71 3 2) v4261_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4261_upper : Scalar.QComplex := ((999993844579568557055236990255 : Int)/10^30,(-3508675387334257472257223819 : Int)/10^30)
theorem v4261_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 71 5) 1) 14) v4261_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4261 : Material (66 : Basis) (71 : Basis) where
  plus := ![v4261_pa,v4261_pb,v4261_pg]
  minus := ![(Primitive.Addresses.material4261 1).one,v4261_mb,v4261_mg]
  upper := v4261_upper
  lower := (Primitive.Addresses.material4261 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4261_pa_checked.trans (by decide +kernel)
    · exact v4261_pb_checked.trans (by decide +kernel)
    · exact v4261_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 71 Primitive.Addresses.material4261
    · exact v4261_mb_checked.trans (by decide +kernel)
    · exact v4261_mg_checked.trans (by decide +kernel)
  upper_error := v4261_upper_checked
  lower_error := reuse_lower_error 66 71 Primitive.Addresses.material4261

def v4262_pa : Scalar.QComplex := ((999998363515586381469625579223 : Int)/10^30,(-1809134088218953640214757218 : Int)/10^30)
theorem v4262_pa_checked : Scalar.distance (sourceCoefficient 66 72 1 0) v4262_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4262_pb : Scalar.QComplex := ((-780600687992011486346280 : Int)/10^30,(-431476812931888611154332373 : Int)/10^30)
theorem v4262_pb_checked : Scalar.distance (sourceCoefficient 66 72 1 1) v4262_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4262_pg : Scalar.QComplex := ((-93086277350787920388736 : Int)/10^30,(168405833094235360874 : Int)/10^30)
theorem v4262_pg_checked : Scalar.distance (sourceCoefficient 66 72 1 2) v4262_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4262_mb : Scalar.QComplex := ((-1152945453904652208547034 : Int)/10^30,(-431475978650114904893824507 : Int)/10^30)
theorem v4262_mb_checked : Scalar.distance (sourceCoefficient 66 72 3 1) v4262_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4262_mg : Scalar.QComplex := ((-93086097363863366490611 : Int)/10^30,(248735035292476339577 : Int)/10^30)
theorem v4262_mg_checked : Scalar.distance (sourceCoefficient 66 72 3 2) v4262_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4262_upper : Scalar.QComplex := ((999993751734179080971259939808 : Int)/10^30,(-3535037850011268071030148609 : Int)/10^30)
theorem v4262_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 72 5) 1) 14) v4262_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4262 : Material (66 : Basis) (72 : Basis) where
  plus := ![v4262_pa,v4262_pb,v4262_pg]
  minus := ![(Primitive.Addresses.material4262 1).one,v4262_mb,v4262_mg]
  upper := v4262_upper
  lower := (Primitive.Addresses.material4262 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4262_pa_checked.trans (by decide +kernel)
    · exact v4262_pb_checked.trans (by decide +kernel)
    · exact v4262_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 72 Primitive.Addresses.material4262
    · exact v4262_mb_checked.trans (by decide +kernel)
    · exact v4262_mg_checked.trans (by decide +kernel)
  upper_error := v4262_upper_checked
  lower_error := reuse_lower_error 66 72 Primitive.Addresses.material4262

def v4263_pa : Scalar.QComplex := ((999998346375267978038281253669 : Int)/10^30,(-1818583715304073947372693495 : Int)/10^30)
theorem v4263_pa_checked : Scalar.distance (sourceCoefficient 66 73 1 0) v4263_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4263_pb : Scalar.QComplex := ((-784677989222546390343087 : Int)/10^30,(-431476805305284438494550969 : Int)/10^30)
theorem v4263_pb_checked : Scalar.distance (sourceCoefficient 66 73 1 1) v4263_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4263_pg : Scalar.QComplex := ((-93086275730345293052048 : Int)/10^30,(169285465096142647401 : Int)/10^30)
theorem v4263_pg_checked : Scalar.distance (sourceCoefficient 66 73 1 2) v4263_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4263_mb : Scalar.QComplex := ((-1157022747035605611039601 : Int)/10^30,(-431475967504986244846285417 : Int)/10^30)
theorem v4263_mb_checked : Scalar.distance (sourceCoefficient 66 73 3 1) v4263_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4263_mg : Scalar.QComplex := ((-93086094984338542027490 : Int)/10^30,(249614665568487425261 : Int)/10^30)
theorem v4263_mg_checked : Scalar.distance (sourceCoefficient 66 73 3 2) v4263_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4263_upper : Scalar.QComplex := ((999993718284687120585671497965 : Int)/10^30,(-3544487433439644259290639883 : Int)/10^30)
theorem v4263_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 73 5) 1) 14) v4263_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4263 : Material (66 : Basis) (73 : Basis) where
  plus := ![v4263_pa,v4263_pb,v4263_pg]
  minus := ![(Primitive.Addresses.material4263 1).one,v4263_mb,v4263_mg]
  upper := v4263_upper
  lower := (Primitive.Addresses.material4263 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4263_pa_checked.trans (by decide +kernel)
    · exact v4263_pb_checked.trans (by decide +kernel)
    · exact v4263_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 73 Primitive.Addresses.material4263
    · exact v4263_mb_checked.trans (by decide +kernel)
    · exact v4263_mg_checked.trans (by decide +kernel)
  upper_error := v4263_upper_checked
  lower_error := reuse_lower_error 66 73 Primitive.Addresses.material4263

def v4264_pa : Scalar.QComplex := ((999998326981424762316950591463 : Int)/10^30,(-1829216868357662234383630834 : Int)/10^30)
theorem v4264_pa_checked : Scalar.distance (sourceCoefficient 66 74 1 0) v4264_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4264_pb : Scalar.QComplex := ((-789265955215761929489309 : Int)/10^30,(-431476796662053903401620912 : Int)/10^30)
theorem v4264_pb_checked : Scalar.distance (sourceCoefficient 66 74 1 1) v4264_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4264_pg : Scalar.QComplex := ((-93086273895353515255872 : Int)/10^30,(170275267295627250787 : Int)/10^30)
theorem v4264_pg_checked : Scalar.distance (sourceCoefficient 66 74 1 2) v4264_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4264_mb : Scalar.QComplex := ((-1161610703861793055374839 : Int)/10^30,(-431475954902550910195796435 : Int)/10^30)
theorem v4264_mb_checked : Scalar.distance (sourceCoefficient 66 74 3 1) v4264_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4264_mg : Scalar.QComplex := ((-93086092295192728363617 : Int)/10^30,(250604465815908174307 : Int)/10^30)
theorem v4264_mg_checked : Scalar.distance (sourceCoefficient 66 74 3 2) v4264_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4264_upper : Scalar.QComplex := ((999993680539015251331995428537 : Int)/10^30,(-3555120537184386136258898501 : Int)/10^30)
theorem v4264_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 74 5) 1) 14) v4264_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4264 : Material (66 : Basis) (74 : Basis) where
  plus := ![v4264_pa,v4264_pb,v4264_pg]
  minus := ![(Primitive.Addresses.material4264 1).one,v4264_mb,v4264_mg]
  upper := v4264_upper
  lower := (Primitive.Addresses.material4264 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4264_pa_checked.trans (by decide +kernel)
    · exact v4264_pb_checked.trans (by decide +kernel)
    · exact v4264_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 74 Primitive.Addresses.material4264
    · exact v4264_mb_checked.trans (by decide +kernel)
    · exact v4264_mg_checked.trans (by decide +kernel)
  upper_error := v4264_upper_checked
  lower_error := reuse_lower_error 66 74 Primitive.Addresses.material4264

def v4265_pa : Scalar.QComplex := ((999998299771597157858645501577 : Int)/10^30,(-1844031972311668157389411508 : Int)/10^30)
theorem v4265_pa_checked : Scalar.distance (sourceCoefficient 66 75 1 0) v4265_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4265_pb : Scalar.QComplex := ((-795658338749506845482350 : Int)/10^30,(-431476784511045761299843085 : Int)/10^30)
theorem v4265_pb_checked : Scalar.distance (sourceCoefficient 66 75 1 1) v4265_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4265_pg : Scalar.QComplex := ((-93086271318198881999231 : Int)/10^30,(171654352345642680055 : Int)/10^30)
theorem v4265_pg_checked : Scalar.distance (sourceCoefficient 66 75 1 2) v4265_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4265_mb : Scalar.QComplex := ((-1168003074529588669852432 : Int)/10^30,(-431475937235208205114741272 : Int)/10^30)
theorem v4265_mb_checked : Scalar.distance (sourceCoefficient 66 75 3 1) v4265_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4265_mg : Scalar.QComplex := ((-93086088527950768221070 : Int)/10^30,(251983548128458834390 : Int)/10^30)
theorem v4265_mg_checked : Scalar.distance (sourceCoefficient 66 75 3 2) v4265_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4265_upper : Scalar.QComplex := ((999993627759702763833225875325 : Int)/10^30,(-3569935572111341035115727638 : Int)/10^30)
theorem v4265_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 75 5) 1) 14) v4265_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4265 : Material (66 : Basis) (75 : Basis) where
  plus := ![v4265_pa,v4265_pb,v4265_pg]
  minus := ![(Primitive.Addresses.material4265 1).one,v4265_mb,v4265_mg]
  upper := v4265_upper
  lower := (Primitive.Addresses.material4265 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4265_pa_checked.trans (by decide +kernel)
    · exact v4265_pb_checked.trans (by decide +kernel)
    · exact v4265_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 75 Primitive.Addresses.material4265
    · exact v4265_mb_checked.trans (by decide +kernel)
    · exact v4265_mg_checked.trans (by decide +kernel)
  upper_error := v4265_upper_checked
  lower_error := reuse_lower_error 66 75 Primitive.Addresses.material4265

def v4266_pa : Scalar.QComplex := ((999998276772684037407760231067 : Int)/10^30,(-1856462136002994810312185650 : Int)/10^30)
theorem v4266_pa_checked : Scalar.distance (sourceCoefficient 66 76 1 0) v4266_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4266_pb : Scalar.QComplex := ((-801021674244147290953332 : Int)/10^30,(-431476774218693445119957296 : Int)/10^30)
theorem v4266_pb_checked : Scalar.distance (sourceCoefficient 66 76 1 1) v4266_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4266_pg : Scalar.QComplex := ((-93086269137525808030025 : Int)/10^30,(172811431828980653356 : Int)/10^30)
theorem v4266_pg_checked : Scalar.distance (sourceCoefficient 66 76 1 2) v4266_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4266_mb : Scalar.QComplex := ((-1173366399145377695604950 : Int)/10^30,(-431475922314542745037012966 : Int)/10^30)
theorem v4266_mb_checked : Scalar.distance (sourceCoefficient 66 76 3 1) v4266_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4266_mg : Scalar.QComplex := ((-93086085348771025020847 : Int)/10^30,(253140625299140585933 : Int)/10^30)
theorem v4266_mg_checked : Scalar.distance (sourceCoefficient 66 76 3 2) v4266_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4266_upper : Scalar.QComplex := ((999993583307489021973303151280 : Int)/10^30,(-3582365677595361418606194999 : Int)/10^30)
theorem v4266_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 76 5) 1) 14) v4266_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4266 : Material (66 : Basis) (76 : Basis) where
  plus := ![v4266_pa,v4266_pb,v4266_pg]
  minus := ![(Primitive.Addresses.material4266 1).one,v4266_mb,v4266_mg]
  upper := v4266_upper
  lower := (Primitive.Addresses.material4266 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4266_pa_checked.trans (by decide +kernel)
    · exact v4266_pb_checked.trans (by decide +kernel)
    · exact v4266_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 76 Primitive.Addresses.material4266
    · exact v4266_mb_checked.trans (by decide +kernel)
    · exact v4266_mg_checked.trans (by decide +kernel)
  upper_error := v4266_upper_checked
  lower_error := reuse_lower_error 66 76 Primitive.Addresses.material4266

def v4267_pa : Scalar.QComplex := ((999998271426214589321709567897 : Int)/10^30,(-1859339824468358170239236362 : Int)/10^30)
theorem v4267_pa_checked : Scalar.distance (sourceCoefficient 66 77 1 0) v4267_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4267_pb : Scalar.QComplex := ((-802263331955389408475498 : Int)/10^30,(-431476771823255006456835330 : Int)/10^30)
theorem v4267_pb_checked : Scalar.distance (sourceCoefficient 66 77 1 1) v4267_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4267_pg : Scalar.QComplex := ((-93086268630289459534056 : Int)/10^30,(173079305555807220062 : Int)/10^30)
theorem v4267_pg_checked : Scalar.distance (sourceCoefficient 66 77 1 2) v4267_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4267_mb : Scalar.QComplex := ((-1174608054327138414647001 : Int)/10^30,(-431475918847610515690536407 : Int)/10^30)
theorem v4267_mb_checked : Scalar.distance (sourceCoefficient 66 77 3 1) v4267_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4267_mg : Scalar.QComplex := ((-93086084610371903725623 : Int)/10^30,(253408498488503398033 : Int)/10^30)
theorem v4267_mg_checked : Scalar.distance (sourceCoefficient 66 77 3 2) v4267_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4267_upper : Scalar.QComplex := ((999993572994398307466570200246 : Int)/10^30,(-3585243352547224606930445852 : Int)/10^30)
theorem v4267_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 77 5) 1) 14) v4267_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4267 : Material (66 : Basis) (77 : Basis) where
  plus := ![v4267_pa,v4267_pb,v4267_pg]
  minus := ![(Primitive.Addresses.material4267 1).one,v4267_mb,v4267_mg]
  upper := v4267_upper
  lower := (Primitive.Addresses.material4267 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4267_pa_checked.trans (by decide +kernel)
    · exact v4267_pb_checked.trans (by decide +kernel)
    · exact v4267_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 77 Primitive.Addresses.material4267
    · exact v4267_mb_checked.trans (by decide +kernel)
    · exact v4267_mg_checked.trans (by decide +kernel)
  upper_error := v4267_upper_checked
  lower_error := reuse_lower_error 66 77 Primitive.Addresses.material4267

def v4268_pa : Scalar.QComplex := ((999998239110761710586645076271 : Int)/10^30,(-1876639383538541532112529021 : Int)/10^30)
theorem v4268_pa_checked : Scalar.distance (sourceCoefficient 66 78 1 0) v4268_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4268_pb : Scalar.QComplex := ((-809727701713496044465557 : Int)/10^30,(-431476757322390690972116240 : Int)/10^30)
theorem v4268_pb_checked : Scalar.distance (sourceCoefficient 66 78 1 1) v4268_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4268_pg : Scalar.QComplex := ((-93086265562025070894439 : Int)/10^30,(174689659629365379138 : Int)/10^30)
theorem v4268_pg_checked : Scalar.distance (sourceCoefficient 66 78 1 2) v4268_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4268_mb : Scalar.QComplex := ((-1182072408792326241564870 : Int)/10^30,(-431475897905336681028512767 : Int)/10^30)
theorem v4268_mb_checked : Scalar.distance (sourceCoefficient 66 78 3 1) v4268_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4268_mg : Scalar.QComplex := ((-93086080152445619715494 : Int)/10^30,(255018849314679160809 : Int)/10^30)
theorem v4268_mg_checked : Scalar.distance (sourceCoefficient 66 78 3 2) v4268_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4268_upper : Scalar.QComplex := ((999993510821524007405384043836 : Int)/10^30,(-3602542830078206849012445065 : Int)/10^30)
theorem v4268_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 78 5) 1) 14) v4268_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4268 : Material (66 : Basis) (78 : Basis) where
  plus := ![v4268_pa,v4268_pb,v4268_pg]
  minus := ![(Primitive.Addresses.material4268 1).one,v4268_mb,v4268_mg]
  upper := v4268_upper
  lower := (Primitive.Addresses.material4268 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4268_pa_checked.trans (by decide +kernel)
    · exact v4268_pb_checked.trans (by decide +kernel)
    · exact v4268_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 78 Primitive.Addresses.material4268
    · exact v4268_mb_checked.trans (by decide +kernel)
    · exact v4268_mg_checked.trans (by decide +kernel)
  upper_error := v4268_upper_checked
  lower_error := reuse_lower_error 66 78 Primitive.Addresses.material4268

def v4269_pa : Scalar.QComplex := ((999998228629039840416810768697 : Int)/10^30,(-1882216454758614600125968166 : Int)/10^30)
theorem v4269_pa_checked : Scalar.distance (sourceCoefficient 66 79 1 0) v4269_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4269_pb : Scalar.QComplex := ((-812134082200718573172906 : Int)/10^30,(-431476752610868974381328789 : Int)/10^30)
theorem v4269_pb_checked : Scalar.distance (sourceCoefficient 66 79 1 1) v4269_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4269_pg : Scalar.QComplex := ((-93086264565943085754415 : Int)/10^30,(175208809237828491435 : Int)/10^30)
theorem v4269_pg_checked : Scalar.distance (sourceCoefficient 66 79 1 2) v4269_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4269_mb : Scalar.QComplex := ((-1184478784317712295501097 : Int)/10^30,(-431475891117218737633459079 : Int)/10^30)
theorem v4269_mb_checked : Scalar.distance (sourceCoefficient 66 79 3 1) v4269_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4269_mg : Scalar.QComplex := ((-93086078708361274989048 : Int)/10^30,(255537997870265256256 : Int)/10^30)
theorem v4269_mg_checked : Scalar.distance (sourceCoefficient 66 79 3 2) v4269_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4269_upper : Scalar.QComplex := ((999993490714298770631726965653 : Int)/10^30,(-3608119874901386409999796309 : Int)/10^30)
theorem v4269_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 79 5) 1) 14) v4269_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4269 : Material (66 : Basis) (79 : Basis) where
  plus := ![v4269_pa,v4269_pb,v4269_pg]
  minus := ![(Primitive.Addresses.material4269 1).one,v4269_mb,v4269_mg]
  upper := v4269_upper
  lower := (Primitive.Addresses.material4269 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4269_pa_checked.trans (by decide +kernel)
    · exact v4269_pb_checked.trans (by decide +kernel)
    · exact v4269_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 79 Primitive.Addresses.material4269
    · exact v4269_mb_checked.trans (by decide +kernel)
    · exact v4269_mg_checked.trans (by decide +kernel)
  upper_error := v4269_upper_checked
  lower_error := reuse_lower_error 66 79 Primitive.Addresses.material4269

def v4270_pa : Scalar.QComplex := ((999998212193311675892578644559 : Int)/10^30,(-1890928391133693890177788399 : Int)/10^30)
theorem v4270_pa_checked : Scalar.distance (sourceCoefficient 66 80 1 0) v4270_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4270_pb : Scalar.QComplex := ((-815893086300493763317558 : Int)/10^30,(-431476745215198005511122430 : Int)/10^30)
theorem v4270_pb_checked : Scalar.distance (sourceCoefficient 66 80 1 1) v4270_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4270_pg : Scalar.QComplex := ((-93086263003204976122173 : Int)/10^30,(176019772226624342010 : Int)/10^30)
theorem v4270_pg_checked : Scalar.distance (sourceCoefficient 66 80 1 2) v4270_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4270_mb : Scalar.QComplex := ((-1188237780635707506845860 : Int)/10^30,(-431475880477699283663534127 : Int)/10^30)
theorem v4270_mb_checked : Scalar.distance (sourceCoefficient 66 80 3 1) v4270_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4270_mg : Scalar.QComplex := ((-93086076445799212321971 : Int)/10^30,(256348959208529917762 : Int)/10^30)
theorem v4270_mg_checked : Scalar.distance (sourceCoefficient 66 80 3 2) v4270_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4270_upper : Scalar.QComplex := ((999993459242583242501209516999 : Int)/10^30,(-3616831769934484070948783713 : Int)/10^30)
theorem v4270_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 80 5) 1) 14) v4270_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4270 : Material (66 : Basis) (80 : Basis) where
  plus := ![v4270_pa,v4270_pb,v4270_pg]
  minus := ![(Primitive.Addresses.material4270 1).one,v4270_mb,v4270_mg]
  upper := v4270_upper
  lower := (Primitive.Addresses.material4270 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4270_pa_checked.trans (by decide +kernel)
    · exact v4270_pb_checked.trans (by decide +kernel)
    · exact v4270_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 80 Primitive.Addresses.material4270
    · exact v4270_mb_checked.trans (by decide +kernel)
    · exact v4270_mg_checked.trans (by decide +kernel)
  upper_error := v4270_upper_checked
  lower_error := reuse_lower_error 66 80 Primitive.Addresses.material4270

def v4271_pa : Scalar.QComplex := ((999998162246152510846377189660 : Int)/10^30,(-1917160483016250594560450830 : Int)/10^30)
theorem v4271_pa_checked : Scalar.distance (sourceCoefficient 66 81 1 0) v4271_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4271_pb : Scalar.QComplex := ((-827211642280148307590336 : Int)/10^30,(-431476722682770979138615066 : Int)/10^30)
theorem v4271_pb_checked : Scalar.distance (sourceCoefficient 66 81 1 1) v4271_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4271_pg : Scalar.QComplex := ((-93086258247944559790275 : Int)/10^30,(178461623793340588420 : Int)/10^30)
theorem v4271_pg_checked : Scalar.distance (sourceCoefficient 66 81 1 2) v4271_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4271_mb : Scalar.QComplex := ((-1199556312956476675412453 : Int)/10^30,(-431475848177876605539334636 : Int)/10^30)
theorem v4271_mb_checked : Scalar.distance (sourceCoefficient 66 81 3 1) v4271_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4271_mg : Scalar.QComplex := ((-93086069583332641426762 : Int)/10^30,(258790805762457657439 : Int)/10^30)
theorem v4271_mg_checked : Scalar.distance (sourceCoefficient 66 81 3 2) v4271_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4271_upper : Scalar.QComplex := ((999993364021287635374452871652 : Int)/10^30,(-3643063736543155806249116371 : Int)/10^30)
theorem v4271_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 81 5) 1) 14) v4271_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4271 : Material (66 : Basis) (81 : Basis) where
  plus := ![v4271_pa,v4271_pb,v4271_pg]
  minus := ![(Primitive.Addresses.material4271 1).one,v4271_mb,v4271_mg]
  upper := v4271_upper
  lower := (Primitive.Addresses.material4271 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4271_pa_checked.trans (by decide +kernel)
    · exact v4271_pb_checked.trans (by decide +kernel)
    · exact v4271_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 81 Primitive.Addresses.material4271
    · exact v4271_mb_checked.trans (by decide +kernel)
    · exact v4271_mg_checked.trans (by decide +kernel)
  upper_error := v4271_upper_checked
  lower_error := reuse_lower_error 66 81 Primitive.Addresses.material4271

def v4272_pa : Scalar.QComplex := ((999998143139676666447848435975 : Int)/10^30,(-1927100723557760468297305736 : Int)/10^30)
theorem v4272_pa_checked : Scalar.distance (sourceCoefficient 66 82 1 0) v4272_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4272_pb : Scalar.QComplex := ((-831500631807328803730907 : Int)/10^30,(-431476714041031533481780449 : Int)/10^30)
theorem v4272_pb_checked : Scalar.distance (sourceCoefficient 66 82 1 1) v4272_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4272_pg : Scalar.QComplex := ((-93086256426488626271985 : Int)/10^30,(179386925209233407845 : Int)/10^30)
theorem v4272_pg_checked : Scalar.distance (sourceCoefficient 66 82 1 2) v4272_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4272_mb : Scalar.QComplex := ((-1203845293429238421973571 : Int)/10^30,(-431475835834935584557811397 : Int)/10^30)
theorem v4272_mb_checked : Scalar.distance (sourceCoefficient 66 82 3 1) v4272_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4272_mg : Scalar.QComplex := ((-93086066963383938233017 : Int)/10^30,(259716105261984036067 : Int)/10^30)
theorem v4272_mg_checked : Scalar.distance (sourceCoefficient 66 82 3 2) v4272_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4272_upper : Scalar.QComplex := ((999993327758886844758920754514 : Int)/10^30,(-3653003929303801074601593460 : Int)/10^30)
theorem v4272_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 82 5) 1) 14) v4272_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4272 : Material (66 : Basis) (82 : Basis) where
  plus := ![v4272_pa,v4272_pb,v4272_pg]
  minus := ![(Primitive.Addresses.material4272 1).one,v4272_mb,v4272_mg]
  upper := v4272_upper
  lower := (Primitive.Addresses.material4272 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4272_pa_checked.trans (by decide +kernel)
    · exact v4272_pb_checked.trans (by decide +kernel)
    · exact v4272_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 82 Primitive.Addresses.material4272
    · exact v4272_mb_checked.trans (by decide +kernel)
    · exact v4272_mg_checked.trans (by decide +kernel)
  upper_error := v4272_upper_checked
  lower_error := reuse_lower_error 66 82 Primitive.Addresses.material4272

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
