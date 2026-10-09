import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B123
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B124

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2961_pa : Scalar.QComplex := ((999998977647063565952978967388 : Int)/10^30,(-1429931756295581893021217009 : Int)/10^30)
theorem v2961_pa_checked : Scalar.distance (sourceCoefficient 37 76 1 0) v2961_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2961_pb : Scalar.QComplex := ((-616983367411153127871248 : Int)/10^30,(-431477050509576151218438918 : Int)/10^30)
theorem v2961_pb_checked : Scalar.distance (sourceCoefficient 37 76 1 1) v2961_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2961_pg : Scalar.QComplex := ((-93086331561800384664168 : Int)/10^30,(133107237659853362837 : Int)/10^30)
theorem v2961_pg_checked : Scalar.distance (sourceCoefficient 37 76 1 2) v2961_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2961_mb : Scalar.QComplex := ((-989328399264844228516018 : Int)/10^30,(-431476357422092594640840150 : Int)/10^30)
theorem v2961_mb_checked : Scalar.distance (sourceCoefficient 37 76 3 1) v2961_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2961_mg : Scalar.QComplex := ((-93086182035953715677605 : Int)/10^30,(213436499783036830571 : Int)/10^30)
theorem v2961_mg_checked : Scalar.distance (sourceCoefficient 37 76 3 2) v2961_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2961_upper : Scalar.QComplex := ((999995020333565521673450966230 : Int)/10^30,(-3155837142800441536747899218 : Int)/10^30)
theorem v2961_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 76 5) 1) 14) v2961_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2961 : Material (37 : Basis) (76 : Basis) where
  plus := ![v2961_pa,v2961_pb,v2961_pg]
  minus := ![(Primitive.Addresses.material2961 1).one,v2961_mb,v2961_mg]
  upper := v2961_upper
  lower := (Primitive.Addresses.material2961 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2961_pa_checked.trans (by decide +kernel)
    · exact v2961_pb_checked.trans (by decide +kernel)
    · exact v2961_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 76 Primitive.Addresses.material2961
    · exact v2961_mb_checked.trans (by decide +kernel)
    · exact v2961_mg_checked.trans (by decide +kernel)
  upper_error := v2961_upper_checked
  lower_error := reuse_lower_error 37 76 Primitive.Addresses.material2961

def v2962_pa : Scalar.QComplex := ((999998973528017787184643041031 : Int)/10^30,(-1432809446779612926073567578 : Int)/10^30)
theorem v2962_pa_checked : Scalar.distance (sourceCoefficient 37 77 1 0) v2962_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2962_pb : Scalar.QComplex := ((-618225025703068379650924 : Int)/10^30,(-431477048467208184754314348 : Int)/10^30)
theorem v2962_pb_checked : Scalar.distance (sourceCoefficient 37 77 1 1) v2962_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2962_pg : Scalar.QComplex := ((-93086331149777774436287 : Int)/10^30,(133375111543272066696 : Int)/10^30)
theorem v2962_pg_checked : Scalar.distance (sourceCoefficient 37 77 1 2) v2962_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2962_mb : Scalar.QComplex := ((-990570055331961781408400 : Int)/10^30,(-431476354308230204934325753 : Int)/10^30)
theorem v2962_mb_checked : Scalar.distance (sourceCoefficient 37 77 3 1) v2962_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2962_mg : Scalar.QComplex := ((-93086181392768162066080 : Int)/10^30,(213704373211156889375 : Int)/10^30)
theorem v2962_mg_checked : Scalar.distance (sourceCoefficient 37 77 3 2) v2962_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2962_upper : Scalar.QComplex := ((999995011247893164343788902284 : Int)/10^30,(-3158714821889391293866001623 : Int)/10^30)
theorem v2962_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 77 5) 1) 14) v2962_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2962 : Material (37 : Basis) (77 : Basis) where
  plus := ![v2962_pa,v2962_pb,v2962_pg]
  minus := ![(Primitive.Addresses.material2962 1).one,v2962_mb,v2962_mg]
  upper := v2962_upper
  lower := (Primitive.Addresses.material2962 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2962_pa_checked.trans (by decide +kernel)
    · exact v2962_pb_checked.trans (by decide +kernel)
    · exact v2962_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 77 Primitive.Addresses.material2962
    · exact v2962_mb_checked.trans (by decide +kernel)
    · exact v2962_mg_checked.trans (by decide +kernel)
  upper_error := v2962_upper_checked
  lower_error := reuse_lower_error 37 77 Primitive.Addresses.material2962

def v2963_pa : Scalar.QComplex := ((999998948591365140916006495850 : Int)/10^30,(-1450109018059694203888511917 : Int)/10^30)
theorem v2963_pa_checked : Scalar.distance (sourceCoefficient 37 78 1 0) v2963_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2963_pb : Scalar.QComplex := ((-625689398973372580445789 : Int)/10^30,(-431477036088868100457447322 : Int)/10^30)
theorem v2963_pb_checked : Scalar.distance (sourceCoefficient 37 78 1 1) v2963_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2963_pg : Scalar.QComplex := ((-93086328653901853821243 : Int)/10^30,(134985466563976719242 : Int)/10^30)
theorem v2963_pg_checked : Scalar.distance (sourceCoefficient 37 78 1 2) v2963_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2963_mb : Scalar.QComplex := ((-998034415140988681951801 : Int)/10^30,(-431476335488476780279063836 : Int)/10^30)
theorem v2963_mb_checked : Scalar.distance (sourceCoefficient 37 78 3 1) v2963_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2963_mg : Scalar.QComplex := ((-93086177507229315609372 : Int)/10^30,(215314725478424261440 : Int)/10^30)
theorem v2963_mg_checked : Scalar.distance (sourceCoefficient 37 78 3 2) v2963_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2963_upper : Scalar.QComplex := ((999994956453787033716729567461 : Int)/10^30,(-3176014324365393068390009513 : Int)/10^30)
theorem v2963_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 78 5) 1) 14) v2963_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2963 : Material (37 : Basis) (78 : Basis) where
  plus := ![v2963_pa,v2963_pb,v2963_pg]
  minus := ![(Primitive.Addresses.material2963 1).one,v2963_mb,v2963_mg]
  upper := v2963_upper
  lower := (Primitive.Addresses.material2963 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2963_pa_checked.trans (by decide +kernel)
    · exact v2963_pb_checked.trans (by decide +kernel)
    · exact v2963_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 78 Primitive.Addresses.material2963
    · exact v2963_mb_checked.trans (by decide +kernel)
    · exact v2963_mg_checked.trans (by decide +kernel)
  upper_error := v2963_upper_checked
  lower_error := reuse_lower_error 37 78 Primitive.Addresses.material2963

def v2964_pa : Scalar.QComplex := ((999998940488437686753655763962 : Int)/10^30,(-1455686093243231479424741590 : Int)/10^30)
theorem v2964_pa_checked : Scalar.distance (sourceCoefficient 37 79 1 0) v2964_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2964_pb : Scalar.QComplex := ((-628095780600692218878314 : Int)/10^30,(-431477032061610576528845924 : Int)/10^30)
theorem v2964_pb_checked : Scalar.distance (sourceCoefficient 37 79 1 1) v2964_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2964_pg : Scalar.QComplex := ((-93086327842347765873339 : Int)/10^30,(135504616479893771756 : Int)/10^30)
theorem v2964_pg_checked : Scalar.distance (sourceCoefficient 37 79 1 2) v2964_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2964_mb : Scalar.QComplex := ((-1000440792396960601255196 : Int)/10^30,(-431476329384621790910907229 : Int)/10^30)
theorem v2964_mb_checked : Scalar.distance (sourceCoefficient 37 79 3 1) v2964_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2964_mg : Scalar.QComplex := ((-93086176247672534047973 : Int)/10^30,(215833874500703447075 : Int)/10^30)
theorem v2964_mg_checked : Scalar.distance (sourceCoefficient 37 79 3 2) v2964_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2964_upper : Scalar.QComplex := ((999994938725345829436046722828 : Int)/10^30,(-3181591377257614293271048805 : Int)/10^30)
theorem v2964_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 79 5) 1) 14) v2964_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2964 : Material (37 : Basis) (79 : Basis) where
  plus := ![v2964_pa,v2964_pb,v2964_pg]
  minus := ![(Primitive.Addresses.material2964 1).one,v2964_mb,v2964_mg]
  upper := v2964_upper
  lower := (Primitive.Addresses.material2964 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2964_pa_checked.trans (by decide +kernel)
    · exact v2964_pb_checked.trans (by decide +kernel)
    · exact v2964_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 79 Primitive.Addresses.material2964
    · exact v2964_mb_checked.trans (by decide +kernel)
    · exact v2964_mg_checked.trans (by decide +kernel)
  upper_error := v2964_upper_checked
  lower_error := reuse_lower_error 37 79 Primitive.Addresses.material2964

def v2965_pa : Scalar.QComplex := ((999998927768621479501551291224 : Int)/10^30,(-1464398035836182011043851445 : Int)/10^30)
theorem v2965_pa_checked : Scalar.distance (sourceCoefficient 37 80 1 0) v2965_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2965_pb : Scalar.QComplex := ((-631854786489048472321113 : Int)/10^30,(-431477025734827896908017558 : Int)/10^30)
theorem v2965_pb_checked : Scalar.distance (sourceCoefficient 37 80 1 1) v2965_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2965_pg : Scalar.QComplex := ((-93086326567860467133474 : Int)/10^30,(136315579951022478681 : Int)/10^30)
theorem v2965_pg_checked : Scalar.distance (sourceCoefficient 37 80 1 2) v2965_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2965_mb : Scalar.QComplex := ((-1004199791425938662608375 : Int)/10^30,(-431476319813988684729496650 : Int)/10^30)
theorem v2965_mb_checked : Scalar.distance (sourceCoefficient 37 80 3 1) v2965_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2965_mg : Scalar.QComplex := ((-93086174273360758712791 : Int)/10^30,(216644836570048252802 : Int)/10^30)
theorem v2965_mg_checked : Scalar.distance (sourceCoefficient 37 80 3 2) v2965_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2965_upper : Scalar.QComplex := ((999994910969525992681616177347 : Int)/10^30,(-3190303284921900868350761540 : Int)/10^30)
theorem v2965_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 80 5) 1) 14) v2965_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2965 : Material (37 : Basis) (80 : Basis) where
  plus := ![v2965_pa,v2965_pb,v2965_pg]
  minus := ![(Primitive.Addresses.material2965 1).one,v2965_mb,v2965_mg]
  upper := v2965_upper
  lower := (Primitive.Addresses.material2965 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2965_pa_checked.trans (by decide +kernel)
    · exact v2965_pb_checked.trans (by decide +kernel)
    · exact v2965_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 80 Primitive.Addresses.material2965
    · exact v2965_mb_checked.trans (by decide +kernel)
    · exact v2965_mg_checked.trans (by decide +kernel)
  upper_error := v2965_upper_checked
  lower_error := reuse_lower_error 37 80 Primitive.Addresses.material2965

def v2966_pa : Scalar.QComplex := ((999998889010265820034400274967 : Int)/10^30,(-1490630146636563145749713848 : Int)/10^30)
theorem v2966_pa_checked : Scalar.distance (sourceCoefficient 37 81 1 0) v2966_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2966_pb : Scalar.QComplex := ((-643173347910446849152034 : Int)/10^30,(-431477006420878906577682783 : Int)/10^30)
theorem v2966_pb_checked : Scalar.distance (sourceCoefficient 37 81 1 1) v2966_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2966_pg : Scalar.QComplex := ((-93086322680538182095318 : Int)/10^30,(138757432985232651885 : Int)/10^30)
theorem v2966_pg_checked : Scalar.distance (sourceCoefficient 37 81 1 2) v2966_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2966_mb : Scalar.QComplex := ((-1015518331965851227757812 : Int)/10^30,(-431476290732638148281164762 : Int)/10^30)
theorem v2966_mb_checked : Scalar.distance (sourceCoefficient 37 81 3 1) v2966_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2966_mg : Scalar.QComplex := ((-93086168278830729557125 : Int)/10^30,(219086685340460889681 : Int)/10^30)
theorem v2966_mg_checked : Scalar.distance (sourceCoefficient 37 81 3 2) v2966_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2966_upper : Scalar.QComplex := ((999994826936984576276662485167 : Int)/10^30,(-3216535289759228668401523776 : Int)/10^30)
theorem v2966_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 81 5) 1) 14) v2966_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2966 : Material (37 : Basis) (81 : Basis) where
  plus := ![v2966_pa,v2966_pb,v2966_pg]
  minus := ![(Primitive.Addresses.material2966 1).one,v2966_mb,v2966_mg]
  upper := v2966_upper
  lower := (Primitive.Addresses.material2966 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2966_pa_checked.trans (by decide +kernel)
    · exact v2966_pb_checked.trans (by decide +kernel)
    · exact v2966_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 81 Primitive.Addresses.material2966
    · exact v2966_mb_checked.trans (by decide +kernel)
    · exact v2966_mg_checked.trans (by decide +kernel)
  upper_error := v2966_upper_checked
  lower_error := reuse_lower_error 37 81 Primitive.Addresses.material2966

def v2967_pa : Scalar.QComplex := ((999998874143611913744199553145 : Int)/10^30,(-1500570394423368931962493846 : Int)/10^30)
theorem v2967_pa_checked : Scalar.distance (sourceCoefficient 37 82 1 0) v2967_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2967_pb : Scalar.QComplex := ((-647462339521748826829829 : Int)/10^30,(-431476998998731328271287804 : Int)/10^30)
theorem v2967_pb_checked : Scalar.distance (sourceCoefficient 37 82 1 1) v2967_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2967_pg : Scalar.QComplex := ((-93086321187973816321783 : Int)/10^30,(139682734963157737632 : Int)/10^30)
theorem v2967_pg_checked : Scalar.distance (sourceCoefficient 37 82 1 2) v2967_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2967_mb : Scalar.QComplex := ((-1019807315575186532987237 : Int)/10^30,(-431476279609286742037317625 : Int)/10^30)
theorem v2967_mb_checked : Scalar.distance (sourceCoefficient 37 82 3 1) v2967_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2967_mg : Scalar.QComplex := ((-93086165987772986638241 : Int)/10^30,(220011985685837935598 : Int)/10^30)
theorem v2967_mg_checked : Scalar.distance (sourceCoefficient 37 82 3 2) v2967_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2967_upper : Scalar.QComplex := ((999994794914386904329269235384 : Int)/10^30,(-3226475497082707089746098685 : Int)/10^30)
theorem v2967_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 82 5) 1) 14) v2967_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2967 : Material (37 : Basis) (82 : Basis) where
  plus := ![v2967_pa,v2967_pb,v2967_pg]
  minus := ![(Primitive.Addresses.material2967 1).one,v2967_mb,v2967_mg]
  upper := v2967_upper
  lower := (Primitive.Addresses.material2967 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2967_pa_checked.trans (by decide +kernel)
    · exact v2967_pb_checked.trans (by decide +kernel)
    · exact v2967_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 82 Primitive.Addresses.material2967
    · exact v2967_mb_checked.trans (by decide +kernel)
    · exact v2967_mg_checked.trans (by decide +kernel)
  upper_error := v2967_upper_checked
  lower_error := reuse_lower_error 37 82 Primitive.Addresses.material2967

def v2968_pa : Scalar.QComplex := ((999998853690887588780345108688 : Int)/10^30,(-1514138999827247733779580556 : Int)/10^30)
theorem v2968_pa_checked : Scalar.distance (sourceCoefficient 37 83 1 0) v2968_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2968_pb : Scalar.QComplex := ((-653316885136287108635975 : Int)/10^30,(-431476988775619023371637331 : Int)/10^30)
theorem v2968_pb_checked : Scalar.distance (sourceCoefficient 37 83 1 1) v2968_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2968_pg : Scalar.QComplex := ((-93086319133277430722350 : Int)/10^30,(140945787717501499641 : Int)/10^30)
theorem v2968_pg_checked : Scalar.distance (sourceCoefficient 37 83 1 2) v2968_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2968_mb : Scalar.QComplex := ((-1025661850187724429305950 : Int)/10^30,(-431476264333969057269316600 : Int)/10^30)
theorem v2968_mb_checked : Scalar.distance (sourceCoefficient 37 83 3 1) v2968_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2968_mg : Scalar.QComplex := ((-93086162843119724881865 : Int)/10^30,(221275036196778992121 : Int)/10^30)
theorem v2968_mg_checked : Scalar.distance (sourceCoefficient 37 83 3 2) v2968_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2968_upper : Scalar.QComplex := ((999994751043511048467648197682 : Int)/10^30,(-3240044046978195294609553886 : Int)/10^30)
theorem v2968_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 83 5) 1) 14) v2968_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2968 : Material (37 : Basis) (83 : Basis) where
  plus := ![v2968_pa,v2968_pb,v2968_pg]
  minus := ![(Primitive.Addresses.material2968 1).one,v2968_mb,v2968_mg]
  upper := v2968_upper
  lower := (Primitive.Addresses.material2968 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2968_pa_checked.trans (by decide +kernel)
    · exact v2968_pb_checked.trans (by decide +kernel)
    · exact v2968_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 83 Primitive.Addresses.material2968
    · exact v2968_mb_checked.trans (by decide +kernel)
    · exact v2968_mg_checked.trans (by decide +kernel)
  upper_error := v2968_upper_checked
  lower_error := reuse_lower_error 37 83 Primitive.Addresses.material2968

def v2969_pa : Scalar.QComplex := ((999998799868094734289498028539 : Int)/10^30,(-1549278015791494721369337698 : Int)/10^30)
theorem v2969_pa_checked : Scalar.distance (sourceCoefficient 37 84 1 0) v2969_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2969_pb : Scalar.QComplex := ((-668478573512409774625363 : Int)/10^30,(-431476961808196818831792979 : Int)/10^30)
theorem v2969_pb_checked : Scalar.distance (sourceCoefficient 37 84 1 1) v2969_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2969_pg : Scalar.QComplex := ((-93086313719232354594014 : Int)/10^30,(144216752495402839131 : Int)/10^30)
theorem v2969_pg_checked : Scalar.distance (sourceCoefficient 37 84 1 2) v2969_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2969_mb : Scalar.QComplex := ((-1040823509646786794566308 : Int)/10^30,(-431476224282702682434983973 : Int)/10^30)
theorem v2969_mb_checked : Scalar.distance (sourceCoefficient 37 84 3 1) v2969_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2969_mg : Scalar.QComplex := ((-93086154606381380105956 : Int)/10^30,(224545995084673593162 : Int)/10^30)
theorem v2969_mg_checked : Scalar.distance (sourceCoefficient 37 84 3 2) v2969_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2969_upper : Scalar.QComplex := ((999994636574044589040641844068 : Int)/10^30,(-3275182917713748020999497971 : Int)/10^30)
theorem v2969_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 84 5) 1) 14) v2969_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2969 : Material (37 : Basis) (84 : Basis) where
  plus := ![v2969_pa,v2969_pb,v2969_pg]
  minus := ![(Primitive.Addresses.material2969 1).one,v2969_mb,v2969_mg]
  upper := v2969_upper
  lower := (Primitive.Addresses.material2969 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2969_pa_checked.trans (by decide +kernel)
    · exact v2969_pb_checked.trans (by decide +kernel)
    · exact v2969_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 84 Primitive.Addresses.material2969
    · exact v2969_mb_checked.trans (by decide +kernel)
    · exact v2969_mg_checked.trans (by decide +kernel)
  upper_error := v2969_upper_checked
  lower_error := reuse_lower_error 37 84 Primitive.Addresses.material2969

def v2970_pa : Scalar.QComplex := ((999998674262119154482755236549 : Int)/10^30,(-1628334733434776849894471786 : Int)/10^30)
theorem v2970_pa_checked : Scalar.distance (sourceCoefficient 37 85 1 0) v2970_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2970_pb : Scalar.QComplex := ((-702589752016014746217276 : Int)/10^30,(-431476898539245025107057762 : Int)/10^30)
theorem v2970_pb_checked : Scalar.distance (sourceCoefficient 37 85 1 1) v2970_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2970_pg : Scalar.QComplex := ((-93086301048343485943199 : Int)/10^30,(151575858153840755227 : Int)/10^30)
theorem v2970_pg_checked : Scalar.distance (sourceCoefficient 37 85 1 2) v2970_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2970_mb : Scalar.QComplex := ((-1074934620850985181219292 : Int)/10^30,(-431476131577363708470722765 : Int)/10^30)
theorem v2970_mb_checked : Scalar.distance (sourceCoefficient 37 85 3 1) v2970_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2970_mg : Scalar.QComplex := ((-93086135584920487989391 : Int)/10^30,(231905087068573726883 : Int)/10^30)
theorem v2970_mg_checked : Scalar.distance (sourceCoefficient 37 85 3 2) v2970_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2970_upper : Scalar.QComplex := ((999994374523533401675105112264 : Int)/10^30,(-3354239300826816908608377837 : Int)/10^30)
theorem v2970_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 85 5) 1) 14) v2970_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2970 : Material (37 : Basis) (85 : Basis) where
  plus := ![v2970_pa,v2970_pb,v2970_pg]
  minus := ![(Primitive.Addresses.material2970 1).one,v2970_mb,v2970_mg]
  upper := v2970_upper
  lower := (Primitive.Addresses.material2970 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2970_pa_checked.trans (by decide +kernel)
    · exact v2970_pb_checked.trans (by decide +kernel)
    · exact v2970_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 85 Primitive.Addresses.material2970
    · exact v2970_mb_checked.trans (by decide +kernel)
    · exact v2970_mg_checked.trans (by decide +kernel)
  upper_error := v2970_upper_checked
  lower_error := reuse_lower_error 37 85 Primitive.Addresses.material2970

def v2971_pa : Scalar.QComplex := ((999998650407080810761349094822 : Int)/10^30,(-1642919358026263496031805291 : Int)/10^30)
theorem v2971_pa_checked : Scalar.distance (sourceCoefficient 37 86 1 0) v2971_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2971_pb : Scalar.QComplex := ((-708882686032650257509753 : Int)/10^30,(-431476886474341828590849917 : Int)/10^30)
theorem v2971_pb_checked : Scalar.distance (sourceCoefficient 37 86 1 1) v2971_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2971_pg : Scalar.QComplex := ((-93086298636619614779861 : Int)/10^30,(152933488395069189334 : Int)/10^30)
theorem v2971_pg_checked : Scalar.distance (sourceCoefficient 37 86 1 2) v2971_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2971_mb : Scalar.QComplex := ((-1081227542113005681301173 : Int)/10^30,(-431476114081946371139866580 : Int)/10^30)
theorem v2971_mb_checked : Scalar.distance (sourceCoefficient 37 86 3 1) v2971_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2971_mg : Scalar.QComplex := ((-93086132001623762037174 : Int)/10^30,(233262714723085294610 : Int)/10^30)
theorem v2971_mg_checked : Scalar.distance (sourceCoefficient 37 86 3 2) v2971_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2971_upper : Scalar.QComplex := ((999994325496791649132547549328 : Int)/10^30,(-3368823862524586386989015078 : Int)/10^30)
theorem v2971_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 86 5) 1) 14) v2971_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2971 : Material (37 : Basis) (86 : Basis) where
  plus := ![v2971_pa,v2971_pb,v2971_pg]
  minus := ![(Primitive.Addresses.material2971 1).one,v2971_mb,v2971_mg]
  upper := v2971_upper
  lower := (Primitive.Addresses.material2971 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2971_pa_checked.trans (by decide +kernel)
    · exact v2971_pb_checked.trans (by decide +kernel)
    · exact v2971_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 86 Primitive.Addresses.material2971
    · exact v2971_mb_checked.trans (by decide +kernel)
    · exact v2971_mg_checked.trans (by decide +kernel)
  upper_error := v2971_upper_checked
  lower_error := reuse_lower_error 37 86 Primitive.Addresses.material2971

def v2972_pa : Scalar.QComplex := ((999998648819954517542346832556 : Int)/10^30,(-1643885113162534845989611020 : Int)/10^30)
theorem v2972_pa_checked : Scalar.distance (sourceCoefficient 37 87 1 0) v2972_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2972_pb : Scalar.QComplex := ((-709299387419659241892270 : Int)/10^30,(-431476885671116031547827678 : Int)/10^30)
theorem v2972_pb_checked : Scalar.distance (sourceCoefficient 37 87 1 1) v2972_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2972_pg : Scalar.QComplex := ((-93086298476106181412975 : Int)/10^30,(153023387066422401307 : Int)/10^30)
theorem v2972_pg_checked : Scalar.distance (sourceCoefficient 37 87 1 2) v2972_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2972_mb : Scalar.QComplex := ((-1081644242651710008204913 : Int)/10^30,(-431476112919126343719551573 : Int)/10^30)
theorem v2972_mb_checked : Scalar.distance (sourceCoefficient 37 87 3 1) v2972_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2972_mg : Scalar.QComplex := ((-93086131763531883944809 : Int)/10^30,(233352613222449258927 : Int)/10^30)
theorem v2972_mg_checked : Scalar.distance (sourceCoefficient 37 87 3 2) v2972_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2972_upper : Scalar.QComplex := ((999994322242861967168942354216 : Int)/10^30,(-3369789613483242907914657607 : Int)/10^30)
theorem v2972_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 87 5) 1) 14) v2972_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2972 : Material (37 : Basis) (87 : Basis) where
  plus := ![v2972_pa,v2972_pb,v2972_pg]
  minus := ![(Primitive.Addresses.material2972 1).one,v2972_mb,v2972_mg]
  upper := v2972_upper
  lower := (Primitive.Addresses.material2972 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2972_pa_checked.trans (by decide +kernel)
    · exact v2972_pb_checked.trans (by decide +kernel)
    · exact v2972_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 87 Primitive.Addresses.material2972
    · exact v2972_mb_checked.trans (by decide +kernel)
    · exact v2972_mg_checked.trans (by decide +kernel)
  upper_error := v2972_upper_checked
  lower_error := reuse_lower_error 37 87 Primitive.Addresses.material2972

def v2973_pa : Scalar.QComplex := ((999998629419389808485356223201 : Int)/10^30,(-1655644690714713781402629102 : Int)/10^30)
theorem v2973_pa_checked : Scalar.distance (sourceCoefficient 37 88 1 0) v2973_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2973_pb : Scalar.QComplex := ((-714373377769453764494379 : Int)/10^30,(-431476875847541471677867693 : Int)/10^30)
theorem v2973_pb_checked : Scalar.distance (sourceCoefficient 37 88 1 1) v2973_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2973_pg : Scalar.QComplex := ((-93086296513478576708015 : Int)/10^30,(154118043832038934772 : Int)/10^30)
theorem v2973_pg_checked : Scalar.distance (sourceCoefficient 37 88 1 2) v2973_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2973_mb : Scalar.QComplex := ((-1086718222634923622970151 : Int)/10^30,(-431476098716930293784830303 : Int)/10^30)
theorem v2973_mb_checked : Scalar.distance (sourceCoefficient 37 88 3 1) v2973_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2973_mg : Scalar.QComplex := ((-93086128856265522799300 : Int)/10^30,(234447267886815820873 : Int)/10^30)
theorem v2973_mg_checked : Scalar.distance (sourceCoefficient 37 88 3 2) v2973_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2973_upper : Scalar.QComplex := ((999994282546362118455281874650 : Int)/10^30,(-3381549140037297774022504695 : Int)/10^30)
theorem v2973_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 88 5) 1) 14) v2973_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2973 : Material (37 : Basis) (88 : Basis) where
  plus := ![v2973_pa,v2973_pb,v2973_pg]
  minus := ![(Primitive.Addresses.material2973 1).one,v2973_mb,v2973_mg]
  upper := v2973_upper
  lower := (Primitive.Addresses.material2973 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2973_pa_checked.trans (by decide +kernel)
    · exact v2973_pb_checked.trans (by decide +kernel)
    · exact v2973_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 88 Primitive.Addresses.material2973
    · exact v2973_mb_checked.trans (by decide +kernel)
    · exact v2973_mg_checked.trans (by decide +kernel)
  upper_error := v2973_upper_checked
  lower_error := reuse_lower_error 37 88 Primitive.Addresses.material2973

def v2974_pa : Scalar.QComplex := ((999998602651484596747917107039 : Int)/10^30,(-1671734152975176452925132973 : Int)/10^30)
theorem v2974_pa_checked : Scalar.distance (sourceCoefficient 37 89 1 0) v2974_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2974_pb : Scalar.QComplex := ((-721315614818052265813316 : Int)/10^30,(-431476862278029650822380442 : Int)/10^30)
theorem v2974_pb_checked : Scalar.distance (sourceCoefficient 37 89 1 1) v2974_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2974_pg : Scalar.QComplex := ((-93086293803879308672599 : Int)/10^30,(155615753975269382902 : Int)/10^30)
theorem v2974_pg_checked : Scalar.distance (sourceCoefficient 37 89 1 2) v2974_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2974_mb : Scalar.QComplex := ((-1093660445388732441916239 : Int)/10^30,(-431476079156585619288178184 : Int)/10^30)
theorem v2974_mb_checked : Scalar.distance (sourceCoefficient 37 89 3 1) v2974_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2974_mg : Scalar.QComplex := ((-93086124854210864424476 : Int)/10^30,(235944975134118201450 : Int)/10^30)
theorem v2974_mg_checked : Scalar.distance (sourceCoefficient 37 89 3 2) v2974_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2974_upper : Scalar.QComplex := ((999994228009544537424012974720 : Int)/10^30,(-3397638532135420379520941958 : Int)/10^30)
theorem v2974_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 89 5) 1) 14) v2974_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2974 : Material (37 : Basis) (89 : Basis) where
  plus := ![v2974_pa,v2974_pb,v2974_pg]
  minus := ![(Primitive.Addresses.material2974 1).one,v2974_mb,v2974_mg]
  upper := v2974_upper
  lower := (Primitive.Addresses.material2974 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2974_pa_checked.trans (by decide +kernel)
    · exact v2974_pb_checked.trans (by decide +kernel)
    · exact v2974_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 89 Primitive.Addresses.material2974
    · exact v2974_mb_checked.trans (by decide +kernel)
    · exact v2974_mg_checked.trans (by decide +kernel)
  upper_error := v2974_upper_checked
  lower_error := reuse_lower_error 37 89 Primitive.Addresses.material2974

def v2975_pa : Scalar.QComplex := ((999998558503835487763763649895 : Int)/10^30,(-1697937057465111151642603311 : Int)/10^30)
theorem v2975_pa_checked : Scalar.distance (sourceCoefficient 37 90 1 0) v2975_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2975_pb : Scalar.QComplex := ((-732621571907900127729661 : Int)/10^30,(-431476839860283168124306936 : Int)/10^30)
theorem v2975_pb_checked : Scalar.distance (sourceCoefficient 37 90 1 1) v2975_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2975_pg : Scalar.QComplex := ((-93086289330917248178384 : Int)/10^30,(158054888032398483829 : Int)/10^30)
theorem v2975_pg_checked : Scalar.distance (sourceCoefficient 37 90 1 2) v2975_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2975_mb : Scalar.QComplex := ((-1104966378923350214770220 : Int)/10^30,(-431476046982315716607839062 : Int)/10^30)
theorem v2975_mb_checked : Scalar.distance (sourceCoefficient 37 90 3 1) v2975_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2975_mg : Scalar.QComplex := ((-93086118276387632635989 : Int)/10^30,(238384104423081415500 : Int)/10^30)
theorem v2975_mg_checked : Scalar.distance (sourceCoefficient 37 90 3 2) v2975_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2975_upper : Scalar.QComplex := ((999994138638125140476341183343 : Int)/10^30,(-3423841321404369531195268060 : Int)/10^30)
theorem v2975_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 90 5) 1) 14) v2975_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2975 : Material (37 : Basis) (90 : Basis) where
  plus := ![v2975_pa,v2975_pb,v2975_pg]
  minus := ![(Primitive.Addresses.material2975 1).one,v2975_mb,v2975_mg]
  upper := v2975_upper
  lower := (Primitive.Addresses.material2975 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2975_pa_checked.trans (by decide +kernel)
    · exact v2975_pb_checked.trans (by decide +kernel)
    · exact v2975_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 90 Primitive.Addresses.material2975
    · exact v2975_mb_checked.trans (by decide +kernel)
    · exact v2975_mg_checked.trans (by decide +kernel)
  upper_error := v2975_upper_checked
  lower_error := reuse_lower_error 37 90 Primitive.Addresses.material2975

def v2976_pa : Scalar.QComplex := ((999998533331521599180978160335 : Int)/10^30,(-1712698106989440363206253563 : Int)/10^30)
theorem v2976_pa_checked : Scalar.distance (sourceCoefficient 37 91 1 0) v2976_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2976_pb : Scalar.QComplex := ((-738990628765649648289203 : Int)/10^30,(-431476827057615731158135712 : Int)/10^30)
theorem v2976_pb_checked : Scalar.distance (sourceCoefficient 37 91 1 1) v2976_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2976_pg : Scalar.QComplex := ((-93086286778300961971701 : Int)/10^30,(159428940981274510926 : Int)/10^30)
theorem v2976_pg_checked : Scalar.distance (sourceCoefficient 37 91 1 2) v2976_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2976_mb : Scalar.QComplex := ((-1111335422361483399546317 : Int)/10^30,(-431476028683443830094467608 : Int)/10^30)
theorem v2976_mb_checked : Scalar.distance (sourceCoefficient 37 91 3 1) v2976_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2976_mg : Scalar.QComplex := ((-93086114538026487052535 : Int)/10^30,(239758154657541842983 : Int)/10^30)
theorem v2976_mg_checked : Scalar.distance (sourceCoefficient 37 91 3 2) v2976_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2976_upper : Scalar.QComplex := ((999994087989616376058204509425 : Int)/10^30,(-3438602305498719273734825504 : Int)/10^30)
theorem v2976_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 91 5) 1) 14) v2976_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2976 : Material (37 : Basis) (91 : Basis) where
  plus := ![v2976_pa,v2976_pb,v2976_pg]
  minus := ![(Primitive.Addresses.material2976 1).one,v2976_mb,v2976_mg]
  upper := v2976_upper
  lower := (Primitive.Addresses.material2976 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2976_pa_checked.trans (by decide +kernel)
    · exact v2976_pb_checked.trans (by decide +kernel)
    · exact v2976_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 91 Primitive.Addresses.material2976
    · exact v2976_mb_checked.trans (by decide +kernel)
    · exact v2976_mg_checked.trans (by decide +kernel)
  upper_error := v2976_upper_checked
  lower_error := reuse_lower_error 37 91 Primitive.Addresses.material2976

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
