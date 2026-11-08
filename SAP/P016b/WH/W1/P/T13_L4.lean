import SAP.P016b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

namespace SAP.P016b.WH.W1.P.T13_L4

open SAP.P016b.WH.W1

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def internalScale : ℕ := 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def outputScale : ℕ := 100000000000000000000
def rescaleFactor : ℕ := 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def coefficients : List ℕ := [1,1000,499500,166167000,41417124750,8250291250200,1368173298991500,194280608456793000,24115080524699431125,2658017764500203964000,263409560461970212832400,23706860441577319154916000,1953840414726664053684327000,148491871519226468080008852000,10468676942105465999640624066000,688141030994399298376377021938400,42363682220592706806295710413082750,2452109606180189617493822296851378000,133912430159729244110912628766939143000,6921158232466006195627168497322854654000,339482811302457603895512614793686020778700,15842531194114688181790588690372014303006000,704992638138103624089681196721554636483767000,29977513047785449754769922191029584107874962000,1220334593653599350433758915859829319724743244750,47641862536236518640933948075167736642053976275040]

theorem internalScale_eq : (10 : ℕ)^600 = internalScale := by decide +kernel
theorem outputScale_eq : (10 : ℕ)^20 = outputScale := by decide +kernel
theorem scale_factor : internalScale = rescaleFactor * outputScale := by norm_num [internalScale, rescaleFactor, outputScale]
theorem coefficients_eq : (List.range 26).map (Nat.fast_choose 1000) = coefficients := by decide +kernel

@[irreducible] def rowAt (j : ℕ) : NatBounds := mixtureRowBounds internalScale 6435 1000 25 (j+1) coefficients
def rawBlock (i : ℕ) : NatBounds := boundsSum ((List.range 32).map fun j => rowAt (i*32+j))
def rawFinal : NatBounds := boundsSum (List.map rowAt (List.map (fun x => 201*32+x) (List.range 3)))
def outputBlock (i : ℕ) : NatBounds := boundsRescale internalScale outputScale (rawBlock i)
def outputFinal : NatBounds := boundsRescale internalScale outputScale rawFinal

theorem block_000 : outputBlock 0 = (⟨3199999999995675004188, 3199999999995675004189⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_001 : outputBlock 1 = (⟨3199994260498904962264, 3199994260498904962265⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_002 : outputBlock 2 = (⟨3196034133228668227878, 3196034133228668227879⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_003 : outputBlock 3 = (⟨3069928380512623535134, 3069928380512623535135⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_004 : outputBlock 4 = (⟨2369024434813598516490, 2369024434813598516491⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_005 : outputBlock 5 = (⟨1186731100853780323261, 1186731100853780323262⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_006 : outputBlock 6 = (⟨362313609676416228161, 362313609676416228162⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_007 : outputBlock 7 = (⟨70139284947460368410, 70139284947460368411⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_008 : outputBlock 8 = (⟨9189105383898940249, 9189105383898940250⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_009 : outputBlock 9 = (⟨866021038873579010, 866021038873579011⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_010 : outputBlock 10 = (⟨61750467266596494, 61750467266596495⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_011 : outputBlock 11 = (⟨3468208188752525, 3468208188752526⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_012 : outputBlock 12 = (⟨158421392900642, 158421392900643⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_013 : outputBlock 13 = (⟨6037378332423, 6037378332424⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_014 : outputBlock 14 = (⟨195942266793, 195942266794⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_015 : outputBlock 15 = (⟨5506845551, 5506845552⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_016 : outputBlock 16 = (⟨135870113, 135870114⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_017 : outputBlock 17 = (⟨2976612, 2976613⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_018 : outputBlock 18 = (⟨58454, 58455⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_019 : outputBlock 19 = (⟨1037, 1038⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_020 : outputBlock 20 = (⟨16, 17⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_021 : outputBlock 21 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_022 : outputBlock 22 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_023 : outputBlock 23 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_024 : outputBlock 24 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_025 : outputBlock 25 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_026 : outputBlock 26 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_027 : outputBlock 27 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_028 : outputBlock 28 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_029 : outputBlock 29 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_030 : outputBlock 30 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_031 : outputBlock 31 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_032 : outputBlock 32 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_033 : outputBlock 33 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_034 : outputBlock 34 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_035 : outputBlock 35 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_036 : outputBlock 36 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_037 : outputBlock 37 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_038 : outputBlock 38 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_039 : outputBlock 39 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_040 : outputBlock 40 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_041 : outputBlock 41 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_042 : outputBlock 42 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_043 : outputBlock 43 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_044 : outputBlock 44 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_045 : outputBlock 45 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_046 : outputBlock 46 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_047 : outputBlock 47 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_048 : outputBlock 48 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_049 : outputBlock 49 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_050 : outputBlock 50 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_051 : outputBlock 51 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_052 : outputBlock 52 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_053 : outputBlock 53 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_054 : outputBlock 54 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_055 : outputBlock 55 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_056 : outputBlock 56 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_057 : outputBlock 57 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_058 : outputBlock 58 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_059 : outputBlock 59 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_060 : outputBlock 60 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_061 : outputBlock 61 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_062 : outputBlock 62 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_063 : outputBlock 63 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_064 : outputBlock 64 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_065 : outputBlock 65 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_066 : outputBlock 66 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_067 : outputBlock 67 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_068 : outputBlock 68 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_069 : outputBlock 69 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_070 : outputBlock 70 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_071 : outputBlock 71 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_072 : outputBlock 72 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_073 : outputBlock 73 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_074 : outputBlock 74 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_075 : outputBlock 75 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_076 : outputBlock 76 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_077 : outputBlock 77 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_078 : outputBlock 78 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_079 : outputBlock 79 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_080 : outputBlock 80 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_081 : outputBlock 81 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_082 : outputBlock 82 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_083 : outputBlock 83 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_084 : outputBlock 84 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_085 : outputBlock 85 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_086 : outputBlock 86 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_087 : outputBlock 87 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_088 : outputBlock 88 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_089 : outputBlock 89 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_090 : outputBlock 90 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_091 : outputBlock 91 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_092 : outputBlock 92 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_093 : outputBlock 93 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_094 : outputBlock 94 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_095 : outputBlock 95 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_096 : outputBlock 96 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_097 : outputBlock 97 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_098 : outputBlock 98 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_099 : outputBlock 99 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_100 : outputBlock 100 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_101 : outputBlock 101 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_102 : outputBlock 102 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_103 : outputBlock 103 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_104 : outputBlock 104 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_105 : outputBlock 105 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_106 : outputBlock 106 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_107 : outputBlock 107 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_108 : outputBlock 108 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_109 : outputBlock 109 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_110 : outputBlock 110 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_111 : outputBlock 111 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_112 : outputBlock 112 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_113 : outputBlock 113 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_114 : outputBlock 114 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_115 : outputBlock 115 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_116 : outputBlock 116 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_117 : outputBlock 117 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_118 : outputBlock 118 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_119 : outputBlock 119 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_120 : outputBlock 120 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_121 : outputBlock 121 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_122 : outputBlock 122 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_123 : outputBlock 123 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_124 : outputBlock 124 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_125 : outputBlock 125 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_126 : outputBlock 126 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_127 : outputBlock 127 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_128 : outputBlock 128 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_129 : outputBlock 129 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_130 : outputBlock 130 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_131 : outputBlock 131 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_132 : outputBlock 132 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_133 : outputBlock 133 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_134 : outputBlock 134 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_135 : outputBlock 135 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_136 : outputBlock 136 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_137 : outputBlock 137 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_138 : outputBlock 138 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_139 : outputBlock 139 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_140 : outputBlock 140 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_141 : outputBlock 141 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_142 : outputBlock 142 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_143 : outputBlock 143 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_144 : outputBlock 144 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_145 : outputBlock 145 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_146 : outputBlock 146 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_147 : outputBlock 147 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_148 : outputBlock 148 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_149 : outputBlock 149 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_150 : outputBlock 150 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_151 : outputBlock 151 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_152 : outputBlock 152 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_153 : outputBlock 153 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_154 : outputBlock 154 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_155 : outputBlock 155 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_156 : outputBlock 156 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_157 : outputBlock 157 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_158 : outputBlock 158 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_159 : outputBlock 159 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_160 : outputBlock 160 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_161 : outputBlock 161 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_162 : outputBlock 162 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_163 : outputBlock 163 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_164 : outputBlock 164 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_165 : outputBlock 165 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_166 : outputBlock 166 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_167 : outputBlock 167 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_168 : outputBlock 168 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_169 : outputBlock 169 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_170 : outputBlock 170 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_171 : outputBlock 171 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_172 : outputBlock 172 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_173 : outputBlock 173 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_174 : outputBlock 174 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_175 : outputBlock 175 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_176 : outputBlock 176 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_177 : outputBlock 177 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_178 : outputBlock 178 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_179 : outputBlock 179 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_180 : outputBlock 180 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_181 : outputBlock 181 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_182 : outputBlock 182 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_183 : outputBlock 183 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_184 : outputBlock 184 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_185 : outputBlock 185 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_186 : outputBlock 186 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_187 : outputBlock 187 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_188 : outputBlock 188 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_189 : outputBlock 189 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_190 : outputBlock 190 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_191 : outputBlock 191 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_192 : outputBlock 192 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_193 : outputBlock 193 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_194 : outputBlock 194 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_195 : outputBlock 195 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_196 : outputBlock 196 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_197 : outputBlock 197 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_198 : outputBlock 198 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_199 : outputBlock 199 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_200 : outputBlock 200 = (⟨0, 1⟩ : NatBounds) := by unfold outputBlock rawBlock rowAt; decide +kernel
theorem block_final : outputFinal = (⟨0, 1⟩ : NatBounds) := by unfold outputFinal rawFinal rowAt; decide +kernel

def cachedBlocks : List NatBounds :=
  [⟨3199999999995675004188, 3199999999995675004189⟩,
   ⟨3199994260498904962264, 3199994260498904962265⟩,
   ⟨3196034133228668227878, 3196034133228668227879⟩,
   ⟨3069928380512623535134, 3069928380512623535135⟩,
   ⟨2369024434813598516490, 2369024434813598516491⟩,
   ⟨1186731100853780323261, 1186731100853780323262⟩,
   ⟨362313609676416228161, 362313609676416228162⟩,
   ⟨70139284947460368410, 70139284947460368411⟩,
   ⟨9189105383898940249, 9189105383898940250⟩,
   ⟨866021038873579010, 866021038873579011⟩,
   ⟨61750467266596494, 61750467266596495⟩,
   ⟨3468208188752525, 3468208188752526⟩,
   ⟨158421392900642, 158421392900643⟩,
   ⟨6037378332423, 6037378332424⟩,
   ⟨195942266793, 195942266794⟩,
   ⟨5506845551, 5506845552⟩,
   ⟨135870113, 135870114⟩,
   ⟨2976612, 2976613⟩,
   ⟨58454, 58455⟩,
   ⟨1037, 1038⟩,
   ⟨16, 17⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩,
   ⟨0, 1⟩]

def rawBlocks : List NatBounds := (List.range 201).map rawBlock ++ [rawFinal]

theorem outputBlocks_eq : (List.range 201).map outputBlock ++ [outputFinal] = cachedBlocks := by
  simp [cachedBlocks, List.range_succ, block_000, block_001, block_002, block_003, block_004, block_005, block_006, block_007, block_008, block_009, block_010, block_011, block_012, block_013, block_014, block_015, block_016, block_017, block_018, block_019, block_020, block_021, block_022, block_023, block_024, block_025, block_026, block_027, block_028, block_029, block_030, block_031, block_032, block_033, block_034, block_035, block_036, block_037, block_038, block_039, block_040, block_041, block_042, block_043, block_044, block_045, block_046, block_047, block_048, block_049, block_050, block_051, block_052, block_053, block_054, block_055, block_056, block_057, block_058, block_059, block_060, block_061, block_062, block_063, block_064, block_065, block_066, block_067, block_068, block_069, block_070, block_071, block_072, block_073, block_074, block_075, block_076, block_077, block_078, block_079, block_080, block_081, block_082, block_083, block_084, block_085, block_086, block_087, block_088, block_089, block_090, block_091, block_092, block_093, block_094, block_095, block_096, block_097, block_098, block_099, block_100, block_101, block_102, block_103, block_104, block_105, block_106, block_107, block_108, block_109, block_110, block_111, block_112, block_113, block_114, block_115, block_116, block_117, block_118, block_119, block_120, block_121, block_122, block_123, block_124, block_125, block_126, block_127, block_128, block_129, block_130, block_131, block_132, block_133, block_134, block_135, block_136, block_137, block_138, block_139, block_140, block_141, block_142, block_143, block_144, block_145, block_146, block_147, block_148, block_149, block_150, block_151, block_152, block_153, block_154, block_155, block_156, block_157, block_158, block_159, block_160, block_161, block_162, block_163, block_164, block_165, block_166, block_167, block_168, block_169, block_170, block_171, block_172, block_173, block_174, block_175, block_176, block_177, block_178, block_179, block_180, block_181, block_182, block_183, block_184, block_185, block_186, block_187, block_188, block_189, block_190, block_191, block_192, block_193, block_194, block_195, block_196, block_197, block_198, block_199, block_200, block_final]

def blockRel (raw out : NatBounds) : Prop :=
  out.lo * rescaleFactor ≤ raw.lo ∧ raw.hi ≤ out.hi * rescaleFactor

lemma rescaleBounds (a b : NatBounds)
    (h : boundsRescale internalScale outputScale a = b) :
    b.lo * rescaleFactor ≤ a.lo ∧ a.hi ≤ b.hi * rescaleFactor := by
  have hS := scale_factor
  have hO : 0 < outputScale := by norm_num [outputScale]
  have hSpos : 0 < internalScale := by norm_num [internalScale]
  have hlo : b.lo = a.lo * outputScale / internalScale := by
    have hh := congrArg NatBounds.lo h
    simpa [boundsRescale] using hh.symm
  have hhi : b.hi = (a.hi * outputScale + internalScale - 1) / internalScale := by
    have hh := congrArg NatBounds.hi h
    simpa [boundsRescale] using hh.symm
  constructor
  · have hd := Nat.div_mul_le_self (a.lo * outputScale) internalScale
    rw [← hlo, hS] at hd
    have hh : (b.lo * rescaleFactor) * outputScale ≤ a.lo * outputScale := by
      simpa [Nat.mul_assoc] using hd
    exact Nat.le_of_mul_le_mul_right hh hO
  · have ht := Nat.lt_mul_div_succ (a.hi * outputScale + internalScale - 1) hSpos
    rw [← hhi, hS] at ht
    have ht' : a.hi * outputScale + rescaleFactor * outputScale - 1 <
        (rescaleFactor * outputScale) * (b.hi + 1) := by simpa [hS] using ht
    have ht'' : a.hi * outputScale + rescaleFactor * outputScale - 1 <
        (b.hi * rescaleFactor) * outputScale + rescaleFactor * outputScale := by
      simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ht'
    have hh : a.hi * outputScale ≤ (b.hi * rescaleFactor) * outputScale := by omega
    exact Nat.le_of_mul_le_mul_right hh hO


theorem blockRelAll : List.Forall₂ blockRel rawBlocks cachedBlocks := by
  simpa [rawBlocks, cachedBlocks, List.range_succ] using
    (List.Forall₂.cons (by exact rescaleBounds (rawBlock 0) (⟨3199999999995675004188, 3199999999995675004189⟩ : NatBounds) block_000) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 1) (⟨3199994260498904962264, 3199994260498904962265⟩ : NatBounds) block_001) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 2) (⟨3196034133228668227878, 3196034133228668227879⟩ : NatBounds) block_002) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 3) (⟨3069928380512623535134, 3069928380512623535135⟩ : NatBounds) block_003) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 4) (⟨2369024434813598516490, 2369024434813598516491⟩ : NatBounds) block_004) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 5) (⟨1186731100853780323261, 1186731100853780323262⟩ : NatBounds) block_005) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 6) (⟨362313609676416228161, 362313609676416228162⟩ : NatBounds) block_006) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 7) (⟨70139284947460368410, 70139284947460368411⟩ : NatBounds) block_007) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 8) (⟨9189105383898940249, 9189105383898940250⟩ : NatBounds) block_008) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 9) (⟨866021038873579010, 866021038873579011⟩ : NatBounds) block_009) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 10) (⟨61750467266596494, 61750467266596495⟩ : NatBounds) block_010) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 11) (⟨3468208188752525, 3468208188752526⟩ : NatBounds) block_011) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 12) (⟨158421392900642, 158421392900643⟩ : NatBounds) block_012) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 13) (⟨6037378332423, 6037378332424⟩ : NatBounds) block_013) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 14) (⟨195942266793, 195942266794⟩ : NatBounds) block_014) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 15) (⟨5506845551, 5506845552⟩ : NatBounds) block_015) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 16) (⟨135870113, 135870114⟩ : NatBounds) block_016) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 17) (⟨2976612, 2976613⟩ : NatBounds) block_017) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 18) (⟨58454, 58455⟩ : NatBounds) block_018) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 19) (⟨1037, 1038⟩ : NatBounds) block_019) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 20) (⟨16, 17⟩ : NatBounds) block_020) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 21) (⟨0, 1⟩ : NatBounds) block_021) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 22) (⟨0, 1⟩ : NatBounds) block_022) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 23) (⟨0, 1⟩ : NatBounds) block_023) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 24) (⟨0, 1⟩ : NatBounds) block_024) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 25) (⟨0, 1⟩ : NatBounds) block_025) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 26) (⟨0, 1⟩ : NatBounds) block_026) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 27) (⟨0, 1⟩ : NatBounds) block_027) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 28) (⟨0, 1⟩ : NatBounds) block_028) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 29) (⟨0, 1⟩ : NatBounds) block_029) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 30) (⟨0, 1⟩ : NatBounds) block_030) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 31) (⟨0, 1⟩ : NatBounds) block_031) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 32) (⟨0, 1⟩ : NatBounds) block_032) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 33) (⟨0, 1⟩ : NatBounds) block_033) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 34) (⟨0, 1⟩ : NatBounds) block_034) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 35) (⟨0, 1⟩ : NatBounds) block_035) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 36) (⟨0, 1⟩ : NatBounds) block_036) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 37) (⟨0, 1⟩ : NatBounds) block_037) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 38) (⟨0, 1⟩ : NatBounds) block_038) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 39) (⟨0, 1⟩ : NatBounds) block_039) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 40) (⟨0, 1⟩ : NatBounds) block_040) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 41) (⟨0, 1⟩ : NatBounds) block_041) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 42) (⟨0, 1⟩ : NatBounds) block_042) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 43) (⟨0, 1⟩ : NatBounds) block_043) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 44) (⟨0, 1⟩ : NatBounds) block_044) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 45) (⟨0, 1⟩ : NatBounds) block_045) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 46) (⟨0, 1⟩ : NatBounds) block_046) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 47) (⟨0, 1⟩ : NatBounds) block_047) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 48) (⟨0, 1⟩ : NatBounds) block_048) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 49) (⟨0, 1⟩ : NatBounds) block_049) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 50) (⟨0, 1⟩ : NatBounds) block_050) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 51) (⟨0, 1⟩ : NatBounds) block_051) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 52) (⟨0, 1⟩ : NatBounds) block_052) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 53) (⟨0, 1⟩ : NatBounds) block_053) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 54) (⟨0, 1⟩ : NatBounds) block_054) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 55) (⟨0, 1⟩ : NatBounds) block_055) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 56) (⟨0, 1⟩ : NatBounds) block_056) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 57) (⟨0, 1⟩ : NatBounds) block_057) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 58) (⟨0, 1⟩ : NatBounds) block_058) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 59) (⟨0, 1⟩ : NatBounds) block_059) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 60) (⟨0, 1⟩ : NatBounds) block_060) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 61) (⟨0, 1⟩ : NatBounds) block_061) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 62) (⟨0, 1⟩ : NatBounds) block_062) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 63) (⟨0, 1⟩ : NatBounds) block_063) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 64) (⟨0, 1⟩ : NatBounds) block_064) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 65) (⟨0, 1⟩ : NatBounds) block_065) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 66) (⟨0, 1⟩ : NatBounds) block_066) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 67) (⟨0, 1⟩ : NatBounds) block_067) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 68) (⟨0, 1⟩ : NatBounds) block_068) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 69) (⟨0, 1⟩ : NatBounds) block_069) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 70) (⟨0, 1⟩ : NatBounds) block_070) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 71) (⟨0, 1⟩ : NatBounds) block_071) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 72) (⟨0, 1⟩ : NatBounds) block_072) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 73) (⟨0, 1⟩ : NatBounds) block_073) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 74) (⟨0, 1⟩ : NatBounds) block_074) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 75) (⟨0, 1⟩ : NatBounds) block_075) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 76) (⟨0, 1⟩ : NatBounds) block_076) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 77) (⟨0, 1⟩ : NatBounds) block_077) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 78) (⟨0, 1⟩ : NatBounds) block_078) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 79) (⟨0, 1⟩ : NatBounds) block_079) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 80) (⟨0, 1⟩ : NatBounds) block_080) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 81) (⟨0, 1⟩ : NatBounds) block_081) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 82) (⟨0, 1⟩ : NatBounds) block_082) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 83) (⟨0, 1⟩ : NatBounds) block_083) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 84) (⟨0, 1⟩ : NatBounds) block_084) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 85) (⟨0, 1⟩ : NatBounds) block_085) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 86) (⟨0, 1⟩ : NatBounds) block_086) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 87) (⟨0, 1⟩ : NatBounds) block_087) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 88) (⟨0, 1⟩ : NatBounds) block_088) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 89) (⟨0, 1⟩ : NatBounds) block_089) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 90) (⟨0, 1⟩ : NatBounds) block_090) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 91) (⟨0, 1⟩ : NatBounds) block_091) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 92) (⟨0, 1⟩ : NatBounds) block_092) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 93) (⟨0, 1⟩ : NatBounds) block_093) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 94) (⟨0, 1⟩ : NatBounds) block_094) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 95) (⟨0, 1⟩ : NatBounds) block_095) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 96) (⟨0, 1⟩ : NatBounds) block_096) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 97) (⟨0, 1⟩ : NatBounds) block_097) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 98) (⟨0, 1⟩ : NatBounds) block_098) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 99) (⟨0, 1⟩ : NatBounds) block_099) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 100) (⟨0, 1⟩ : NatBounds) block_100) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 101) (⟨0, 1⟩ : NatBounds) block_101) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 102) (⟨0, 1⟩ : NatBounds) block_102) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 103) (⟨0, 1⟩ : NatBounds) block_103) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 104) (⟨0, 1⟩ : NatBounds) block_104) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 105) (⟨0, 1⟩ : NatBounds) block_105) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 106) (⟨0, 1⟩ : NatBounds) block_106) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 107) (⟨0, 1⟩ : NatBounds) block_107) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 108) (⟨0, 1⟩ : NatBounds) block_108) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 109) (⟨0, 1⟩ : NatBounds) block_109) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 110) (⟨0, 1⟩ : NatBounds) block_110) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 111) (⟨0, 1⟩ : NatBounds) block_111) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 112) (⟨0, 1⟩ : NatBounds) block_112) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 113) (⟨0, 1⟩ : NatBounds) block_113) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 114) (⟨0, 1⟩ : NatBounds) block_114) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 115) (⟨0, 1⟩ : NatBounds) block_115) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 116) (⟨0, 1⟩ : NatBounds) block_116) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 117) (⟨0, 1⟩ : NatBounds) block_117) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 118) (⟨0, 1⟩ : NatBounds) block_118) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 119) (⟨0, 1⟩ : NatBounds) block_119) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 120) (⟨0, 1⟩ : NatBounds) block_120) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 121) (⟨0, 1⟩ : NatBounds) block_121) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 122) (⟨0, 1⟩ : NatBounds) block_122) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 123) (⟨0, 1⟩ : NatBounds) block_123) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 124) (⟨0, 1⟩ : NatBounds) block_124) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 125) (⟨0, 1⟩ : NatBounds) block_125) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 126) (⟨0, 1⟩ : NatBounds) block_126) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 127) (⟨0, 1⟩ : NatBounds) block_127) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 128) (⟨0, 1⟩ : NatBounds) block_128) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 129) (⟨0, 1⟩ : NatBounds) block_129) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 130) (⟨0, 1⟩ : NatBounds) block_130) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 131) (⟨0, 1⟩ : NatBounds) block_131) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 132) (⟨0, 1⟩ : NatBounds) block_132) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 133) (⟨0, 1⟩ : NatBounds) block_133) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 134) (⟨0, 1⟩ : NatBounds) block_134) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 135) (⟨0, 1⟩ : NatBounds) block_135) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 136) (⟨0, 1⟩ : NatBounds) block_136) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 137) (⟨0, 1⟩ : NatBounds) block_137) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 138) (⟨0, 1⟩ : NatBounds) block_138) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 139) (⟨0, 1⟩ : NatBounds) block_139) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 140) (⟨0, 1⟩ : NatBounds) block_140) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 141) (⟨0, 1⟩ : NatBounds) block_141) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 142) (⟨0, 1⟩ : NatBounds) block_142) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 143) (⟨0, 1⟩ : NatBounds) block_143) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 144) (⟨0, 1⟩ : NatBounds) block_144) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 145) (⟨0, 1⟩ : NatBounds) block_145) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 146) (⟨0, 1⟩ : NatBounds) block_146) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 147) (⟨0, 1⟩ : NatBounds) block_147) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 148) (⟨0, 1⟩ : NatBounds) block_148) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 149) (⟨0, 1⟩ : NatBounds) block_149) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 150) (⟨0, 1⟩ : NatBounds) block_150) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 151) (⟨0, 1⟩ : NatBounds) block_151) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 152) (⟨0, 1⟩ : NatBounds) block_152) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 153) (⟨0, 1⟩ : NatBounds) block_153) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 154) (⟨0, 1⟩ : NatBounds) block_154) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 155) (⟨0, 1⟩ : NatBounds) block_155) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 156) (⟨0, 1⟩ : NatBounds) block_156) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 157) (⟨0, 1⟩ : NatBounds) block_157) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 158) (⟨0, 1⟩ : NatBounds) block_158) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 159) (⟨0, 1⟩ : NatBounds) block_159) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 160) (⟨0, 1⟩ : NatBounds) block_160) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 161) (⟨0, 1⟩ : NatBounds) block_161) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 162) (⟨0, 1⟩ : NatBounds) block_162) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 163) (⟨0, 1⟩ : NatBounds) block_163) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 164) (⟨0, 1⟩ : NatBounds) block_164) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 165) (⟨0, 1⟩ : NatBounds) block_165) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 166) (⟨0, 1⟩ : NatBounds) block_166) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 167) (⟨0, 1⟩ : NatBounds) block_167) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 168) (⟨0, 1⟩ : NatBounds) block_168) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 169) (⟨0, 1⟩ : NatBounds) block_169) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 170) (⟨0, 1⟩ : NatBounds) block_170) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 171) (⟨0, 1⟩ : NatBounds) block_171) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 172) (⟨0, 1⟩ : NatBounds) block_172) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 173) (⟨0, 1⟩ : NatBounds) block_173) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 174) (⟨0, 1⟩ : NatBounds) block_174) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 175) (⟨0, 1⟩ : NatBounds) block_175) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 176) (⟨0, 1⟩ : NatBounds) block_176) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 177) (⟨0, 1⟩ : NatBounds) block_177) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 178) (⟨0, 1⟩ : NatBounds) block_178) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 179) (⟨0, 1⟩ : NatBounds) block_179) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 180) (⟨0, 1⟩ : NatBounds) block_180) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 181) (⟨0, 1⟩ : NatBounds) block_181) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 182) (⟨0, 1⟩ : NatBounds) block_182) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 183) (⟨0, 1⟩ : NatBounds) block_183) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 184) (⟨0, 1⟩ : NatBounds) block_184) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 185) (⟨0, 1⟩ : NatBounds) block_185) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 186) (⟨0, 1⟩ : NatBounds) block_186) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 187) (⟨0, 1⟩ : NatBounds) block_187) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 188) (⟨0, 1⟩ : NatBounds) block_188) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 189) (⟨0, 1⟩ : NatBounds) block_189) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 190) (⟨0, 1⟩ : NatBounds) block_190) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 191) (⟨0, 1⟩ : NatBounds) block_191) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 192) (⟨0, 1⟩ : NatBounds) block_192) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 193) (⟨0, 1⟩ : NatBounds) block_193) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 194) (⟨0, 1⟩ : NatBounds) block_194) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 195) (⟨0, 1⟩ : NatBounds) block_195) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 196) (⟨0, 1⟩ : NatBounds) block_196) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 197) (⟨0, 1⟩ : NatBounds) block_197) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 198) (⟨0, 1⟩ : NatBounds) block_198) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 199) (⟨0, 1⟩ : NatBounds) block_199) (List.Forall₂.cons (by exact rescaleBounds (rawBlock 200) (⟨0, 1⟩ : NatBounds) block_200) (List.Forall₂.cons (by exact rescaleBounds rawFinal (⟨0, 1⟩ : NatBounds) block_final) List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

lemma foldLower (acc : NatBounds) (xs : List NatBounds) :
    (xs.foldl boundsAdd acc).lo = acc.lo + (xs.map NatBounds.lo).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, boundsAdd, List.map_cons, List.sum_cons]
    rw [ih]
    dsimp
    omega

lemma foldUpper (acc : NatBounds) (xs : List NatBounds) :
    (xs.foldl boundsAdd acc).hi = acc.hi + (xs.map NatBounds.hi).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, boundsAdd, List.map_cons, List.sum_cons]
    rw [ih]
    dsimp
    omega

lemma sumLower (xs : List NatBounds) :
    (boundsSum xs).lo = (xs.map NatBounds.lo).sum := by
  simpa [boundsSum, boundsZero] using foldLower boundsZero xs

lemma sumUpper (xs : List NatBounds) :
    (boundsSum xs).hi = (xs.map NatBounds.hi).sum := by
  simpa [boundsSum, boundsZero] using foldUpper boundsZero xs

lemma bounds_ext {a b : NatBounds} (hlo : a.lo = b.lo) (hhi : a.hi = b.hi) : a = b := by
  cases a
  cases b
  simp_all

lemma sumAppend (xs ys : List NatBounds) :
    boundsSum (xs ++ ys) = boundsAdd (boundsSum xs) (boundsSum ys) := by
  apply bounds_ext
  · simp [sumLower, boundsAdd, List.map_append, List.sum_append]
  · simp [sumUpper, boundsAdd, List.map_append, List.sum_append]

lemma sumRangeGroup (f : ℕ → NatBounds) (n m : ℕ) :
    boundsSum ((List.range (n*m)).map f) =
      boundsSum ((List.range n).map fun i =>
        boundsSum ((List.range m).map fun j => f (i*m+j))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, sumAppend, ih]
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, sumAppend]
    apply bounds_ext
    · simp only [boundsAdd, sumLower]
      simp only [Nat.add_left_cancel_iff]
      calc
        _ = ((List.range m).map fun j => (f (n*m+j)).lo).sum := by
          apply congrArg List.sum
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro j hj
          rfl
        _ = (boundsSum ((List.range m).map fun j => f (n*m+j))).lo := by
          rw [sumLower, List.map_map]
          rfl
        _ = (List.map NatBounds.lo [boundsSum ((List.range m).map fun j => f (n*m+j))]).sum := by simp
    · simp only [boundsAdd, sumUpper]
      simp only [Nat.add_left_cancel_iff]
      calc
        _ = ((List.range m).map fun j => (f (n*m+j)).hi).sum := by
          apply congrArg List.sum
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro j hj
          rfl
        _ = (boundsSum ((List.range m).map fun j => f (n*m+j))).hi := by
          rw [sumUpper, List.map_map]
          rfl
        _ = (List.map NatBounds.hi [boundsSum ((List.range m).map fun j => f (n*m+j))]).sum := by simp


lemma sumBlockRel {xs ys : List NatBounds}
    (h : List.Forall₂ blockRel xs ys) :
    (ys.map NatBounds.lo).sum * rescaleFactor ≤ (xs.map NatBounds.lo).sum ∧
      (xs.map NatBounds.hi).sum ≤ (ys.map NatBounds.hi).sum * rescaleFactor := by
  induction h with
  | nil => simp
  | cons hxy htail ih =>
    simp only [List.map_cons, List.sum_cons]
    constructor
    · rw [Nat.add_mul]
      exact Nat.add_le_add hxy.1 ih.1
    · rw [Nat.add_mul]
      exact Nat.add_le_add hxy.2 ih.2

def allRows : List NatBounds := (List.range 6435).map rowAt

lemma boundsSum_singleton (a : NatBounds) : boundsSum [a] = a := by
  cases a
  simp [boundsSum, boundsAdd, boundsZero]

theorem rowsEq :
    (List.range 6435).map (fun r =>
      mixtureRowBounds internalScale 6435 1000 25 (r+1) coefficients) = allRows := by
  unfold allRows
  apply List.map_congr_left
  intro r hr
  unfold rowAt
  rfl

theorem allRows_sum_eq_rawBlocks : boundsSum allRows = boundsSum rawBlocks := by
  unfold allRows rawBlocks rawBlock
  rw [show 6435 = 201*32+3 by norm_num, List.range_add, List.map_append, sumAppend]
  rw [sumRangeGroup rowAt 201 32]
  rw [sumAppend, boundsSum_singleton]
  unfold rawFinal
  rfl

theorem blockTotals : boundsSum cachedBlocks = (⟨16664285714285714285705, 16664285714285714285907⟩ : NatBounds) := by decide +kernel

def coarseRows : NatBounds := ⟨16664285714285714285705 * rescaleFactor, 16664285714285714285907 * rescaleFactor⟩

theorem rowSum_bounds : coarseRows.lo ≤ (boundsSum allRows).lo ∧
    (boundsSum allRows).hi ≤ coarseRows.hi := by
  have hb := sumBlockRel blockRelAll
  have hL : (cachedBlocks.map NatBounds.lo).sum = 16664285714285714285705 := by
    have h := congrArg NatBounds.lo blockTotals
    simpa [sumLower] using h
  have hH : (cachedBlocks.map NatBounds.hi).sum = 16664285714285714285907 := by
    have h := congrArg NatBounds.hi blockTotals
    simpa [sumUpper] using h
  constructor
  · change 16664285714285714285705 * rescaleFactor ≤ (boundsSum allRows).lo
    rw [allRows_sum_eq_rawBlocks, sumLower]
    calc
      16664285714285714285705 * rescaleFactor = (cachedBlocks.map NatBounds.lo).sum * rescaleFactor := by rw [hL]
      _ ≤ (rawBlocks.map NatBounds.lo).sum := hb.1
  · change (boundsSum allRows).hi ≤ 16664285714285714285907 * rescaleFactor
    rw [allRows_sum_eq_rawBlocks, sumUpper]
    calc
      (rawBlocks.map NatBounds.hi).sum ≤ (cachedBlocks.map NatBounds.hi).sum * rescaleFactor := hb.2
      _ = 16664285714285714285907 * rescaleFactor := by rw [hH]

lemma boundsMulMono (s : ℕ) (p a b : NatBounds)
    (hlo : a.lo ≤ b.lo) (hhi : b.hi ≤ a.hi) :
    (boundsMul s p a).lo ≤ (boundsMul s p b).lo ∧
      (boundsMul s p b).hi ≤ (boundsMul s p a).hi := by
  constructor
  · apply Nat.div_le_div_right
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left p.lo hlo
  · apply Nat.div_le_div_right
    exact Nat.sub_le_sub_right
      (Nat.add_le_add_right (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left p.hi hhi) s) 1

lemma boundsRescaleMono (s o : ℕ) (a b : NatBounds)
    (hlo : a.lo ≤ b.lo) (hhi : b.hi ≤ a.hi) :
    (boundsRescale s o a).lo ≤ (boundsRescale s o b).lo ∧
      (boundsRescale s o b).hi ≤ (boundsRescale s o a).hi := by
  constructor
  · apply Nat.div_le_div_right
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left o hlo
  · apply Nat.div_le_div_right
    exact Nat.sub_le_sub_right
      (Nat.add_le_add_right (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left o hhi) s) 1

theorem candidateBounds :
    boundsRescale internalScale outputScale
      (boundsMul internalScale (boundsRatio internalScale 2 6435) coarseRows) =
        (⟨5179265179265179265, 5179265179265179266⟩ : NatBounds) := by decide +kernel

end SAP.P016b.WH.W1.P.T13_L4

open SAP.P016b.WH.W1.P.T13_L4

theorem SAP.P016b.WH.W1.T13_L4_proof : SAP.P016b.WH.W1.T13_L4 := by
  unfold SAP.P016b.WH.W1.T13_L4 SAP.P016b.WH.W1.PrefixCertificate
  have hmixture : mixtureBounds (10^600) (10^20) 6435 1000 25 =
      boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows)) := by
    change boundsRescale internalScale outputScale
      (boundsMul internalScale (boundsRatio internalScale 2 6435)
        (boundsSum ((List.range 6435).map fun r =>
          mixtureRowBounds internalScale 6435 1000 25 (r+1)
            ((List.range (25+1)).map (Nat.fast_choose 1000))))) =
      boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows))
    rw [show (List.range (25+1)).map (Nat.fast_choose 1000) = coefficients by
      simpa using coefficients_eq]
    rw [rowsEq]
  rw [hmixture]
  have hrow := rowSum_bounds
  have hm := boundsMulMono internalScale (boundsRatio internalScale 2 6435)
    coarseRows (boundsSum allRows) hrow.1 hrow.2
  have hr := boundsRescaleMono internalScale outputScale
    (boundsMul internalScale (boundsRatio internalScale 2 6435) coarseRows)
    (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows)) hm.1 hm.2
  have hlo : 5179265179265179265 ≤
      (boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows))).lo := by
    calc
      5179265179265179265 = (boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) coarseRows)).lo := by rw [candidateBounds]
      _ ≤ _ := hr.1
  have hhi : (boundsRescale internalScale outputScale
      (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows))).hi ≤
        5179265179265179266 := by
    calc
      _ ≤ (boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) coarseRows)).hi := hr.2
      _ = 5179265179265179266 := by rw [candidateBounds]
  constructor
  · calc
      51792651792 * 10^20 < 5179265179265179265 * 10^12 := by norm_num
      _ ≤ (boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows))).lo * 10^12 :=
          Nat.mul_le_mul_right _ hlo
  · calc
      (boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows))).hi * 10^12 ≤
          5179265179265179266 * 10^12 := Nat.mul_le_mul_right _ hhi
      _ < 51792651793 * 10^20 := by norm_num

