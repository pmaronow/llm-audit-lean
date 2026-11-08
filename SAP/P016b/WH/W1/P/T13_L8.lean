import SAP.P016b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016b.WH.W1.P.T13_L8

open SAP.P016b.WH.W1

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def internalScale : ℕ := 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def outputScale : ℕ := 100000000000000000000
def rescaleFactor : ℕ := 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def coefficients : List ℕ := [1]

theorem internalScale_eq : (10 : ℕ)^600 = internalScale := by decide +kernel
theorem outputScale_eq : (10 : ℕ)^20 = outputScale := by decide +kernel
theorem scale_factor : internalScale = rescaleFactor * outputScale := by norm_num [internalScale, rescaleFactor, outputScale]
theorem coefficients_eq : (List.range 1).map (Nat.fast_choose 1000) = coefficients := by decide +kernel

def rowAt (j : ℕ) : NatBounds := mixtureRowBounds internalScale 6435 1000 0 (j+1) coefficients
def rawBlock (i : ℕ) : NatBounds := boundsSum ((List.range 32).map fun j => rowAt (i*32+j))
def rawFinal : NatBounds := boundsSum ((List.range 3).map fun j => rowAt (201*32+j))
def outputBlock (i : ℕ) : NatBounds := boundsRescale internalScale outputScale (rawBlock i)
def outputFinal : NatBounds := boundsRescale internalScale outputScale rawFinal

theorem block_000 : outputBlock 0 = (⟨590110431579941315874, 590110431579941315875⟩ : NatBounds) := by decide +kernel
theorem block_001 : outputBlock 1 = (⟨4014385359182846322, 4014385359182846323⟩ : NatBounds) := by decide +kernel
theorem block_002 : outputBlock 2 = (⟨26634452837220226, 26634452837220227⟩ : NatBounds) := by decide +kernel
theorem block_003 : outputBlock 3 = (⟨172305076883631, 172305076883632⟩ : NatBounds) := by decide +kernel
theorem block_004 : outputBlock 4 = (⟨1086603019295, 1086603019296⟩ : NatBounds) := by decide +kernel
theorem block_005 : outputBlock 5 = (⟨6678048197, 6678048198⟩ : NatBounds) := by decide +kernel
theorem block_006 : outputBlock 6 = (⟨39987065, 39987066⟩ : NatBounds) := by decide +kernel
theorem block_007 : outputBlock 7 = (⟨233219, 233220⟩ : NatBounds) := by decide +kernel
theorem block_008 : outputBlock 8 = (⟨1324, 1325⟩ : NatBounds) := by decide +kernel
theorem block_009 : outputBlock 9 = (⟨7, 8⟩ : NatBounds) := by decide +kernel
theorem block_010 : outputBlock 10 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_011 : outputBlock 11 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_012 : outputBlock 12 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_013 : outputBlock 13 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_014 : outputBlock 14 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_015 : outputBlock 15 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_016 : outputBlock 16 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_017 : outputBlock 17 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_018 : outputBlock 18 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_019 : outputBlock 19 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_020 : outputBlock 20 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_021 : outputBlock 21 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_022 : outputBlock 22 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_023 : outputBlock 23 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_024 : outputBlock 24 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_025 : outputBlock 25 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_026 : outputBlock 26 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_027 : outputBlock 27 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_028 : outputBlock 28 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_029 : outputBlock 29 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_030 : outputBlock 30 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_031 : outputBlock 31 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_032 : outputBlock 32 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_033 : outputBlock 33 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_034 : outputBlock 34 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_035 : outputBlock 35 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_036 : outputBlock 36 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_037 : outputBlock 37 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_038 : outputBlock 38 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_039 : outputBlock 39 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_040 : outputBlock 40 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_041 : outputBlock 41 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_042 : outputBlock 42 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_043 : outputBlock 43 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_044 : outputBlock 44 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_045 : outputBlock 45 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_046 : outputBlock 46 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_047 : outputBlock 47 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_048 : outputBlock 48 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_049 : outputBlock 49 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_050 : outputBlock 50 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_051 : outputBlock 51 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_052 : outputBlock 52 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_053 : outputBlock 53 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_054 : outputBlock 54 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_055 : outputBlock 55 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_056 : outputBlock 56 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_057 : outputBlock 57 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_058 : outputBlock 58 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_059 : outputBlock 59 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_060 : outputBlock 60 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_061 : outputBlock 61 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_062 : outputBlock 62 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_063 : outputBlock 63 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_064 : outputBlock 64 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_065 : outputBlock 65 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_066 : outputBlock 66 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_067 : outputBlock 67 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_068 : outputBlock 68 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_069 : outputBlock 69 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_070 : outputBlock 70 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_071 : outputBlock 71 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_072 : outputBlock 72 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_073 : outputBlock 73 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_074 : outputBlock 74 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_075 : outputBlock 75 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_076 : outputBlock 76 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_077 : outputBlock 77 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_078 : outputBlock 78 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_079 : outputBlock 79 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_080 : outputBlock 80 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_081 : outputBlock 81 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_082 : outputBlock 82 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_083 : outputBlock 83 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_084 : outputBlock 84 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_085 : outputBlock 85 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_086 : outputBlock 86 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_087 : outputBlock 87 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_088 : outputBlock 88 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_089 : outputBlock 89 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_090 : outputBlock 90 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_091 : outputBlock 91 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_092 : outputBlock 92 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_093 : outputBlock 93 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_094 : outputBlock 94 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_095 : outputBlock 95 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_096 : outputBlock 96 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_097 : outputBlock 97 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_098 : outputBlock 98 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_099 : outputBlock 99 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_100 : outputBlock 100 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_101 : outputBlock 101 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_102 : outputBlock 102 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_103 : outputBlock 103 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_104 : outputBlock 104 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_105 : outputBlock 105 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_106 : outputBlock 106 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_107 : outputBlock 107 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_108 : outputBlock 108 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_109 : outputBlock 109 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_110 : outputBlock 110 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_111 : outputBlock 111 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_112 : outputBlock 112 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_113 : outputBlock 113 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_114 : outputBlock 114 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_115 : outputBlock 115 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_116 : outputBlock 116 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_117 : outputBlock 117 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_118 : outputBlock 118 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_119 : outputBlock 119 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_120 : outputBlock 120 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_121 : outputBlock 121 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_122 : outputBlock 122 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_123 : outputBlock 123 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_124 : outputBlock 124 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_125 : outputBlock 125 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_126 : outputBlock 126 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_127 : outputBlock 127 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_128 : outputBlock 128 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_129 : outputBlock 129 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_130 : outputBlock 130 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_131 : outputBlock 131 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_132 : outputBlock 132 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_133 : outputBlock 133 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_134 : outputBlock 134 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_135 : outputBlock 135 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_136 : outputBlock 136 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_137 : outputBlock 137 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_138 : outputBlock 138 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_139 : outputBlock 139 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_140 : outputBlock 140 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_141 : outputBlock 141 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_142 : outputBlock 142 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_143 : outputBlock 143 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_144 : outputBlock 144 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_145 : outputBlock 145 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_146 : outputBlock 146 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_147 : outputBlock 147 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_148 : outputBlock 148 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_149 : outputBlock 149 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_150 : outputBlock 150 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_151 : outputBlock 151 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_152 : outputBlock 152 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_153 : outputBlock 153 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_154 : outputBlock 154 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_155 : outputBlock 155 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_156 : outputBlock 156 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_157 : outputBlock 157 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_158 : outputBlock 158 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_159 : outputBlock 159 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_160 : outputBlock 160 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_161 : outputBlock 161 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_162 : outputBlock 162 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_163 : outputBlock 163 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_164 : outputBlock 164 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_165 : outputBlock 165 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_166 : outputBlock 166 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_167 : outputBlock 167 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_168 : outputBlock 168 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_169 : outputBlock 169 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_170 : outputBlock 170 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_171 : outputBlock 171 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_172 : outputBlock 172 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_173 : outputBlock 173 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_174 : outputBlock 174 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_175 : outputBlock 175 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_176 : outputBlock 176 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_177 : outputBlock 177 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_178 : outputBlock 178 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_179 : outputBlock 179 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_180 : outputBlock 180 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_181 : outputBlock 181 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_182 : outputBlock 182 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_183 : outputBlock 183 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_184 : outputBlock 184 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_185 : outputBlock 185 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_186 : outputBlock 186 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_187 : outputBlock 187 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_188 : outputBlock 188 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_189 : outputBlock 189 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_190 : outputBlock 190 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_191 : outputBlock 191 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_192 : outputBlock 192 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_193 : outputBlock 193 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_194 : outputBlock 194 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_195 : outputBlock 195 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_196 : outputBlock 196 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_197 : outputBlock 197 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_198 : outputBlock 198 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_199 : outputBlock 199 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_200 : outputBlock 200 = (⟨0, 1⟩ : NatBounds) := by decide +kernel
theorem block_final : outputFinal = (⟨0, 1⟩ : NatBounds) := by decide +kernel

def cachedBlocks : List NatBounds := [
  ⟨590110431579941315874, 590110431579941315875⟩,
  ⟨4014385359182846322, 4014385359182846323⟩,
  ⟨26634452837220226, 26634452837220227⟩,
  ⟨172305076883631, 172305076883632⟩,
  ⟨1086603019295, 1086603019296⟩,
  ⟨6678048197, 6678048198⟩,
  ⟨39987065, 39987066⟩,
  ⟨233219, 233220⟩,
  ⟨1324, 1325⟩,
  ⟨7, 8⟩,
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
  ⟨0, 1⟩
]

def rawBlocks : List NatBounds := (List.range 201).map rawBlock ++ [rawFinal]

theorem outputBlocks_eq : (List.range 201).map outputBlock ++ [outputFinal] = cachedBlocks := by
  simp [cachedBlocks, List.range_succ, block_000, block_001, block_002, block_003, block_004, block_005, block_006, block_007, block_008, block_009, block_010, block_011, block_012, block_013, block_014, block_015, block_016, block_017, block_018, block_019, block_020, block_021, block_022, block_023, block_024, block_025, block_026, block_027, block_028, block_029, block_030, block_031, block_032, block_033, block_034, block_035, block_036, block_037, block_038, block_039, block_040, block_041, block_042, block_043, block_044, block_045, block_046, block_047, block_048, block_049, block_050, block_051, block_052, block_053, block_054, block_055, block_056, block_057, block_058, block_059, block_060, block_061, block_062, block_063, block_064, block_065, block_066, block_067, block_068, block_069, block_070, block_071, block_072, block_073, block_074, block_075, block_076, block_077, block_078, block_079, block_080, block_081, block_082, block_083, block_084, block_085, block_086, block_087, block_088, block_089, block_090, block_091, block_092, block_093, block_094, block_095, block_096, block_097, block_098, block_099, block_100, block_101, block_102, block_103, block_104, block_105, block_106, block_107, block_108, block_109, block_110, block_111, block_112, block_113, block_114, block_115, block_116, block_117, block_118, block_119, block_120, block_121, block_122, block_123, block_124, block_125, block_126, block_127, block_128, block_129, block_130, block_131, block_132, block_133, block_134, block_135, block_136, block_137, block_138, block_139, block_140, block_141, block_142, block_143, block_144, block_145, block_146, block_147, block_148, block_149, block_150, block_151, block_152, block_153, block_154, block_155, block_156, block_157, block_158, block_159, block_160, block_161, block_162, block_163, block_164, block_165, block_166, block_167, block_168, block_169, block_170, block_171, block_172, block_173, block_174, block_175, block_176, block_177, block_178, block_179, block_180, block_181, block_182, block_183, block_184, block_185, block_186, block_187, block_188, block_189, block_190, block_191, block_192, block_193, block_194, block_195, block_196, block_197, block_198, block_199, block_200, block_final]

def blockRel (raw out : NatBounds) : Prop :=
  out.lo * rescaleFactor ≤ raw.lo ∧ raw.hi ≤ out.hi * rescaleFactor

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

lemma rescaleBounds (a b : NatBounds)
    (h : boundsRescale internalScale outputScale a = b) :
    b.lo * rescaleFactor ≤ a.lo ∧ a.hi ≤ b.hi * rescaleFactor := by
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
    rw [← hlo, scale_factor] at hd
    have hh : (b.lo * rescaleFactor) * outputScale ≤ a.lo * outputScale := by
      simpa [Nat.mul_assoc] using hd
    exact Nat.le_of_mul_le_mul_right hh hO
  · have ht := Nat.lt_mul_div_succ (a.hi * outputScale + internalScale - 1) hSpos
    rw [← hhi, scale_factor] at ht
    have ht' : a.hi * outputScale + rescaleFactor * outputScale - 1 <
        (rescaleFactor * outputScale) * (b.hi + 1) := by simpa [scale_factor] using ht
    have ht'' : a.hi * outputScale + rescaleFactor * outputScale - 1 <
        (b.hi * rescaleFactor) * outputScale + rescaleFactor * outputScale := by
      simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ht'
    have hh : a.hi * outputScale ≤ (b.hi * rescaleFactor) * outputScale := by omega
    exact Nat.le_of_mul_le_mul_right hh hO

theorem blockRelAll : List.Forall₂ blockRel rawBlocks cachedBlocks := by
  have hprefix : List.Forall₂ blockRel
      ((List.range 201).map rawBlock) ((List.range 201).map outputBlock) := by
    apply List.rel_map (R := Eq)
    · intro i j hij
      subst j
      exact rescaleBounds (rawBlock i) (outputBlock i) rfl
    · exact List.forall₂_refl (List.range 201)
  have hlast : List.Forall₂ blockRel [rawFinal] [outputFinal] :=
    List.Forall₂.cons (rescaleBounds rawFinal outputFinal rfl) List.Forall₂.nil
  have hfull := List.rel_append hprefix hlast
  have hraw : List.Forall₂ blockRel rawBlocks
      ((List.range 201).map outputBlock ++ [outputFinal]) := by
    simpa [rawBlocks] using hfull
  rw [outputBlocks_eq] at hraw
  exact hraw

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
theorem allRows_sum_eq_rawBlocks : boundsSum allRows = boundsSum rawBlocks := by
  unfold allRows rawBlocks
  rw [show 6435 = 201*32+3 by norm_num, List.range_add, List.map_append, sumAppend]
  rw [sumRangeGroup rowAt 201 32]
  rw [sumAppend]
  have hmap : (List.range 201).map rawBlock =
      (List.range 201).map (fun i =>
        boundsSum ((List.range 32).map fun j => rowAt (i*32+j))) := rfl
  rw [hmap]
  rw [rawFinal]
  simp only [List.map_map]
  have htail : (List.range 3).map (rowAt ∘ fun x => 6432 + x) =
      (List.range 3).map (fun j => rowAt (6432+j)) := rfl
  rw [htail]
  simp [boundsSum, boundsZero, boundsAdd]

theorem blockTotals : boundsSum cachedBlocks = (⟨594151624790359555160, 594151624790359555362⟩ : NatBounds) := by decide +kernel

def coarseRows : NatBounds := ⟨594151624790359555160 * rescaleFactor, 594151624790359555362 * rescaleFactor⟩

theorem rowSum_bounds : coarseRows.lo ≤ (boundsSum allRows).lo ∧
    (boundsSum allRows).hi ≤ coarseRows.hi := by
  have hb := sumBlockRel blockRelAll
  have hL : (cachedBlocks.map NatBounds.lo).sum = 594151624790359555160 := by
    have h := congrArg NatBounds.lo blockTotals
    simpa [sumLower] using h
  have hH : (cachedBlocks.map NatBounds.hi).sum = 594151624790359555362 := by
    have h := congrArg NatBounds.hi blockTotals
    simpa [sumUpper] using h
  constructor
  · change 594151624790359555160 * rescaleFactor ≤ (boundsSum allRows).lo
    rw [allRows_sum_eq_rawBlocks, sumLower]
    calc
      594151624790359555160 * rescaleFactor = (cachedBlocks.map NatBounds.lo).sum * rescaleFactor := by rw [hL]
      _ ≤ (rawBlocks.map NatBounds.lo).sum := hb.1
  · change (boundsSum allRows).hi ≤ 594151624790359555362 * rescaleFactor
    rw [allRows_sum_eq_rawBlocks, sumUpper]
    calc
      (rawBlocks.map NatBounds.hi).sum ≤ (cachedBlocks.map NatBounds.hi).sum * rescaleFactor := hb.2
      _ = 594151624790359555362 * rescaleFactor := by rw [hH]

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
        (⟨184662509647353397, 184662509647353398⟩ : NatBounds) := by decide +kernel

end SAP.P016b.WH.W1.P.T13_L8

open SAP.P016b.WH.W1.P.T13_L8

theorem SAP.P016b.WH.W1.T13_L8_proof : SAP.P016b.WH.W1.T13_L8 := by
  unfold SAP.P016b.WH.W1.T13_L8 SAP.P016b.WH.W1.PrefixCertificate
  have hmixture : mixtureBounds (10^600) (10^20) 6435 1000 0 =
      boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows)) := by
    simp only [mixtureBounds, allRows]
    rw [internalScale_eq, outputScale_eq]
    rfl
  rw [hmixture]
  have hrow := rowSum_bounds
  have hm := boundsMulMono internalScale (boundsRatio internalScale 2 6435)
    coarseRows (boundsSum allRows) hrow.1 hrow.2
  have hr := boundsRescaleMono internalScale outputScale
    (boundsMul internalScale (boundsRatio internalScale 2 6435) coarseRows)
    (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows)) hm.1 hm.2
  have hlo : 184662509647353397 ≤
      (boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows))).lo := by
    calc
      184662509647353397 = (boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) coarseRows)).lo := by rw [candidateBounds]
      _ ≤ _ := hr.1
  have hhi : (boundsRescale internalScale outputScale
      (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows))).hi ≤
        184662509647353398 := by
    calc
      _ ≤ (boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) coarseRows)).hi := hr.2
      _ = 184662509647353398 := by rw [candidateBounds]
  constructor
  · calc
      1846625 * 10^20 < 184662509647353397 * 10^9 := by norm_num
      _ ≤ (boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows))).lo * 10^9 := Nat.mul_le_mul_right _ hlo
  · calc
      (boundsRescale internalScale outputScale
        (boundsMul internalScale (boundsRatio internalScale 2 6435) (boundsSum allRows))).hi * 10^9 ≤
          184662509647353398 * 10^9 := Nat.mul_le_mul_right _ hhi
      _ < 1846626 * 10^20 := by norm_num
