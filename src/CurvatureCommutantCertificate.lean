import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Exact coefficient-space kernel certificate. The 198 explicit equations
are selected necessary generator-covariance equations on a 20-to-10 linear
map. Their semantic origin and tensor-coordinate completeness must still
be proved; this file makes no original-candidate exhaustion claim. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option maxRecDepth 4096

def commutantEquation (i : Fin 198) (x : Fin 200 → ℝ) : ℝ :=
  match i.val with
  | 0 => (-2) * x 3
  | 1 => (-2) * x 4
  | 2 => (-2) * x 5
  | 3 => (-2) * x 8
  | 4 => (-2) * x 9
  | 5 => (-2) * x 10
  | 6 => (-2) * x 12
  | 7 => (-2) * x 13
  | 8 => (2) * x 20
  | 9 => (2) * x 21
  | 10 => (2) * x 22
  | 11 => (2) * x 26
  | 12 => (2) * x 27
  | 13 => (2) * x 31
  | 14 => (2) * x 34
  | 15 => (2) * x 35
  | 16 => (2) * x 36
  | 17 => (2) * x 37
  | 18 => (2) * x 38
  | 19 => (2) * x 39
  | 20 => (2) * x 40
  | 21 => (2) * x 41
  | 22 => (2) * x 42
  | 23 => (2) * x 46
  | 24 => (2) * x 47
  | 25 => (2) * x 51
  | 26 => (2) * x 54
  | 27 => (2) * x 55
  | 28 => (2) * x 56
  | 29 => (2) * x 57
  | 30 => (2) * x 58
  | 31 => (2) * x 59
  | 32 => (2) * x 60
  | 33 => (2) * x 61
  | 34 => (2) * x 62
  | 35 => (2) * x 66
  | 36 => (2) * x 67
  | 37 => (2) * x 71
  | 38 => (2) * x 74
  | 39 => (2) * x 75
  | 40 => (2) * x 76
  | 41 => (2) * x 77
  | 42 => (2) * x 78
  | 43 => (2) * x 79
  | 44 => (-2) * x 83
  | 45 => (-2) * x 84
  | 46 => (-2) * x 85
  | 47 => (-2) * x 88
  | 48 => (-2) * x 89
  | 49 => (-2) * x 90
  | 50 => (-2) * x 92
  | 51 => (-2) * x 93
  | 52 => (-2) * x 103
  | 53 => (-2) * x 104
  | 54 => (-2) * x 105
  | 55 => (-2) * x 108
  | 56 => (-2) * x 109
  | 57 => (-2) * x 110
  | 58 => (-2) * x 112
  | 59 => (-2) * x 113
  | 60 => (-2) * x 123
  | 61 => (-2) * x 124
  | 62 => (-2) * x 125
  | 63 => (-2) * x 128
  | 64 => (-2) * x 129
  | 65 => (-2) * x 130
  | 66 => (-2) * x 132
  | 67 => (-2) * x 133
  | 68 => (-2) * x 143
  | 69 => (-2) * x 144
  | 70 => (-2) * x 145
  | 71 => (-2) * x 148
  | 72 => (-2) * x 149
  | 73 => (-2) * x 150
  | 74 => (-2) * x 152
  | 75 => (-2) * x 153
  | 76 => (-2) * x 163
  | 77 => (-2) * x 164
  | 78 => (-2) * x 165
  | 79 => (-2) * x 168
  | 80 => (-2) * x 169
  | 81 => (-2) * x 170
  | 82 => (-2) * x 172
  | 83 => (-2) * x 173
  | 84 => (-2) * x 183
  | 85 => (-2) * x 184
  | 86 => (-2) * x 185
  | 87 => (-2) * x 188
  | 88 => (-2) * x 189
  | 89 => (-2) * x 190
  | 90 => (-2) * x 192
  | 91 => (-2) * x 193
  | 92 => (-2) * x 1
  | 93 => (-2) * x 2
  | 94 => (-2) * x 16
  | 95 => (-2) * x 18
  | 96 => (2) * x 23
  | 97 => (2) * x 24
  | 98 => (2) * x 30
  | 99 => (2) * x 33
  | 100 => (-2) * x 45
  | 101 => (-2) * x 48
  | 102 => (-2) * x 49
  | 103 => (-2) * x 52
  | 104 => (-2) * x 65
  | 105 => (-2) * x 68
  | 106 => (-2) * x 69
  | 107 => (-2) * x 72
  | 108 => (-2) * x 81
  | 109 => (-2) * x 82
  | 110 => (-2) * x 96
  | 111 => (-2) * x 98
  | 112 => (2) * x 100
  | 113 => (2) * x 106
  | 114 => (2) * x 107
  | 115 => (2) * x 111
  | 116 => (2) * x 114
  | 117 => (2) * x 115
  | 118 => (2) * x 117
  | 119 => (2) * x 119
  | 120 => (2) * x 120
  | 121 => (2) * x 126
  | 122 => (2) * x 127
  | 123 => (2) * x 131
  | 124 => (2) * x 134
  | 125 => (2) * x 135
  | 126 => (2) * x 137
  | 127 => (2) * x 139
  | 128 => (-2) * x 141
  | 129 => (-2) * x 142
  | 130 => (-2) * x 156
  | 131 => (-2) * x 158
  | 132 => (-2) * x 161
  | 133 => (-2) * x 162
  | 134 => (-2) * x 176
  | 135 => (-2) * x 178
  | 136 => (-2) * x 181
  | 137 => (-2) * x 182
  | 138 => (-2) * x 196
  | 139 => (-2) * x 198
  | 140 => (-2) * x 7
  | 141 => (-2) * x 15
  | 142 => (-2) * x 25
  | 143 => (-2) * x 29
  | 144 => (2) * x 44
  | 145 => (2) * x 50
  | 146 => (-2) * x 63
  | 147 => (-2) * x 73
  | 148 => (-2) * x 87
  | 149 => (-2) * x 95
  | 150 => (2) * x 102
  | 151 => (2) * x 116
  | 152 => (-2) * x 121
  | 153 => (-2) * x 138
  | 154 => (-2) * x 147
  | 155 => (-2) * x 155
  | 156 => (2) * x 160
  | 157 => (2) * x 166
  | 158 => (2) * x 171
  | 159 => (2) * x 174
  | 160 => (2) * x 177
  | 161 => (2) * x 179
  | 162 => (-2) * x 187
  | 163 => (-2) * x 195
  | 164 => (-x 0) + x 6
  | 165 => (-x 17) + x 19
  | 166 => (-x 28) + (-x 43)
  | 167 => x 32 + (-x 53)
  | 168 => (-x 64) + x 70
  | 169 => x 86 + (-x 140)
  | 170 => x 80 + (-x 146)
  | 171 => x 91 + (-x 151)
  | 172 => x 94 + (-x 154)
  | 173 => x 99 + (-x 157)
  | 174 => x 97 + (-x 159)
  | 175 => x 122 + (-x 167)
  | 176 => (-x 136) + (-x 175)
  | 177 => (-x 180) + x 186
  | 178 => (-x 197) + x 199
  | 179 => (-x 0) + x 11
  | 180 => (-x 14) + x 19
  | 181 => (-x 32) + (-x 64)
  | 182 => (-x 28) + (-x 70)
  | 183 => x 91 + (-x 180)
  | 184 => x 86 + (-x 186)
  | 185 => x 80 + (-x 191)
  | 186 => x 99 + (-x 194)
  | 187 => x 97 + (-x 197)
  | 188 => x 94 + (-x 199)
  | 189 => x 101 + (-x 167)
  | 190 => x 118 + (-x 175)
  | 191 => ((-9 / 16 : ℝ)) * x 0 + ((-15 / 8 : ℝ)) * x 20 + ((-9 / 16 : ℝ)) * x 80
  | 192 => ((15 / 16 : ℝ)) * x 8 + ((9 / 16 : ℝ)) * x 14 + ((-15 / 8 : ℝ)) * x 26 + ((-9 / 16 : ℝ)) * x 86
  | 193 => ((15 / 8 : ℝ)) * x 6 + ((9 / 16 : ℝ)) * x 8 + ((15 / 8 : ℝ)) * x 14 + ((-15 / 8 : ℝ)) * x 28 + ((-9 / 16 : ℝ)) * x 88
  | 194 => ((9 / 16 : ℝ)) * x 6 + ((15 / 16 : ℝ)) * x 8 + ((-15 / 8 : ℝ)) * x 34 + ((-9 / 16 : ℝ)) * x 94
  | 195 => ((-9 / 16 : ℝ)) * x 19 + ((-15 / 8 : ℝ)) * x 39 + ((-9 / 16 : ℝ)) * x 99
  | 196 => ((3 / 4 : ℝ)) * x 43 + ((-3 / 4 : ℝ)) * x 101
  | 197 => ((3 / 4 : ℝ)) * x 53 + ((-3 / 4 : ℝ)) * x 118
  | _ => 0

def commutantKernelU (i : Fin 200) : ℝ :=
  match i.val with
  | 14 => -1
  | 17 => -1
  | 19 => -1
  | 28 => -1
  | 32 => -1
  | 43 => 1
  | 53 => -1
  | 64 => 1
  | 70 => 1
  | 86 => -1
  | 91 => -1
  | 99 => 1
  | 101 => 1
  | 118 => -1
  | 122 => 1
  | 136 => 1
  | 140 => -1
  | 151 => -1
  | 157 => 1
  | 167 => 1
  | 175 => -1
  | 180 => -1
  | 186 => -1
  | 194 => 1
  | _ => 0

def commutantKernelV (i : Fin 200) : ℝ :=
  match i.val with
  | 0 => 1
  | 6 => 1
  | 11 => 1
  | 28 => 1
  | 32 => 1
  | 43 => -1
  | 53 => 1
  | 64 => -1
  | 70 => -1
  | 80 => -1
  | 94 => 1
  | 97 => 1
  | 101 => -1
  | 118 => 1
  | 122 => -1
  | 136 => -1
  | 146 => -1
  | 154 => 1
  | 159 => 1
  | 167 => -1
  | 175 => 1
  | 191 => -1
  | 197 => 1
  | 199 => 1
  | _ => 0

set_option maxHeartbeats 0 in
theorem commutant_kernel_reconstruction (x : Fin 200 → ℝ)
    (h : ∀ i : Fin 198, commutantEquation i x = 0) :
    ∀ i : Fin 200, x i = commutantKernelU i * x 194 +
      commutantKernelV i * x 199 := by
  have p3 : x 3 = 0 := by
    have original : (-2) * x 3 = 0 := h 0
    linear_combination ((-1 / 2 : ℝ)) * original
  have p4 : x 4 = 0 := by
    have original : (-2) * x 4 = 0 := h 1
    linear_combination ((-1 / 2 : ℝ)) * original
  have p5 : x 5 = 0 := by
    have original : (-2) * x 5 = 0 := h 2
    linear_combination ((-1 / 2 : ℝ)) * original
  have p8 : x 8 = 0 := by
    have original : (-2) * x 8 = 0 := h 3
    linear_combination ((-1 / 2 : ℝ)) * original
  have p9 : x 9 = 0 := by
    have original : (-2) * x 9 = 0 := h 4
    linear_combination ((-1 / 2 : ℝ)) * original
  have p10 : x 10 = 0 := by
    have original : (-2) * x 10 = 0 := h 5
    linear_combination ((-1 / 2 : ℝ)) * original
  have p12 : x 12 = 0 := by
    have original : (-2) * x 12 = 0 := h 6
    linear_combination ((-1 / 2 : ℝ)) * original
  have p13 : x 13 = 0 := by
    have original : (-2) * x 13 = 0 := h 7
    linear_combination ((-1 / 2 : ℝ)) * original
  have p20 : x 20 = 0 := by
    have original : (2) * x 20 = 0 := h 8
    linear_combination ((1 / 2 : ℝ)) * original
  have p21 : x 21 = 0 := by
    have original : (2) * x 21 = 0 := h 9
    linear_combination ((1 / 2 : ℝ)) * original
  have p22 : x 22 = 0 := by
    have original : (2) * x 22 = 0 := h 10
    linear_combination ((1 / 2 : ℝ)) * original
  have p26 : x 26 = 0 := by
    have original : (2) * x 26 = 0 := h 11
    linear_combination ((1 / 2 : ℝ)) * original
  have p27 : x 27 = 0 := by
    have original : (2) * x 27 = 0 := h 12
    linear_combination ((1 / 2 : ℝ)) * original
  have p31 : x 31 = 0 := by
    have original : (2) * x 31 = 0 := h 13
    linear_combination ((1 / 2 : ℝ)) * original
  have p34 : x 34 = 0 := by
    have original : (2) * x 34 = 0 := h 14
    linear_combination ((1 / 2 : ℝ)) * original
  have p35 : x 35 = 0 := by
    have original : (2) * x 35 = 0 := h 15
    linear_combination ((1 / 2 : ℝ)) * original
  have p36 : x 36 = 0 := by
    have original : (2) * x 36 = 0 := h 16
    linear_combination ((1 / 2 : ℝ)) * original
  have p37 : x 37 = 0 := by
    have original : (2) * x 37 = 0 := h 17
    linear_combination ((1 / 2 : ℝ)) * original
  have p38 : x 38 = 0 := by
    have original : (2) * x 38 = 0 := h 18
    linear_combination ((1 / 2 : ℝ)) * original
  have p39 : x 39 = 0 := by
    have original : (2) * x 39 = 0 := h 19
    linear_combination ((1 / 2 : ℝ)) * original
  have p40 : x 40 = 0 := by
    have original : (2) * x 40 = 0 := h 20
    linear_combination ((1 / 2 : ℝ)) * original
  have p41 : x 41 = 0 := by
    have original : (2) * x 41 = 0 := h 21
    linear_combination ((1 / 2 : ℝ)) * original
  have p42 : x 42 = 0 := by
    have original : (2) * x 42 = 0 := h 22
    linear_combination ((1 / 2 : ℝ)) * original
  have p46 : x 46 = 0 := by
    have original : (2) * x 46 = 0 := h 23
    linear_combination ((1 / 2 : ℝ)) * original
  have p47 : x 47 = 0 := by
    have original : (2) * x 47 = 0 := h 24
    linear_combination ((1 / 2 : ℝ)) * original
  have p51 : x 51 = 0 := by
    have original : (2) * x 51 = 0 := h 25
    linear_combination ((1 / 2 : ℝ)) * original
  have p54 : x 54 = 0 := by
    have original : (2) * x 54 = 0 := h 26
    linear_combination ((1 / 2 : ℝ)) * original
  have p55 : x 55 = 0 := by
    have original : (2) * x 55 = 0 := h 27
    linear_combination ((1 / 2 : ℝ)) * original
  have p56 : x 56 = 0 := by
    have original : (2) * x 56 = 0 := h 28
    linear_combination ((1 / 2 : ℝ)) * original
  have p57 : x 57 = 0 := by
    have original : (2) * x 57 = 0 := h 29
    linear_combination ((1 / 2 : ℝ)) * original
  have p58 : x 58 = 0 := by
    have original : (2) * x 58 = 0 := h 30
    linear_combination ((1 / 2 : ℝ)) * original
  have p59 : x 59 = 0 := by
    have original : (2) * x 59 = 0 := h 31
    linear_combination ((1 / 2 : ℝ)) * original
  have p60 : x 60 = 0 := by
    have original : (2) * x 60 = 0 := h 32
    linear_combination ((1 / 2 : ℝ)) * original
  have p61 : x 61 = 0 := by
    have original : (2) * x 61 = 0 := h 33
    linear_combination ((1 / 2 : ℝ)) * original
  have p62 : x 62 = 0 := by
    have original : (2) * x 62 = 0 := h 34
    linear_combination ((1 / 2 : ℝ)) * original
  have p66 : x 66 = 0 := by
    have original : (2) * x 66 = 0 := h 35
    linear_combination ((1 / 2 : ℝ)) * original
  have p67 : x 67 = 0 := by
    have original : (2) * x 67 = 0 := h 36
    linear_combination ((1 / 2 : ℝ)) * original
  have p71 : x 71 = 0 := by
    have original : (2) * x 71 = 0 := h 37
    linear_combination ((1 / 2 : ℝ)) * original
  have p74 : x 74 = 0 := by
    have original : (2) * x 74 = 0 := h 38
    linear_combination ((1 / 2 : ℝ)) * original
  have p75 : x 75 = 0 := by
    have original : (2) * x 75 = 0 := h 39
    linear_combination ((1 / 2 : ℝ)) * original
  have p76 : x 76 = 0 := by
    have original : (2) * x 76 = 0 := h 40
    linear_combination ((1 / 2 : ℝ)) * original
  have p77 : x 77 = 0 := by
    have original : (2) * x 77 = 0 := h 41
    linear_combination ((1 / 2 : ℝ)) * original
  have p78 : x 78 = 0 := by
    have original : (2) * x 78 = 0 := h 42
    linear_combination ((1 / 2 : ℝ)) * original
  have p79 : x 79 = 0 := by
    have original : (2) * x 79 = 0 := h 43
    linear_combination ((1 / 2 : ℝ)) * original
  have p83 : x 83 = 0 := by
    have original : (-2) * x 83 = 0 := h 44
    linear_combination ((-1 / 2 : ℝ)) * original
  have p84 : x 84 = 0 := by
    have original : (-2) * x 84 = 0 := h 45
    linear_combination ((-1 / 2 : ℝ)) * original
  have p85 : x 85 = 0 := by
    have original : (-2) * x 85 = 0 := h 46
    linear_combination ((-1 / 2 : ℝ)) * original
  have p88 : x 88 = 0 := by
    have original : (-2) * x 88 = 0 := h 47
    linear_combination ((-1 / 2 : ℝ)) * original
  have p89 : x 89 = 0 := by
    have original : (-2) * x 89 = 0 := h 48
    linear_combination ((-1 / 2 : ℝ)) * original
  have p90 : x 90 = 0 := by
    have original : (-2) * x 90 = 0 := h 49
    linear_combination ((-1 / 2 : ℝ)) * original
  have p92 : x 92 = 0 := by
    have original : (-2) * x 92 = 0 := h 50
    linear_combination ((-1 / 2 : ℝ)) * original
  have p93 : x 93 = 0 := by
    have original : (-2) * x 93 = 0 := h 51
    linear_combination ((-1 / 2 : ℝ)) * original
  have p103 : x 103 = 0 := by
    have original : (-2) * x 103 = 0 := h 52
    linear_combination ((-1 / 2 : ℝ)) * original
  have p104 : x 104 = 0 := by
    have original : (-2) * x 104 = 0 := h 53
    linear_combination ((-1 / 2 : ℝ)) * original
  have p105 : x 105 = 0 := by
    have original : (-2) * x 105 = 0 := h 54
    linear_combination ((-1 / 2 : ℝ)) * original
  have p108 : x 108 = 0 := by
    have original : (-2) * x 108 = 0 := h 55
    linear_combination ((-1 / 2 : ℝ)) * original
  have p109 : x 109 = 0 := by
    have original : (-2) * x 109 = 0 := h 56
    linear_combination ((-1 / 2 : ℝ)) * original
  have p110 : x 110 = 0 := by
    have original : (-2) * x 110 = 0 := h 57
    linear_combination ((-1 / 2 : ℝ)) * original
  have p112 : x 112 = 0 := by
    have original : (-2) * x 112 = 0 := h 58
    linear_combination ((-1 / 2 : ℝ)) * original
  have p113 : x 113 = 0 := by
    have original : (-2) * x 113 = 0 := h 59
    linear_combination ((-1 / 2 : ℝ)) * original
  have p123 : x 123 = 0 := by
    have original : (-2) * x 123 = 0 := h 60
    linear_combination ((-1 / 2 : ℝ)) * original
  have p124 : x 124 = 0 := by
    have original : (-2) * x 124 = 0 := h 61
    linear_combination ((-1 / 2 : ℝ)) * original
  have p125 : x 125 = 0 := by
    have original : (-2) * x 125 = 0 := h 62
    linear_combination ((-1 / 2 : ℝ)) * original
  have p128 : x 128 = 0 := by
    have original : (-2) * x 128 = 0 := h 63
    linear_combination ((-1 / 2 : ℝ)) * original
  have p129 : x 129 = 0 := by
    have original : (-2) * x 129 = 0 := h 64
    linear_combination ((-1 / 2 : ℝ)) * original
  have p130 : x 130 = 0 := by
    have original : (-2) * x 130 = 0 := h 65
    linear_combination ((-1 / 2 : ℝ)) * original
  have p132 : x 132 = 0 := by
    have original : (-2) * x 132 = 0 := h 66
    linear_combination ((-1 / 2 : ℝ)) * original
  have p133 : x 133 = 0 := by
    have original : (-2) * x 133 = 0 := h 67
    linear_combination ((-1 / 2 : ℝ)) * original
  have p143 : x 143 = 0 := by
    have original : (-2) * x 143 = 0 := h 68
    linear_combination ((-1 / 2 : ℝ)) * original
  have p144 : x 144 = 0 := by
    have original : (-2) * x 144 = 0 := h 69
    linear_combination ((-1 / 2 : ℝ)) * original
  have p145 : x 145 = 0 := by
    have original : (-2) * x 145 = 0 := h 70
    linear_combination ((-1 / 2 : ℝ)) * original
  have p148 : x 148 = 0 := by
    have original : (-2) * x 148 = 0 := h 71
    linear_combination ((-1 / 2 : ℝ)) * original
  have p149 : x 149 = 0 := by
    have original : (-2) * x 149 = 0 := h 72
    linear_combination ((-1 / 2 : ℝ)) * original
  have p150 : x 150 = 0 := by
    have original : (-2) * x 150 = 0 := h 73
    linear_combination ((-1 / 2 : ℝ)) * original
  have p152 : x 152 = 0 := by
    have original : (-2) * x 152 = 0 := h 74
    linear_combination ((-1 / 2 : ℝ)) * original
  have p153 : x 153 = 0 := by
    have original : (-2) * x 153 = 0 := h 75
    linear_combination ((-1 / 2 : ℝ)) * original
  have p163 : x 163 = 0 := by
    have original : (-2) * x 163 = 0 := h 76
    linear_combination ((-1 / 2 : ℝ)) * original
  have p164 : x 164 = 0 := by
    have original : (-2) * x 164 = 0 := h 77
    linear_combination ((-1 / 2 : ℝ)) * original
  have p165 : x 165 = 0 := by
    have original : (-2) * x 165 = 0 := h 78
    linear_combination ((-1 / 2 : ℝ)) * original
  have p168 : x 168 = 0 := by
    have original : (-2) * x 168 = 0 := h 79
    linear_combination ((-1 / 2 : ℝ)) * original
  have p169 : x 169 = 0 := by
    have original : (-2) * x 169 = 0 := h 80
    linear_combination ((-1 / 2 : ℝ)) * original
  have p170 : x 170 = 0 := by
    have original : (-2) * x 170 = 0 := h 81
    linear_combination ((-1 / 2 : ℝ)) * original
  have p172 : x 172 = 0 := by
    have original : (-2) * x 172 = 0 := h 82
    linear_combination ((-1 / 2 : ℝ)) * original
  have p173 : x 173 = 0 := by
    have original : (-2) * x 173 = 0 := h 83
    linear_combination ((-1 / 2 : ℝ)) * original
  have p183 : x 183 = 0 := by
    have original : (-2) * x 183 = 0 := h 84
    linear_combination ((-1 / 2 : ℝ)) * original
  have p184 : x 184 = 0 := by
    have original : (-2) * x 184 = 0 := h 85
    linear_combination ((-1 / 2 : ℝ)) * original
  have p185 : x 185 = 0 := by
    have original : (-2) * x 185 = 0 := h 86
    linear_combination ((-1 / 2 : ℝ)) * original
  have p188 : x 188 = 0 := by
    have original : (-2) * x 188 = 0 := h 87
    linear_combination ((-1 / 2 : ℝ)) * original
  have p189 : x 189 = 0 := by
    have original : (-2) * x 189 = 0 := h 88
    linear_combination ((-1 / 2 : ℝ)) * original
  have p190 : x 190 = 0 := by
    have original : (-2) * x 190 = 0 := h 89
    linear_combination ((-1 / 2 : ℝ)) * original
  have p192 : x 192 = 0 := by
    have original : (-2) * x 192 = 0 := h 90
    linear_combination ((-1 / 2 : ℝ)) * original
  have p193 : x 193 = 0 := by
    have original : (-2) * x 193 = 0 := h 91
    linear_combination ((-1 / 2 : ℝ)) * original
  have p1 : x 1 = 0 := by
    have original : (-2) * x 1 = 0 := h 92
    linear_combination ((-1 / 2 : ℝ)) * original
  have p2 : x 2 = 0 := by
    have original : (-2) * x 2 = 0 := h 93
    linear_combination ((-1 / 2 : ℝ)) * original
  have p16 : x 16 = 0 := by
    have original : (-2) * x 16 = 0 := h 94
    linear_combination ((-1 / 2 : ℝ)) * original
  have p18 : x 18 = 0 := by
    have original : (-2) * x 18 = 0 := h 95
    linear_combination ((-1 / 2 : ℝ)) * original
  have p23 : x 23 = 0 := by
    have original : (2) * x 23 = 0 := h 96
    linear_combination ((1 / 2 : ℝ)) * original
  have p24 : x 24 = 0 := by
    have original : (2) * x 24 = 0 := h 97
    linear_combination ((1 / 2 : ℝ)) * original
  have p30 : x 30 = 0 := by
    have original : (2) * x 30 = 0 := h 98
    linear_combination ((1 / 2 : ℝ)) * original
  have p33 : x 33 = 0 := by
    have original : (2) * x 33 = 0 := h 99
    linear_combination ((1 / 2 : ℝ)) * original
  have p45 : x 45 = 0 := by
    have original : (-2) * x 45 = 0 := h 100
    linear_combination ((-1 / 2 : ℝ)) * original
  have p48 : x 48 = 0 := by
    have original : (-2) * x 48 = 0 := h 101
    linear_combination ((-1 / 2 : ℝ)) * original
  have p49 : x 49 = 0 := by
    have original : (-2) * x 49 = 0 := h 102
    linear_combination ((-1 / 2 : ℝ)) * original
  have p52 : x 52 = 0 := by
    have original : (-2) * x 52 = 0 := h 103
    linear_combination ((-1 / 2 : ℝ)) * original
  have p65 : x 65 = 0 := by
    have original : (-2) * x 65 = 0 := h 104
    linear_combination ((-1 / 2 : ℝ)) * original
  have p68 : x 68 = 0 := by
    have original : (-2) * x 68 = 0 := h 105
    linear_combination ((-1 / 2 : ℝ)) * original
  have p69 : x 69 = 0 := by
    have original : (-2) * x 69 = 0 := h 106
    linear_combination ((-1 / 2 : ℝ)) * original
  have p72 : x 72 = 0 := by
    have original : (-2) * x 72 = 0 := h 107
    linear_combination ((-1 / 2 : ℝ)) * original
  have p81 : x 81 = 0 := by
    have original : (-2) * x 81 = 0 := h 108
    linear_combination ((-1 / 2 : ℝ)) * original
  have p82 : x 82 = 0 := by
    have original : (-2) * x 82 = 0 := h 109
    linear_combination ((-1 / 2 : ℝ)) * original
  have p96 : x 96 = 0 := by
    have original : (-2) * x 96 = 0 := h 110
    linear_combination ((-1 / 2 : ℝ)) * original
  have p98 : x 98 = 0 := by
    have original : (-2) * x 98 = 0 := h 111
    linear_combination ((-1 / 2 : ℝ)) * original
  have p100 : x 100 = 0 := by
    have original : (2) * x 100 = 0 := h 112
    linear_combination ((1 / 2 : ℝ)) * original
  have p106 : x 106 = 0 := by
    have original : (2) * x 106 = 0 := h 113
    linear_combination ((1 / 2 : ℝ)) * original
  have p107 : x 107 = 0 := by
    have original : (2) * x 107 = 0 := h 114
    linear_combination ((1 / 2 : ℝ)) * original
  have p111 : x 111 = 0 := by
    have original : (2) * x 111 = 0 := h 115
    linear_combination ((1 / 2 : ℝ)) * original
  have p114 : x 114 = 0 := by
    have original : (2) * x 114 = 0 := h 116
    linear_combination ((1 / 2 : ℝ)) * original
  have p115 : x 115 = 0 := by
    have original : (2) * x 115 = 0 := h 117
    linear_combination ((1 / 2 : ℝ)) * original
  have p117 : x 117 = 0 := by
    have original : (2) * x 117 = 0 := h 118
    linear_combination ((1 / 2 : ℝ)) * original
  have p119 : x 119 = 0 := by
    have original : (2) * x 119 = 0 := h 119
    linear_combination ((1 / 2 : ℝ)) * original
  have p120 : x 120 = 0 := by
    have original : (2) * x 120 = 0 := h 120
    linear_combination ((1 / 2 : ℝ)) * original
  have p126 : x 126 = 0 := by
    have original : (2) * x 126 = 0 := h 121
    linear_combination ((1 / 2 : ℝ)) * original
  have p127 : x 127 = 0 := by
    have original : (2) * x 127 = 0 := h 122
    linear_combination ((1 / 2 : ℝ)) * original
  have p131 : x 131 = 0 := by
    have original : (2) * x 131 = 0 := h 123
    linear_combination ((1 / 2 : ℝ)) * original
  have p134 : x 134 = 0 := by
    have original : (2) * x 134 = 0 := h 124
    linear_combination ((1 / 2 : ℝ)) * original
  have p135 : x 135 = 0 := by
    have original : (2) * x 135 = 0 := h 125
    linear_combination ((1 / 2 : ℝ)) * original
  have p137 : x 137 = 0 := by
    have original : (2) * x 137 = 0 := h 126
    linear_combination ((1 / 2 : ℝ)) * original
  have p139 : x 139 = 0 := by
    have original : (2) * x 139 = 0 := h 127
    linear_combination ((1 / 2 : ℝ)) * original
  have p141 : x 141 = 0 := by
    have original : (-2) * x 141 = 0 := h 128
    linear_combination ((-1 / 2 : ℝ)) * original
  have p142 : x 142 = 0 := by
    have original : (-2) * x 142 = 0 := h 129
    linear_combination ((-1 / 2 : ℝ)) * original
  have p156 : x 156 = 0 := by
    have original : (-2) * x 156 = 0 := h 130
    linear_combination ((-1 / 2 : ℝ)) * original
  have p158 : x 158 = 0 := by
    have original : (-2) * x 158 = 0 := h 131
    linear_combination ((-1 / 2 : ℝ)) * original
  have p161 : x 161 = 0 := by
    have original : (-2) * x 161 = 0 := h 132
    linear_combination ((-1 / 2 : ℝ)) * original
  have p162 : x 162 = 0 := by
    have original : (-2) * x 162 = 0 := h 133
    linear_combination ((-1 / 2 : ℝ)) * original
  have p176 : x 176 = 0 := by
    have original : (-2) * x 176 = 0 := h 134
    linear_combination ((-1 / 2 : ℝ)) * original
  have p178 : x 178 = 0 := by
    have original : (-2) * x 178 = 0 := h 135
    linear_combination ((-1 / 2 : ℝ)) * original
  have p181 : x 181 = 0 := by
    have original : (-2) * x 181 = 0 := h 136
    linear_combination ((-1 / 2 : ℝ)) * original
  have p182 : x 182 = 0 := by
    have original : (-2) * x 182 = 0 := h 137
    linear_combination ((-1 / 2 : ℝ)) * original
  have p196 : x 196 = 0 := by
    have original : (-2) * x 196 = 0 := h 138
    linear_combination ((-1 / 2 : ℝ)) * original
  have p198 : x 198 = 0 := by
    have original : (-2) * x 198 = 0 := h 139
    linear_combination ((-1 / 2 : ℝ)) * original
  have p7 : x 7 = 0 := by
    have original : (-2) * x 7 = 0 := h 140
    linear_combination ((-1 / 2 : ℝ)) * original
  have p15 : x 15 = 0 := by
    have original : (-2) * x 15 = 0 := h 141
    linear_combination ((-1 / 2 : ℝ)) * original
  have p25 : x 25 = 0 := by
    have original : (-2) * x 25 = 0 := h 142
    linear_combination ((-1 / 2 : ℝ)) * original
  have p29 : x 29 = 0 := by
    have original : (-2) * x 29 = 0 := h 143
    linear_combination ((-1 / 2 : ℝ)) * original
  have p44 : x 44 = 0 := by
    have original : (2) * x 44 = 0 := h 144
    linear_combination ((1 / 2 : ℝ)) * original
  have p50 : x 50 = 0 := by
    have original : (2) * x 50 = 0 := h 145
    linear_combination ((1 / 2 : ℝ)) * original
  have p63 : x 63 = 0 := by
    have original : (-2) * x 63 = 0 := h 146
    linear_combination ((-1 / 2 : ℝ)) * original
  have p73 : x 73 = 0 := by
    have original : (-2) * x 73 = 0 := h 147
    linear_combination ((-1 / 2 : ℝ)) * original
  have p87 : x 87 = 0 := by
    have original : (-2) * x 87 = 0 := h 148
    linear_combination ((-1 / 2 : ℝ)) * original
  have p95 : x 95 = 0 := by
    have original : (-2) * x 95 = 0 := h 149
    linear_combination ((-1 / 2 : ℝ)) * original
  have p102 : x 102 = 0 := by
    have original : (2) * x 102 = 0 := h 150
    linear_combination ((1 / 2 : ℝ)) * original
  have p116 : x 116 = 0 := by
    have original : (2) * x 116 = 0 := h 151
    linear_combination ((1 / 2 : ℝ)) * original
  have p121 : x 121 = 0 := by
    have original : (-2) * x 121 = 0 := h 152
    linear_combination ((-1 / 2 : ℝ)) * original
  have p138 : x 138 = 0 := by
    have original : (-2) * x 138 = 0 := h 153
    linear_combination ((-1 / 2 : ℝ)) * original
  have p147 : x 147 = 0 := by
    have original : (-2) * x 147 = 0 := h 154
    linear_combination ((-1 / 2 : ℝ)) * original
  have p155 : x 155 = 0 := by
    have original : (-2) * x 155 = 0 := h 155
    linear_combination ((-1 / 2 : ℝ)) * original
  have p160 : x 160 = 0 := by
    have original : (2) * x 160 = 0 := h 156
    linear_combination ((1 / 2 : ℝ)) * original
  have p166 : x 166 = 0 := by
    have original : (2) * x 166 = 0 := h 157
    linear_combination ((1 / 2 : ℝ)) * original
  have p171 : x 171 = 0 := by
    have original : (2) * x 171 = 0 := h 158
    linear_combination ((1 / 2 : ℝ)) * original
  have p174 : x 174 = 0 := by
    have original : (2) * x 174 = 0 := h 159
    linear_combination ((1 / 2 : ℝ)) * original
  have p177 : x 177 = 0 := by
    have original : (2) * x 177 = 0 := h 160
    linear_combination ((1 / 2 : ℝ)) * original
  have p179 : x 179 = 0 := by
    have original : (2) * x 179 = 0 := h 161
    linear_combination ((1 / 2 : ℝ)) * original
  have p187 : x 187 = 0 := by
    have original : (-2) * x 187 = 0 := h 162
    linear_combination ((-1 / 2 : ℝ)) * original
  have p195 : x 195 = 0 := by
    have original : (-2) * x 195 = 0 := h 163
    linear_combination ((-1 / 2 : ℝ)) * original
  have p0 : x 0 + (-x 6) = 0 := by
    have original : (-x 0) + x 6 = 0 := h 164
    linear_combination (-original)
  have p17 : x 17 + (-x 19) = 0 := by
    have original : (-x 17) + x 19 = 0 := h 165
    linear_combination (-original)
  have p28 : x 28 + x 43 = 0 := by
    have original : (-x 28) + (-x 43) = 0 := h 166
    linear_combination (-original)
  have p32 : x 32 + (-x 53) = 0 := by
    have original : x 32 + (-x 53) = 0 := h 167
    linear_combination original
  have p64 : x 64 + (-x 70) = 0 := by
    have original : (-x 64) + x 70 = 0 := h 168
    linear_combination (-original)
  have p86 : x 86 + (-x 140) = 0 := by
    have original : x 86 + (-x 140) = 0 := h 169
    linear_combination original
  have p80 : x 80 + (-x 146) = 0 := by
    have original : x 80 + (-x 146) = 0 := h 170
    linear_combination original
  have p91 : x 91 + (-x 151) = 0 := by
    have original : x 91 + (-x 151) = 0 := h 171
    linear_combination original
  have p94 : x 94 + (-x 154) = 0 := by
    have original : x 94 + (-x 154) = 0 := h 172
    linear_combination original
  have p99 : x 99 + (-x 157) = 0 := by
    have original : x 99 + (-x 157) = 0 := h 173
    linear_combination original
  have p97 : x 97 + (-x 159) = 0 := by
    have original : x 97 + (-x 159) = 0 := h 174
    linear_combination original
  have p122 : x 122 + (-x 167) = 0 := by
    have original : x 122 + (-x 167) = 0 := h 175
    linear_combination original
  have p136 : x 136 + x 175 = 0 := by
    have original : (-x 136) + (-x 175) = 0 := h 176
    linear_combination (-original)
  have p180 : x 180 + (-x 186) = 0 := by
    have original : (-x 180) + x 186 = 0 := h 177
    linear_combination (-original)
  have p197 : x 197 + (-x 199) = 0 := by
    have original : (-x 197) + x 199 = 0 := h 178
    linear_combination (-original)
  have p6 : x 6 + (-x 11) = 0 := by
    have original : (-x 0) + x 11 = 0 := h 179
    linear_combination (-original) + (-p0)
  have p14 : x 14 + (-x 19) = 0 := by
    have original : (-x 14) + x 19 = 0 := h 180
    linear_combination (-original)
  have p53 : x 53 + x 64 = 0 := by
    have original : (-x 32) + (-x 64) = 0 := h 181
    linear_combination (-original) + (-p32)
  have p43 : x 43 + (-x 70) = 0 := by
    have original : (-x 28) + (-x 70) = 0 := h 182
    linear_combination original + p28
  have p151 : x 151 + (-x 180) = 0 := by
    have original : x 91 + (-x 180) = 0 := h 183
    linear_combination original + (-p91)
  have p140 : x 140 + (-x 186) = 0 := by
    have original : x 86 + (-x 186) = 0 := h 184
    linear_combination original + (-p86)
  have p146 : x 146 + (-x 191) = 0 := by
    have original : x 80 + (-x 191) = 0 := h 185
    linear_combination original + (-p80)
  have p157 : x 157 + (-x 194) = 0 := by
    have original : x 99 + (-x 194) = 0 := h 186
    linear_combination original + (-p99)
  have p159 : x 159 + (-x 197) = 0 := by
    have original : x 97 + (-x 197) = 0 := h 187
    linear_combination original + (-p97)
  have p154 : x 154 + (-x 199) = 0 := by
    have original : x 94 + (-x 199) = 0 := h 188
    linear_combination original + (-p94)
  have p101 : x 101 + (-x 167) = 0 := by
    have original : x 101 + (-x 167) = 0 := h 189
    linear_combination original
  have p118 : x 118 + (-x 175) = 0 := by
    have original : x 118 + (-x 175) = 0 := h 190
    linear_combination original
  have p11 : x 11 + ((10 / 3 : ℝ)) * x 20 + x 80 = 0 := by
    have original : ((-9 / 16 : ℝ)) * x 0 + ((-15 / 8 : ℝ)) * x 20 + ((-9 / 16 : ℝ)) * x 80 = 0 := h 191
    linear_combination ((-16 / 9 : ℝ)) * original + (-p0) + (-p6)
  have p19 : x 19 + ((-10 / 3 : ℝ)) * x 26 + (-x 86) = 0 := by
    have original : ((15 / 16 : ℝ)) * x 8 + ((9 / 16 : ℝ)) * x 14 + ((-15 / 8 : ℝ)) * x 26 + ((-9 / 16 : ℝ)) * x 86 = 0 := h 192
    linear_combination ((16 / 9 : ℝ)) * original + ((-5 / 3 : ℝ)) * p8 + (-p14)
  have p70 : x 70 + (-x 80) + x 86 + ((-3 / 10 : ℝ)) * x 88 = 0 := by
    have original : ((15 / 8 : ℝ)) * x 6 + ((9 / 16 : ℝ)) * x 8 + ((15 / 8 : ℝ)) * x 14 + ((-15 / 8 : ℝ)) * x 28 + ((-9 / 16 : ℝ)) * x 88 = 0 := h 193
    linear_combination ((8 / 15 : ℝ)) * original + (-p6) + ((-3 / 10 : ℝ)) * p8 + (-p11) + (-p14) + (-p19) + ((10 / 3 : ℝ)) * p20 + ((-10 / 3 : ℝ)) * p26 + p28 + (-p43)
  have p191 : x 191 + x 199 = 0 := by
    have original : ((9 / 16 : ℝ)) * x 6 + ((15 / 16 : ℝ)) * x 8 + ((-15 / 8 : ℝ)) * x 34 + ((-9 / 16 : ℝ)) * x 94 = 0 := h 194
    linear_combination ((-16 / 9 : ℝ)) * original + p6 + ((5 / 3 : ℝ)) * p8 + p11 + ((-10 / 3 : ℝ)) * p20 + ((-10 / 3 : ℝ)) * p34 + (-p80) + (-p94) + (-p146) + (-p154)
  have p186 : x 186 + x 194 = 0 := by
    have original : ((-9 / 16 : ℝ)) * x 19 + ((-15 / 8 : ℝ)) * x 39 + ((-9 / 16 : ℝ)) * x 99 = 0 := h 195
    linear_combination ((-16 / 9 : ℝ)) * original + (-p19) + ((-10 / 3 : ℝ)) * p26 + ((-10 / 3 : ℝ)) * p39 + (-p86) + (-p99) + (-p140) + (-p157)
  have p167 : x 167 + x 186 + (-x 191) = 0 := by
    have original : ((3 / 4 : ℝ)) * x 43 + ((-3 / 4 : ℝ)) * x 101 = 0 := h 196
    linear_combination ((-4 / 3 : ℝ)) * original + p43 + p70 + p80 + (-p86) + ((3 / 10 : ℝ)) * p88 + (-p101) + (-p140) + p146
  have p175 : x 175 + (-x 186) + x 191 = 0 := by
    have original : ((3 / 4 : ℝ)) * x 53 + ((-3 / 4 : ℝ)) * x 118 = 0 := h 197
    linear_combination ((-4 / 3 : ℝ)) * original + p53 + (-p64) + (-p70) + (-p80) + p86 + ((-3 / 10 : ℝ)) * p88 + (-p118) + p140 + (-p146)
  have s194 : x 194 = x 194 + (0) * x 199 := by ring
  have s199 : x 199 = (0) * x 194 + x 199 := by ring
  have s198 : x 198 = (0) * x 194 + (0) * x 199 := by
    linear_combination p198
  have s197 : x 197 = (0) * x 194 + x 199 := by
    linear_combination p197 + s199
  have s196 : x 196 = (0) * x 194 + (0) * x 199 := by
    linear_combination p196
  have s195 : x 195 = (0) * x 194 + (0) * x 199 := by
    linear_combination p195
  have s193 : x 193 = (0) * x 194 + (0) * x 199 := by
    linear_combination p193
  have s192 : x 192 = (0) * x 194 + (0) * x 199 := by
    linear_combination p192
  have s191 : x 191 = (0) * x 194 + (-x 199) := by
    linear_combination p191 + (-s199)
  have s190 : x 190 = (0) * x 194 + (0) * x 199 := by
    linear_combination p190
  have s189 : x 189 = (0) * x 194 + (0) * x 199 := by
    linear_combination p189
  have s188 : x 188 = (0) * x 194 + (0) * x 199 := by
    linear_combination p188
  have s187 : x 187 = (0) * x 194 + (0) * x 199 := by
    linear_combination p187
  have s186 : x 186 = (-x 194) + (0) * x 199 := by
    linear_combination p186 + (-s194)
  have s185 : x 185 = (0) * x 194 + (0) * x 199 := by
    linear_combination p185
  have s184 : x 184 = (0) * x 194 + (0) * x 199 := by
    linear_combination p184
  have s183 : x 183 = (0) * x 194 + (0) * x 199 := by
    linear_combination p183
  have s182 : x 182 = (0) * x 194 + (0) * x 199 := by
    linear_combination p182
  have s181 : x 181 = (0) * x 194 + (0) * x 199 := by
    linear_combination p181
  have s180 : x 180 = (-x 194) + (0) * x 199 := by
    linear_combination p180 + s186
  have s179 : x 179 = (0) * x 194 + (0) * x 199 := by
    linear_combination p179
  have s178 : x 178 = (0) * x 194 + (0) * x 199 := by
    linear_combination p178
  have s177 : x 177 = (0) * x 194 + (0) * x 199 := by
    linear_combination p177
  have s176 : x 176 = (0) * x 194 + (0) * x 199 := by
    linear_combination p176
  have s175 : x 175 = (-x 194) + x 199 := by
    linear_combination p175 + s186 + (-s191)
  have s174 : x 174 = (0) * x 194 + (0) * x 199 := by
    linear_combination p174
  have s173 : x 173 = (0) * x 194 + (0) * x 199 := by
    linear_combination p173
  have s172 : x 172 = (0) * x 194 + (0) * x 199 := by
    linear_combination p172
  have s171 : x 171 = (0) * x 194 + (0) * x 199 := by
    linear_combination p171
  have s170 : x 170 = (0) * x 194 + (0) * x 199 := by
    linear_combination p170
  have s169 : x 169 = (0) * x 194 + (0) * x 199 := by
    linear_combination p169
  have s168 : x 168 = (0) * x 194 + (0) * x 199 := by
    linear_combination p168
  have s167 : x 167 = x 194 + (-x 199) := by
    linear_combination p167 + (-s186) + s191
  have s166 : x 166 = (0) * x 194 + (0) * x 199 := by
    linear_combination p166
  have s165 : x 165 = (0) * x 194 + (0) * x 199 := by
    linear_combination p165
  have s164 : x 164 = (0) * x 194 + (0) * x 199 := by
    linear_combination p164
  have s163 : x 163 = (0) * x 194 + (0) * x 199 := by
    linear_combination p163
  have s162 : x 162 = (0) * x 194 + (0) * x 199 := by
    linear_combination p162
  have s161 : x 161 = (0) * x 194 + (0) * x 199 := by
    linear_combination p161
  have s160 : x 160 = (0) * x 194 + (0) * x 199 := by
    linear_combination p160
  have s159 : x 159 = (0) * x 194 + x 199 := by
    linear_combination p159 + s197
  have s158 : x 158 = (0) * x 194 + (0) * x 199 := by
    linear_combination p158
  have s157 : x 157 = x 194 + (0) * x 199 := by
    linear_combination p157 + s194
  have s156 : x 156 = (0) * x 194 + (0) * x 199 := by
    linear_combination p156
  have s155 : x 155 = (0) * x 194 + (0) * x 199 := by
    linear_combination p155
  have s154 : x 154 = (0) * x 194 + x 199 := by
    linear_combination p154 + s199
  have s153 : x 153 = (0) * x 194 + (0) * x 199 := by
    linear_combination p153
  have s152 : x 152 = (0) * x 194 + (0) * x 199 := by
    linear_combination p152
  have s151 : x 151 = (-x 194) + (0) * x 199 := by
    linear_combination p151 + s180
  have s150 : x 150 = (0) * x 194 + (0) * x 199 := by
    linear_combination p150
  have s149 : x 149 = (0) * x 194 + (0) * x 199 := by
    linear_combination p149
  have s148 : x 148 = (0) * x 194 + (0) * x 199 := by
    linear_combination p148
  have s147 : x 147 = (0) * x 194 + (0) * x 199 := by
    linear_combination p147
  have s146 : x 146 = (0) * x 194 + (-x 199) := by
    linear_combination p146 + s191
  have s145 : x 145 = (0) * x 194 + (0) * x 199 := by
    linear_combination p145
  have s144 : x 144 = (0) * x 194 + (0) * x 199 := by
    linear_combination p144
  have s143 : x 143 = (0) * x 194 + (0) * x 199 := by
    linear_combination p143
  have s142 : x 142 = (0) * x 194 + (0) * x 199 := by
    linear_combination p142
  have s141 : x 141 = (0) * x 194 + (0) * x 199 := by
    linear_combination p141
  have s140 : x 140 = (-x 194) + (0) * x 199 := by
    linear_combination p140 + s186
  have s139 : x 139 = (0) * x 194 + (0) * x 199 := by
    linear_combination p139
  have s138 : x 138 = (0) * x 194 + (0) * x 199 := by
    linear_combination p138
  have s137 : x 137 = (0) * x 194 + (0) * x 199 := by
    linear_combination p137
  have s136 : x 136 = x 194 + (-x 199) := by
    linear_combination p136 + (-s175)
  have s135 : x 135 = (0) * x 194 + (0) * x 199 := by
    linear_combination p135
  have s134 : x 134 = (0) * x 194 + (0) * x 199 := by
    linear_combination p134
  have s133 : x 133 = (0) * x 194 + (0) * x 199 := by
    linear_combination p133
  have s132 : x 132 = (0) * x 194 + (0) * x 199 := by
    linear_combination p132
  have s131 : x 131 = (0) * x 194 + (0) * x 199 := by
    linear_combination p131
  have s130 : x 130 = (0) * x 194 + (0) * x 199 := by
    linear_combination p130
  have s129 : x 129 = (0) * x 194 + (0) * x 199 := by
    linear_combination p129
  have s128 : x 128 = (0) * x 194 + (0) * x 199 := by
    linear_combination p128
  have s127 : x 127 = (0) * x 194 + (0) * x 199 := by
    linear_combination p127
  have s126 : x 126 = (0) * x 194 + (0) * x 199 := by
    linear_combination p126
  have s125 : x 125 = (0) * x 194 + (0) * x 199 := by
    linear_combination p125
  have s124 : x 124 = (0) * x 194 + (0) * x 199 := by
    linear_combination p124
  have s123 : x 123 = (0) * x 194 + (0) * x 199 := by
    linear_combination p123
  have s122 : x 122 = x 194 + (-x 199) := by
    linear_combination p122 + s167
  have s121 : x 121 = (0) * x 194 + (0) * x 199 := by
    linear_combination p121
  have s120 : x 120 = (0) * x 194 + (0) * x 199 := by
    linear_combination p120
  have s119 : x 119 = (0) * x 194 + (0) * x 199 := by
    linear_combination p119
  have s118 : x 118 = (-x 194) + x 199 := by
    linear_combination p118 + s175
  have s117 : x 117 = (0) * x 194 + (0) * x 199 := by
    linear_combination p117
  have s116 : x 116 = (0) * x 194 + (0) * x 199 := by
    linear_combination p116
  have s115 : x 115 = (0) * x 194 + (0) * x 199 := by
    linear_combination p115
  have s114 : x 114 = (0) * x 194 + (0) * x 199 := by
    linear_combination p114
  have s113 : x 113 = (0) * x 194 + (0) * x 199 := by
    linear_combination p113
  have s112 : x 112 = (0) * x 194 + (0) * x 199 := by
    linear_combination p112
  have s111 : x 111 = (0) * x 194 + (0) * x 199 := by
    linear_combination p111
  have s110 : x 110 = (0) * x 194 + (0) * x 199 := by
    linear_combination p110
  have s109 : x 109 = (0) * x 194 + (0) * x 199 := by
    linear_combination p109
  have s108 : x 108 = (0) * x 194 + (0) * x 199 := by
    linear_combination p108
  have s107 : x 107 = (0) * x 194 + (0) * x 199 := by
    linear_combination p107
  have s106 : x 106 = (0) * x 194 + (0) * x 199 := by
    linear_combination p106
  have s105 : x 105 = (0) * x 194 + (0) * x 199 := by
    linear_combination p105
  have s104 : x 104 = (0) * x 194 + (0) * x 199 := by
    linear_combination p104
  have s103 : x 103 = (0) * x 194 + (0) * x 199 := by
    linear_combination p103
  have s102 : x 102 = (0) * x 194 + (0) * x 199 := by
    linear_combination p102
  have s101 : x 101 = x 194 + (-x 199) := by
    linear_combination p101 + s167
  have s100 : x 100 = (0) * x 194 + (0) * x 199 := by
    linear_combination p100
  have s99 : x 99 = x 194 + (0) * x 199 := by
    linear_combination p99 + s157
  have s98 : x 98 = (0) * x 194 + (0) * x 199 := by
    linear_combination p98
  have s97 : x 97 = (0) * x 194 + x 199 := by
    linear_combination p97 + s159
  have s96 : x 96 = (0) * x 194 + (0) * x 199 := by
    linear_combination p96
  have s95 : x 95 = (0) * x 194 + (0) * x 199 := by
    linear_combination p95
  have s94 : x 94 = (0) * x 194 + x 199 := by
    linear_combination p94 + s154
  have s93 : x 93 = (0) * x 194 + (0) * x 199 := by
    linear_combination p93
  have s92 : x 92 = (0) * x 194 + (0) * x 199 := by
    linear_combination p92
  have s91 : x 91 = (-x 194) + (0) * x 199 := by
    linear_combination p91 + s151
  have s90 : x 90 = (0) * x 194 + (0) * x 199 := by
    linear_combination p90
  have s89 : x 89 = (0) * x 194 + (0) * x 199 := by
    linear_combination p89
  have s88 : x 88 = (0) * x 194 + (0) * x 199 := by
    linear_combination p88
  have s87 : x 87 = (0) * x 194 + (0) * x 199 := by
    linear_combination p87
  have s86 : x 86 = (-x 194) + (0) * x 199 := by
    linear_combination p86 + s140
  have s85 : x 85 = (0) * x 194 + (0) * x 199 := by
    linear_combination p85
  have s84 : x 84 = (0) * x 194 + (0) * x 199 := by
    linear_combination p84
  have s83 : x 83 = (0) * x 194 + (0) * x 199 := by
    linear_combination p83
  have s82 : x 82 = (0) * x 194 + (0) * x 199 := by
    linear_combination p82
  have s81 : x 81 = (0) * x 194 + (0) * x 199 := by
    linear_combination p81
  have s80 : x 80 = (0) * x 194 + (-x 199) := by
    linear_combination p80 + s146
  have s79 : x 79 = (0) * x 194 + (0) * x 199 := by
    linear_combination p79
  have s78 : x 78 = (0) * x 194 + (0) * x 199 := by
    linear_combination p78
  have s77 : x 77 = (0) * x 194 + (0) * x 199 := by
    linear_combination p77
  have s76 : x 76 = (0) * x 194 + (0) * x 199 := by
    linear_combination p76
  have s75 : x 75 = (0) * x 194 + (0) * x 199 := by
    linear_combination p75
  have s74 : x 74 = (0) * x 194 + (0) * x 199 := by
    linear_combination p74
  have s73 : x 73 = (0) * x 194 + (0) * x 199 := by
    linear_combination p73
  have s72 : x 72 = (0) * x 194 + (0) * x 199 := by
    linear_combination p72
  have s71 : x 71 = (0) * x 194 + (0) * x 199 := by
    linear_combination p71
  have s70 : x 70 = x 194 + (-x 199) := by
    linear_combination p70 + s80 + (-s86) + ((3 / 10 : ℝ)) * s88
  have s69 : x 69 = (0) * x 194 + (0) * x 199 := by
    linear_combination p69
  have s68 : x 68 = (0) * x 194 + (0) * x 199 := by
    linear_combination p68
  have s67 : x 67 = (0) * x 194 + (0) * x 199 := by
    linear_combination p67
  have s66 : x 66 = (0) * x 194 + (0) * x 199 := by
    linear_combination p66
  have s65 : x 65 = (0) * x 194 + (0) * x 199 := by
    linear_combination p65
  have s64 : x 64 = x 194 + (-x 199) := by
    linear_combination p64 + s70
  have s63 : x 63 = (0) * x 194 + (0) * x 199 := by
    linear_combination p63
  have s62 : x 62 = (0) * x 194 + (0) * x 199 := by
    linear_combination p62
  have s61 : x 61 = (0) * x 194 + (0) * x 199 := by
    linear_combination p61
  have s60 : x 60 = (0) * x 194 + (0) * x 199 := by
    linear_combination p60
  have s59 : x 59 = (0) * x 194 + (0) * x 199 := by
    linear_combination p59
  have s58 : x 58 = (0) * x 194 + (0) * x 199 := by
    linear_combination p58
  have s57 : x 57 = (0) * x 194 + (0) * x 199 := by
    linear_combination p57
  have s56 : x 56 = (0) * x 194 + (0) * x 199 := by
    linear_combination p56
  have s55 : x 55 = (0) * x 194 + (0) * x 199 := by
    linear_combination p55
  have s54 : x 54 = (0) * x 194 + (0) * x 199 := by
    linear_combination p54
  have s53 : x 53 = (-x 194) + x 199 := by
    linear_combination p53 + (-s64)
  have s52 : x 52 = (0) * x 194 + (0) * x 199 := by
    linear_combination p52
  have s51 : x 51 = (0) * x 194 + (0) * x 199 := by
    linear_combination p51
  have s50 : x 50 = (0) * x 194 + (0) * x 199 := by
    linear_combination p50
  have s49 : x 49 = (0) * x 194 + (0) * x 199 := by
    linear_combination p49
  have s48 : x 48 = (0) * x 194 + (0) * x 199 := by
    linear_combination p48
  have s47 : x 47 = (0) * x 194 + (0) * x 199 := by
    linear_combination p47
  have s46 : x 46 = (0) * x 194 + (0) * x 199 := by
    linear_combination p46
  have s45 : x 45 = (0) * x 194 + (0) * x 199 := by
    linear_combination p45
  have s44 : x 44 = (0) * x 194 + (0) * x 199 := by
    linear_combination p44
  have s43 : x 43 = x 194 + (-x 199) := by
    linear_combination p43 + s70
  have s42 : x 42 = (0) * x 194 + (0) * x 199 := by
    linear_combination p42
  have s41 : x 41 = (0) * x 194 + (0) * x 199 := by
    linear_combination p41
  have s40 : x 40 = (0) * x 194 + (0) * x 199 := by
    linear_combination p40
  have s39 : x 39 = (0) * x 194 + (0) * x 199 := by
    linear_combination p39
  have s38 : x 38 = (0) * x 194 + (0) * x 199 := by
    linear_combination p38
  have s37 : x 37 = (0) * x 194 + (0) * x 199 := by
    linear_combination p37
  have s36 : x 36 = (0) * x 194 + (0) * x 199 := by
    linear_combination p36
  have s35 : x 35 = (0) * x 194 + (0) * x 199 := by
    linear_combination p35
  have s34 : x 34 = (0) * x 194 + (0) * x 199 := by
    linear_combination p34
  have s33 : x 33 = (0) * x 194 + (0) * x 199 := by
    linear_combination p33
  have s32 : x 32 = (-x 194) + x 199 := by
    linear_combination p32 + s53
  have s31 : x 31 = (0) * x 194 + (0) * x 199 := by
    linear_combination p31
  have s30 : x 30 = (0) * x 194 + (0) * x 199 := by
    linear_combination p30
  have s29 : x 29 = (0) * x 194 + (0) * x 199 := by
    linear_combination p29
  have s28 : x 28 = (-x 194) + x 199 := by
    linear_combination p28 + (-s43)
  have s27 : x 27 = (0) * x 194 + (0) * x 199 := by
    linear_combination p27
  have s26 : x 26 = (0) * x 194 + (0) * x 199 := by
    linear_combination p26
  have s25 : x 25 = (0) * x 194 + (0) * x 199 := by
    linear_combination p25
  have s24 : x 24 = (0) * x 194 + (0) * x 199 := by
    linear_combination p24
  have s23 : x 23 = (0) * x 194 + (0) * x 199 := by
    linear_combination p23
  have s22 : x 22 = (0) * x 194 + (0) * x 199 := by
    linear_combination p22
  have s21 : x 21 = (0) * x 194 + (0) * x 199 := by
    linear_combination p21
  have s20 : x 20 = (0) * x 194 + (0) * x 199 := by
    linear_combination p20
  have s19 : x 19 = (-x 194) + (0) * x 199 := by
    linear_combination p19 + ((10 / 3 : ℝ)) * s26 + s86
  have s18 : x 18 = (0) * x 194 + (0) * x 199 := by
    linear_combination p18
  have s17 : x 17 = (-x 194) + (0) * x 199 := by
    linear_combination p17 + s19
  have s16 : x 16 = (0) * x 194 + (0) * x 199 := by
    linear_combination p16
  have s15 : x 15 = (0) * x 194 + (0) * x 199 := by
    linear_combination p15
  have s14 : x 14 = (-x 194) + (0) * x 199 := by
    linear_combination p14 + s19
  have s13 : x 13 = (0) * x 194 + (0) * x 199 := by
    linear_combination p13
  have s12 : x 12 = (0) * x 194 + (0) * x 199 := by
    linear_combination p12
  have s11 : x 11 = (0) * x 194 + x 199 := by
    linear_combination p11 + ((-10 / 3 : ℝ)) * s20 + (-s80)
  have s10 : x 10 = (0) * x 194 + (0) * x 199 := by
    linear_combination p10
  have s9 : x 9 = (0) * x 194 + (0) * x 199 := by
    linear_combination p9
  have s8 : x 8 = (0) * x 194 + (0) * x 199 := by
    linear_combination p8
  have s7 : x 7 = (0) * x 194 + (0) * x 199 := by
    linear_combination p7
  have s6 : x 6 = (0) * x 194 + x 199 := by
    linear_combination p6 + s11
  have s5 : x 5 = (0) * x 194 + (0) * x 199 := by
    linear_combination p5
  have s4 : x 4 = (0) * x 194 + (0) * x 199 := by
    linear_combination p4
  have s3 : x 3 = (0) * x 194 + (0) * x 199 := by
    linear_combination p3
  have s2 : x 2 = (0) * x 194 + (0) * x 199 := by
    linear_combination p2
  have s1 : x 1 = (0) * x 194 + (0) * x 199 := by
    linear_combination p1
  have s0 : x 0 = (0) * x 194 + x 199 := by
    linear_combination p0 + s6
  intro i
  fin_cases i
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s0
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s1
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s2
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s3
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s4
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s5
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s6
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s7
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s8
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s9
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s10
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s11
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s12
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s13
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s14
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s15
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s16
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s17
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s18
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s19
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s20
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s21
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s22
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s23
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s24
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s25
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s26
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s27
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s28
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s29
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s30
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s31
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s32
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s33
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s34
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s35
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s36
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s37
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s38
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s39
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s40
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s41
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s42
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s43
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s44
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s45
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s46
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s47
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s48
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s49
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s50
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s51
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s52
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s53
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s54
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s55
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s56
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s57
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s58
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s59
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s60
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s61
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s62
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s63
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s64
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s65
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s66
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s67
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s68
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s69
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s70
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s71
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s72
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s73
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s74
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s75
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s76
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s77
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s78
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s79
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s80
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s81
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s82
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s83
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s84
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s85
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s86
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s87
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s88
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s89
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s90
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s91
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s92
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s93
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s94
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s95
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s96
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s97
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s98
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s99
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s100
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s101
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s102
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s103
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s104
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s105
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s106
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s107
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s108
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s109
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s110
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s111
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s112
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s113
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s114
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s115
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s116
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s117
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s118
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s119
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s120
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s121
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s122
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s123
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s124
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s125
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s126
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s127
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s128
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s129
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s130
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s131
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s132
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s133
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s134
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s135
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s136
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s137
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s138
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s139
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s140
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s141
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s142
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s143
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s144
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s145
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s146
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s147
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s148
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s149
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s150
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s151
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s152
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s153
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s154
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s155
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s156
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s157
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s158
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s159
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s160
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s161
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s162
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s163
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s164
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s165
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s166
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s167
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s168
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s169
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s170
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s171
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s172
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s173
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s174
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s175
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s176
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s177
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s178
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s179
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s180
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s181
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s182
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s183
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s184
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s185
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s186
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s187
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s188
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s189
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s190
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s191
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s192
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s193
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s194
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s195
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s196
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s197
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s198
  · simpa only [commutantKernelU, commutantKernelV, zero_mul, one_mul, neg_one_mul] using s199

set_option maxHeartbeats 0 in
theorem commutant_kernel_u_solution :
    ∀ i : Fin 198, commutantEquation i commutantKernelU = 0 := by
  intro i; fin_cases i <;> norm_num [commutantEquation, commutantKernelU]

set_option maxHeartbeats 0 in
theorem commutant_kernel_v_solution :
    ∀ i : Fin 198, commutantEquation i commutantKernelV = 0 := by
  intro i; fin_cases i <;> norm_num [commutantEquation, commutantKernelV]

#print axioms commutant_kernel_reconstruction
#print axioms commutant_kernel_u_solution
#print axioms commutant_kernel_v_solution
end
end AASCSemanticExhaustion
