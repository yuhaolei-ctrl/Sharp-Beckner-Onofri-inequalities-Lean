import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.SpinSmallMean
import BecknerOnofri.SpinLargeMean
import BecknerOnofri.EntropyCheckedLog
namespace BecknerOnofri.HighDim.Spin
open ScalarCertificate ScalarCertificate.CertifiedMinorant EntropyLogCertificate
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def endLogs : List LogRow := [
  ⟨(397/200),397,200,(0),(137123782827830747126043/200000000000000000000000),(342809457069576867815109/500000000000000000000000)⟩,
  ⟨(3/200),48,25,(-7),(-4199705077879926986057971/1000000000000000000000000),(-262481567367495436628623/62500000000000000000000)⟩
]
theorem endLogs_accepted : endLogs.all LogRow.check=true := by decide +kernel
def logPlus := checkedLogOfRows endLogs endLogs_accepted ⟨0,by decide⟩
def logMinus := checkedLogOfRows endLogs endLogs_accepted ⟨1,by decide⟩
def lastPiece : AffinePiece := pieces[1621]'(by decide +kernel)
def entropyLowerQ : ℚ := ((1+197/200)*logPlus.lower+(1-197/200)*logMinus.lower)/2
theorem large_margin : (1/250 : ℚ)≤24*entropyLowerQ-(∑ s : Order,weightQ s)+
    12*(lastPiece.slope*(197/200)+lastPiece.intercept) := by decide +kernel
theorem last_slope_nonneg : 0≤lastPiece.slope := by decide +kernel
theorem binaryCost_large_lower : (entropyLowerQ : ℝ)≤binaryCost (197/200) := by
  have hp := logPlus.sound.1
  have hm := logMinus.sound.1
  change (logPlus.lower : ℝ)≤Real.log ((397/200 : ℚ) : ℝ) at hp
  change (logMinus.lower : ℝ)≤Real.log ((3/200 : ℚ) : ℝ) at hm
  push_cast at hp hm
  have he1 : (1 : ℝ)+197/200=397/200 := by norm_num
  have he2 : (1 : ℝ)-197/200=3/200 := by norm_num
  unfold binaryCost entropyLowerQ
  push_cast
  rw [he1,he2]
  nlinarith
theorem small_spin_bound (q : Count → ℝ) (t : ℝ) (hq : FeasibleAt t q)
    (ht : t∈Set.Icc (0 : ℝ) (1/16)) : t^4/250≤functional q+12*psi t := by
  rw [psi_small ht.2]
  have h := small_mean_spin_inequality t q ht.1 ht.2 hq
  nlinarith [pow_nonneg ht.1 4]
theorem large_spin_bound (q : Count → ℝ) (t : ℝ) (hq : FeasibleAt t q)
    (ht : t∈Set.Icc (197/200 : ℝ) 1) : t^4/250≤functional q+12*psi t := by
  have he := entropy_lower_at_smaller_mean (197/200) t q (by norm_num) (by norm_num) ht.1 hq
  have hQ := probability_quadratic_upper hq.1.1 hq.1.2.1
  have hp := piece_le_psi ⟨1621,by decide +kernel⟩ t
  change lastPiece.value t≤psi t at hp
  have hs : (0 : ℝ)≤lastPiece.slope := by exact_mod_cast last_slope_nonneg
  have hl := mul_le_mul_of_nonneg_left ht.1 hs
  have hmargin := (Rat.cast_le (K := ℝ)).mpr large_margin
  push_cast at hmargin
  have hw : (∑ s : Order,(weightQ s : ℝ))=∑ s : Order,weight s := rfl
  rw [hw] at hmargin
  have ht0 : 0≤t := by linarith [ht.1]
  have h4 : t^4≤1 := by simpa using pow_le_pow_left₀ ht0 ht.2 4
  unfold AffinePiece.value at hp
  unfold functional
  nlinarith [binaryCost_large_lower]
#print axioms small_spin_bound
#print axioms large_spin_bound
end BecknerOnofri.HighDim.Spin
