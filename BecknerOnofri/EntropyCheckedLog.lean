import BecknerOnofri.EntropyLogRows

namespace BecknerOnofri.HighDim.EntropyLogCertificate
structure CheckedLog where
  value : ℚ
  lower : ℚ
  upper : ℚ
  sound : (lower : ℝ)≤Real.log (value : ℝ) ∧ Real.log (value : ℝ)≤(upper : ℝ)

def checkedLogOfRows (cs : List LogRow) (hc : cs.all LogRow.check=true)
    (i : Fin cs.length) : CheckedLog where
  value := (cs[i]).value
  lower := (cs[i]).lower
  upper := (cs[i]).upper
  sound := logRows_sound cs hc i
end BecknerOnofri.HighDim.EntropyLogCertificate
