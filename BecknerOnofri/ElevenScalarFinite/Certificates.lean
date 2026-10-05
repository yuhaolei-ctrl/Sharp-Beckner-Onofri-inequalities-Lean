import BecknerOnofri.ElevenScalarFinite.Case01
import BecknerOnofri.ElevenScalarFinite.Case02
import BecknerOnofri.ElevenScalarFinite.Case03
import BecknerOnofri.ElevenScalarFinite.Case04
import BecknerOnofri.ElevenScalarFinite.Case05
import BecknerOnofri.ElevenScalarFinite.Case06
import BecknerOnofri.ElevenScalarFinite.Case07
import BecknerOnofri.ElevenScalarFinite.Case08
import BecknerOnofri.ElevenScalarFinite.Case09
import BecknerOnofri.ElevenScalarFinite.Case10
import BecknerOnofri.ElevenScalarFinite.Case11
import BecknerOnofri.ElevenScalarFinite.Case12
import BecknerOnofri.ElevenScalarFinite.Case13
import BecknerOnofri.ElevenScalarFinite.Case14
import BecknerOnofri.ElevenScalarFinite.Case15
import BecknerOnofri.ElevenScalarFinite.Case16
import BecknerOnofri.ElevenScalarFinite.Case17
import BecknerOnofri.ElevenScalarFinite.Case18
import BecknerOnofri.ElevenScalarFinite.Case19
import BecknerOnofri.ElevenScalarFinite.Case20
import BecknerOnofri.ElevenScalarFinite.Case21
namespace BecknerOnofri.HighDim.Eleven.ScalarFinite
open Legacy.D10.FiniteScalar Legacy.BecknerOnofri.FiniteScalar
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checks : ∀ i : Fin 21,
    betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 (i.val+1) + 1/2000 <
      11 * harmonic (i.val+1) := by
  intro i
  fin_cases i
  · exact Case01.checked
  · exact Case02.checked
  · exact Case03.checked
  · exact Case04.checked
  · exact Case05.checked
  · exact Case06.checked
  · exact Case07.checked
  · exact Case08.checked
  · exact Case09.checked
  · exact Case10.checked
  · exact Case11.checked
  · exact Case12.checked
  · exact Case13.checked
  · exact Case14.checked
  · exact Case15.checked
  · exact Case16.checked
  · exact Case17.checked
  · exact Case18.checked
  · exact Case19.checked
  · exact Case20.checked
  · exact Case21.checked
theorem weight_checks : ∀ i : Fin 65,
    Legacy.BecknerOnofri.FiniteScalar.scale^2 ≤
      reciprocalUnits 11 (i.val+1)^2 * (i.val+1)^11 := by
  decide +kernel
theorem weight_check {q : ℕ} (h : 1 ≤ q) (h' : q ≤ 65) :
    Legacy.BecknerOnofri.FiniteScalar.scale^2 ≤ reciprocalUnits 11 q^2 * q^11 := by
  have hh := weight_checks ⟨q-1, by omega⟩
  simpa [Nat.sub_add_cancel h] using hh
#print axioms checks
#print axioms weight_check
end BecknerOnofri.HighDim.Eleven.ScalarFinite
