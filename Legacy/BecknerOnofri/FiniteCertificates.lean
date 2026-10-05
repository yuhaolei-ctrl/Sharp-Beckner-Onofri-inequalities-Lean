import Legacy.BecknerOnofri.FiniteData01
import Legacy.BecknerOnofri.FiniteData02
import Legacy.BecknerOnofri.FiniteData03
import Legacy.BecknerOnofri.FiniteData04
import Legacy.BecknerOnofri.FiniteData05
import Legacy.BecknerOnofri.FiniteData06
import Legacy.BecknerOnofri.FiniteData07
import Legacy.BecknerOnofri.FiniteData08
import Legacy.BecknerOnofri.FiniteData09
import Legacy.BecknerOnofri.FiniteData10
import Legacy.BecknerOnofri.FiniteData11
import Legacy.BecknerOnofri.FiniteData12
import Legacy.BecknerOnofri.FiniteData13
import Legacy.BecknerOnofri.FiniteData14
import Legacy.BecknerOnofri.FiniteData15
import Legacy.BecknerOnofri.FiniteData16
import Legacy.BecknerOnofri.FiniteData17
import Legacy.BecknerOnofri.FiniteData18
import Legacy.BecknerOnofri.FiniteData19
import Legacy.BecknerOnofri.FiniteData20
import Legacy.BecknerOnofri.FiniteData21
namespace Legacy.BecknerOnofri.FiniteScalar
theorem finite_checks : ∀ j : Fin 21, ∀ i : Fin 8, FiniteCheck (i.val+3) (j.val+1) := by
  intro j
  fin_cases j
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
theorem finite_check {d n : Nat} (hd : 3 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n) (hn21 : n ≤ 21) : FiniteCheck d n := by
  have h := finite_checks ⟨n-1, by omega⟩ ⟨d-3, by omega⟩
  simpa only [Nat.sub_add_cancel hd, Nat.sub_add_cancel hn] using h
#print axioms finite_check
end Legacy.BecknerOnofri.FiniteScalar
