module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0437
public import BecknerOnofri.EntropyScalarCertificate.Bessel0438
public import BecknerOnofri.EntropyScalarCertificate.Bessel0439

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0175
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2800b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨32,by decide⟩
def lo2800b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨33,by decide⟩
def lo2800 : CheckedMoment :=
  CheckedMoment.ofBessel lo2800b1 lo2800b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2800b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨37,by decide⟩
def hi2800b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨38,by decide⟩
def hi2800 : CheckedMoment :=
  CheckedMoment.ofBessel hi2800b1 hi2800b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2800 : meanBracketCheck (12467/12500) lo2800 hi2800=true := by decide +kernel
def bracket2800 : MeanBracket := meanBracketOfMoments (12467/12500) lo2800 hi2800 accepted2800
def lo2801b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨42,by decide⟩
def lo2801b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨43,by decide⟩
def lo2801 : CheckedMoment :=
  CheckedMoment.ofBessel lo2801b1 lo2801b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2801b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨47,by decide⟩
def hi2801b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨48,by decide⟩
def hi2801 : CheckedMoment :=
  CheckedMoment.ofBessel hi2801b1 hi2801b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2801 : meanBracketCheck (199473/200000) lo2801 hi2801=true := by decide +kernel
def bracket2801 : MeanBracket := meanBracketOfMoments (199473/200000) lo2801 hi2801 accepted2801
def lo2802b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨52,by decide⟩
def lo2802b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨53,by decide⟩
def lo2802 : CheckedMoment :=
  CheckedMoment.ofBessel lo2802b1 lo2802b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2802b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨57,by decide⟩
def hi2802b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨58,by decide⟩
def hi2802 : CheckedMoment :=
  CheckedMoment.ofBessel hi2802b1 hi2802b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2802 : meanBracketCheck (99737/100000) lo2802 hi2802=true := by decide +kernel
def bracket2802 : MeanBracket := meanBracketOfMoments (99737/100000) lo2802 hi2802 accepted2802
def lo2803b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨62,by decide⟩
def lo2803b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨63,by decide⟩
def lo2803 : CheckedMoment :=
  CheckedMoment.ofBessel lo2803b1 lo2803b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2803b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨3,by decide⟩
def hi2803b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨4,by decide⟩
def hi2803 : CheckedMoment :=
  CheckedMoment.ofBessel hi2803b1 hi2803b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2803 : meanBracketCheck (7979/8000) lo2803 hi2803=true := by decide +kernel
def bracket2803 : MeanBracket := meanBracketOfMoments (7979/8000) lo2803 hi2803 accepted2803
def lo2804b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨8,by decide⟩
def lo2804b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨9,by decide⟩
def lo2804 : CheckedMoment :=
  CheckedMoment.ofBessel lo2804b1 lo2804b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2804b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨13,by decide⟩
def hi2804b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨14,by decide⟩
def hi2804 : CheckedMoment :=
  CheckedMoment.ofBessel hi2804b1 hi2804b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2804 : meanBracketCheck (49869/50000) lo2804 hi2804=true := by decide +kernel
def bracket2804 : MeanBracket := meanBracketOfMoments (49869/50000) lo2804 hi2804 accepted2804
def lo2805b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨18,by decide⟩
def lo2805b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨19,by decide⟩
def lo2805 : CheckedMoment :=
  CheckedMoment.ofBessel lo2805b1 lo2805b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2805b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨23,by decide⟩
def hi2805b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨24,by decide⟩
def hi2805 : CheckedMoment :=
  CheckedMoment.ofBessel hi2805b1 hi2805b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2805 : meanBracketCheck (199477/200000) lo2805 hi2805=true := by decide +kernel
def bracket2805 : MeanBracket := meanBracketOfMoments (199477/200000) lo2805 hi2805 accepted2805
def lo2806b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨28,by decide⟩
def lo2806b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨29,by decide⟩
def lo2806 : CheckedMoment :=
  CheckedMoment.ofBessel lo2806b1 lo2806b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2806b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨33,by decide⟩
def hi2806b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨34,by decide⟩
def hi2806 : CheckedMoment :=
  CheckedMoment.ofBessel hi2806b1 hi2806b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2806 : meanBracketCheck (99739/100000) lo2806 hi2806=true := by decide +kernel
def bracket2806 : MeanBracket := meanBracketOfMoments (99739/100000) lo2806 hi2806 accepted2806
def lo2807b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨38,by decide⟩
def lo2807b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨39,by decide⟩
def lo2807 : CheckedMoment :=
  CheckedMoment.ofBessel lo2807b1 lo2807b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2807b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨43,by decide⟩
def hi2807b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨44,by decide⟩
def hi2807 : CheckedMoment :=
  CheckedMoment.ofBessel hi2807b1 hi2807b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2807 : meanBracketCheck (199479/200000) lo2807 hi2807=true := by decide +kernel
def bracket2807 : MeanBracket := meanBracketOfMoments (199479/200000) lo2807 hi2807 accepted2807
def lo2808b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨48,by decide⟩
def lo2808b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨49,by decide⟩
def lo2808 : CheckedMoment :=
  CheckedMoment.ofBessel lo2808b1 lo2808b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2808b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨53,by decide⟩
def hi2808b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨54,by decide⟩
def hi2808 : CheckedMoment :=
  CheckedMoment.ofBessel hi2808b1 hi2808b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2808 : meanBracketCheck (4987/5000) lo2808 hi2808=true := by decide +kernel
def bracket2808 : MeanBracket := meanBracketOfMoments (4987/5000) lo2808 hi2808 accepted2808
def lo2809b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨58,by decide⟩
def lo2809b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨59,by decide⟩
def lo2809 : CheckedMoment :=
  CheckedMoment.ofBessel lo2809b1 lo2809b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2809b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨63,by decide⟩
def hi2809b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨0,by decide⟩
def hi2809 : CheckedMoment :=
  CheckedMoment.ofBessel hi2809b1 hi2809b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2809 : meanBracketCheck (199481/200000) lo2809 hi2809=true := by decide +kernel
def bracket2809 : MeanBracket := meanBracketOfMoments (199481/200000) lo2809 hi2809 accepted2809
def lo2810b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨4,by decide⟩
def lo2810b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨5,by decide⟩
def lo2810 : CheckedMoment :=
  CheckedMoment.ofBessel lo2810b1 lo2810b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2810b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨9,by decide⟩
def hi2810b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨10,by decide⟩
def hi2810 : CheckedMoment :=
  CheckedMoment.ofBessel hi2810b1 hi2810b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2810 : meanBracketCheck (99741/100000) lo2810 hi2810=true := by decide +kernel
def bracket2810 : MeanBracket := meanBracketOfMoments (99741/100000) lo2810 hi2810 accepted2810
def lo2811b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨14,by decide⟩
def lo2811b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨15,by decide⟩
def lo2811 : CheckedMoment :=
  CheckedMoment.ofBessel lo2811b1 lo2811b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2811b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨19,by decide⟩
def hi2811b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨20,by decide⟩
def hi2811 : CheckedMoment :=
  CheckedMoment.ofBessel hi2811b1 hi2811b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2811 : meanBracketCheck (199483/200000) lo2811 hi2811=true := by decide +kernel
def bracket2811 : MeanBracket := meanBracketOfMoments (199483/200000) lo2811 hi2811 accepted2811
def lo2812b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨24,by decide⟩
def lo2812b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨25,by decide⟩
def lo2812 : CheckedMoment :=
  CheckedMoment.ofBessel lo2812b1 lo2812b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2812b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨29,by decide⟩
def hi2812b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨30,by decide⟩
def hi2812 : CheckedMoment :=
  CheckedMoment.ofBessel hi2812b1 hi2812b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2812 : meanBracketCheck (49871/50000) lo2812 hi2812=true := by decide +kernel
def bracket2812 : MeanBracket := meanBracketOfMoments (49871/50000) lo2812 hi2812 accepted2812
def lo2813b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨34,by decide⟩
def lo2813b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨35,by decide⟩
def lo2813 : CheckedMoment :=
  CheckedMoment.ofBessel lo2813b1 lo2813b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2813b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨39,by decide⟩
def hi2813b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨40,by decide⟩
def hi2813 : CheckedMoment :=
  CheckedMoment.ofBessel hi2813b1 hi2813b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2813 : meanBracketCheck (39897/40000) lo2813 hi2813=true := by decide +kernel
def bracket2813 : MeanBracket := meanBracketOfMoments (39897/40000) lo2813 hi2813 accepted2813
def lo2814b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨44,by decide⟩
def lo2814b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨45,by decide⟩
def lo2814 : CheckedMoment :=
  CheckedMoment.ofBessel lo2814b1 lo2814b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2814b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨49,by decide⟩
def hi2814b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨50,by decide⟩
def hi2814 : CheckedMoment :=
  CheckedMoment.ofBessel hi2814b1 hi2814b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2814 : meanBracketCheck (99743/100000) lo2814 hi2814=true := by decide +kernel
def bracket2814 : MeanBracket := meanBracketOfMoments (99743/100000) lo2814 hi2814 accepted2814
def lo2815b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨54,by decide⟩
def lo2815b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨55,by decide⟩
def lo2815 : CheckedMoment :=
  CheckedMoment.ofBessel lo2815b1 lo2815b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2815b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨59,by decide⟩
def hi2815b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0439.rows BesselBatch0439.accepted ⟨60,by decide⟩
def hi2815 : CheckedMoment :=
  CheckedMoment.ofBessel hi2815b1 hi2815b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2815 : meanBracketCheck (199487/200000) lo2815 hi2815=true := by decide +kernel
def bracket2815 : MeanBracket := meanBracketOfMoments (199487/200000) lo2815 hi2815 accepted2815
#print axioms bracket2800
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0175
