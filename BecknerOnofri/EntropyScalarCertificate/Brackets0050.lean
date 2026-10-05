import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0125
import BecknerOnofri.EntropyScalarCertificate.Bessel0126
import BecknerOnofri.EntropyScalarCertificate.Bessel0127
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0050
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0800b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨0,by decide⟩
def lo0800b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨1,by decide⟩
def lo0800 : CheckedMoment :=
  CheckedMoment.ofBessel lo0800b1 lo0800b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0800b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨5,by decide⟩
def hi0800b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨6,by decide⟩
def hi0800 : CheckedMoment :=
  CheckedMoment.ofBessel hi0800b1 hi0800b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0800 : meanBracketCheck (141/500) lo0800 hi0800=true := by decide +kernel
def bracket0800 : MeanBracket := meanBracketOfMoments (141/500) lo0800 hi0800 accepted0800
def lo0801b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨10,by decide⟩
def lo0801b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨11,by decide⟩
def lo0801 : CheckedMoment :=
  CheckedMoment.ofBessel lo0801b1 lo0801b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0801b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨15,by decide⟩
def hi0801b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨16,by decide⟩
def hi0801 : CheckedMoment :=
  CheckedMoment.ofBessel hi0801b1 hi0801b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0801 : meanBracketCheck (283/1000) lo0801 hi0801=true := by decide +kernel
def bracket0801 : MeanBracket := meanBracketOfMoments (283/1000) lo0801 hi0801 accepted0801
def lo0802b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨20,by decide⟩
def lo0802b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨21,by decide⟩
def lo0802 : CheckedMoment :=
  CheckedMoment.ofBessel lo0802b1 lo0802b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0802b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨25,by decide⟩
def hi0802b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨26,by decide⟩
def hi0802 : CheckedMoment :=
  CheckedMoment.ofBessel hi0802b1 hi0802b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0802 : meanBracketCheck (71/250) lo0802 hi0802=true := by decide +kernel
def bracket0802 : MeanBracket := meanBracketOfMoments (71/250) lo0802 hi0802 accepted0802
def lo0803b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨30,by decide⟩
def lo0803b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨31,by decide⟩
def lo0803 : CheckedMoment :=
  CheckedMoment.ofBessel lo0803b1 lo0803b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0803b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨35,by decide⟩
def hi0803b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨36,by decide⟩
def hi0803 : CheckedMoment :=
  CheckedMoment.ofBessel hi0803b1 hi0803b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0803 : meanBracketCheck (57/200) lo0803 hi0803=true := by decide +kernel
def bracket0803 : MeanBracket := meanBracketOfMoments (57/200) lo0803 hi0803 accepted0803
def lo0804b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨40,by decide⟩
def lo0804b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨41,by decide⟩
def lo0804 : CheckedMoment :=
  CheckedMoment.ofBessel lo0804b1 lo0804b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0804b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨45,by decide⟩
def hi0804b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨46,by decide⟩
def hi0804 : CheckedMoment :=
  CheckedMoment.ofBessel hi0804b1 hi0804b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0804 : meanBracketCheck (143/500) lo0804 hi0804=true := by decide +kernel
def bracket0804 : MeanBracket := meanBracketOfMoments (143/500) lo0804 hi0804 accepted0804
def lo0805b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨50,by decide⟩
def lo0805b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨51,by decide⟩
def lo0805 : CheckedMoment :=
  CheckedMoment.ofBessel lo0805b1 lo0805b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0805b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨55,by decide⟩
def hi0805b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨56,by decide⟩
def hi0805 : CheckedMoment :=
  CheckedMoment.ofBessel hi0805b1 hi0805b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0805 : meanBracketCheck (287/1000) lo0805 hi0805=true := by decide +kernel
def bracket0805 : MeanBracket := meanBracketOfMoments (287/1000) lo0805 hi0805 accepted0805
def lo0806b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨60,by decide⟩
def lo0806b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨61,by decide⟩
def lo0806 : CheckedMoment :=
  CheckedMoment.ofBessel lo0806b1 lo0806b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0806b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨1,by decide⟩
def hi0806b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨2,by decide⟩
def hi0806 : CheckedMoment :=
  CheckedMoment.ofBessel hi0806b1 hi0806b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0806 : meanBracketCheck (36/125) lo0806 hi0806=true := by decide +kernel
def bracket0806 : MeanBracket := meanBracketOfMoments (36/125) lo0806 hi0806 accepted0806
def lo0807b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨6,by decide⟩
def lo0807b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨7,by decide⟩
def lo0807 : CheckedMoment :=
  CheckedMoment.ofBessel lo0807b1 lo0807b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0807b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨11,by decide⟩
def hi0807b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨12,by decide⟩
def hi0807 : CheckedMoment :=
  CheckedMoment.ofBessel hi0807b1 hi0807b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0807 : meanBracketCheck (289/1000) lo0807 hi0807=true := by decide +kernel
def bracket0807 : MeanBracket := meanBracketOfMoments (289/1000) lo0807 hi0807 accepted0807
def lo0808b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨16,by decide⟩
def lo0808b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨17,by decide⟩
def lo0808 : CheckedMoment :=
  CheckedMoment.ofBessel lo0808b1 lo0808b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0808b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨21,by decide⟩
def hi0808b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨22,by decide⟩
def hi0808 : CheckedMoment :=
  CheckedMoment.ofBessel hi0808b1 hi0808b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0808 : meanBracketCheck (29/100) lo0808 hi0808=true := by decide +kernel
def bracket0808 : MeanBracket := meanBracketOfMoments (29/100) lo0808 hi0808 accepted0808
def lo0809b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨26,by decide⟩
def lo0809b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨27,by decide⟩
def lo0809 : CheckedMoment :=
  CheckedMoment.ofBessel lo0809b1 lo0809b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0809b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨31,by decide⟩
def hi0809b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨32,by decide⟩
def hi0809 : CheckedMoment :=
  CheckedMoment.ofBessel hi0809b1 hi0809b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0809 : meanBracketCheck (291/1000) lo0809 hi0809=true := by decide +kernel
def bracket0809 : MeanBracket := meanBracketOfMoments (291/1000) lo0809 hi0809 accepted0809
def lo0810b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨36,by decide⟩
def lo0810b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨37,by decide⟩
def lo0810 : CheckedMoment :=
  CheckedMoment.ofBessel lo0810b1 lo0810b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0810b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨41,by decide⟩
def hi0810b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨42,by decide⟩
def hi0810 : CheckedMoment :=
  CheckedMoment.ofBessel hi0810b1 hi0810b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0810 : meanBracketCheck (73/250) lo0810 hi0810=true := by decide +kernel
def bracket0810 : MeanBracket := meanBracketOfMoments (73/250) lo0810 hi0810 accepted0810
def lo0811b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨46,by decide⟩
def lo0811b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨47,by decide⟩
def lo0811 : CheckedMoment :=
  CheckedMoment.ofBessel lo0811b1 lo0811b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0811b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨51,by decide⟩
def hi0811b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨52,by decide⟩
def hi0811 : CheckedMoment :=
  CheckedMoment.ofBessel hi0811b1 hi0811b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0811 : meanBracketCheck (293/1000) lo0811 hi0811=true := by decide +kernel
def bracket0811 : MeanBracket := meanBracketOfMoments (293/1000) lo0811 hi0811 accepted0811
def lo0812b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨56,by decide⟩
def lo0812b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨57,by decide⟩
def lo0812 : CheckedMoment :=
  CheckedMoment.ofBessel lo0812b1 lo0812b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0812b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨61,by decide⟩
def hi0812b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨62,by decide⟩
def hi0812 : CheckedMoment :=
  CheckedMoment.ofBessel hi0812b1 hi0812b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0812 : meanBracketCheck (147/500) lo0812 hi0812=true := by decide +kernel
def bracket0812 : MeanBracket := meanBracketOfMoments (147/500) lo0812 hi0812 accepted0812
def lo0813b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨2,by decide⟩
def lo0813b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨3,by decide⟩
def lo0813 : CheckedMoment :=
  CheckedMoment.ofBessel lo0813b1 lo0813b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0813b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨7,by decide⟩
def hi0813b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨8,by decide⟩
def hi0813 : CheckedMoment :=
  CheckedMoment.ofBessel hi0813b1 hi0813b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0813 : meanBracketCheck (59/200) lo0813 hi0813=true := by decide +kernel
def bracket0813 : MeanBracket := meanBracketOfMoments (59/200) lo0813 hi0813 accepted0813
def lo0814b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨12,by decide⟩
def lo0814b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨13,by decide⟩
def lo0814 : CheckedMoment :=
  CheckedMoment.ofBessel lo0814b1 lo0814b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0814b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨17,by decide⟩
def hi0814b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨18,by decide⟩
def hi0814 : CheckedMoment :=
  CheckedMoment.ofBessel hi0814b1 hi0814b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0814 : meanBracketCheck (37/125) lo0814 hi0814=true := by decide +kernel
def bracket0814 : MeanBracket := meanBracketOfMoments (37/125) lo0814 hi0814 accepted0814
def lo0815b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨22,by decide⟩
def lo0815b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨23,by decide⟩
def lo0815 : CheckedMoment :=
  CheckedMoment.ofBessel lo0815b1 lo0815b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0815b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨27,by decide⟩
def hi0815b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨28,by decide⟩
def hi0815 : CheckedMoment :=
  CheckedMoment.ofBessel hi0815b1 hi0815b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0815 : meanBracketCheck (297/1000) lo0815 hi0815=true := by decide +kernel
def bracket0815 : MeanBracket := meanBracketOfMoments (297/1000) lo0815 hi0815 accepted0815
#print axioms bracket0800
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0050
