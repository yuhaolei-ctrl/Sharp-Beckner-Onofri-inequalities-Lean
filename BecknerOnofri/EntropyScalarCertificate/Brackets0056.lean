import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0140
import BecknerOnofri.EntropyScalarCertificate.Bessel0141
import BecknerOnofri.EntropyScalarCertificate.Bessel0142
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0056
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0896b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨0,by decide⟩
def lo0896b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨1,by decide⟩
def lo0896 : CheckedMoment :=
  CheckedMoment.ofBessel lo0896b1 lo0896b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0896b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨5,by decide⟩
def hi0896b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨6,by decide⟩
def hi0896 : CheckedMoment :=
  CheckedMoment.ofBessel hi0896b1 hi0896b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0896 : meanBracketCheck (189/500) lo0896 hi0896=true := by decide +kernel
def bracket0896 : MeanBracket := meanBracketOfMoments (189/500) lo0896 hi0896 accepted0896
def lo0897b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨10,by decide⟩
def lo0897b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨11,by decide⟩
def lo0897 : CheckedMoment :=
  CheckedMoment.ofBessel lo0897b1 lo0897b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0897b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨15,by decide⟩
def hi0897b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨16,by decide⟩
def hi0897 : CheckedMoment :=
  CheckedMoment.ofBessel hi0897b1 hi0897b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0897 : meanBracketCheck (379/1000) lo0897 hi0897=true := by decide +kernel
def bracket0897 : MeanBracket := meanBracketOfMoments (379/1000) lo0897 hi0897 accepted0897
def lo0898b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨20,by decide⟩
def lo0898b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨21,by decide⟩
def lo0898 : CheckedMoment :=
  CheckedMoment.ofBessel lo0898b1 lo0898b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0898b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨25,by decide⟩
def hi0898b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨26,by decide⟩
def hi0898 : CheckedMoment :=
  CheckedMoment.ofBessel hi0898b1 hi0898b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0898 : meanBracketCheck (19/50) lo0898 hi0898=true := by decide +kernel
def bracket0898 : MeanBracket := meanBracketOfMoments (19/50) lo0898 hi0898 accepted0898
def lo0899b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨30,by decide⟩
def lo0899b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨31,by decide⟩
def lo0899 : CheckedMoment :=
  CheckedMoment.ofBessel lo0899b1 lo0899b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0899b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨35,by decide⟩
def hi0899b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨36,by decide⟩
def hi0899 : CheckedMoment :=
  CheckedMoment.ofBessel hi0899b1 hi0899b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0899 : meanBracketCheck (381/1000) lo0899 hi0899=true := by decide +kernel
def bracket0899 : MeanBracket := meanBracketOfMoments (381/1000) lo0899 hi0899 accepted0899
def lo0900b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨40,by decide⟩
def lo0900b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨41,by decide⟩
def lo0900 : CheckedMoment :=
  CheckedMoment.ofBessel lo0900b1 lo0900b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0900b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨45,by decide⟩
def hi0900b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨46,by decide⟩
def hi0900 : CheckedMoment :=
  CheckedMoment.ofBessel hi0900b1 hi0900b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0900 : meanBracketCheck (191/500) lo0900 hi0900=true := by decide +kernel
def bracket0900 : MeanBracket := meanBracketOfMoments (191/500) lo0900 hi0900 accepted0900
def lo0901b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨50,by decide⟩
def lo0901b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨51,by decide⟩
def lo0901 : CheckedMoment :=
  CheckedMoment.ofBessel lo0901b1 lo0901b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0901b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨55,by decide⟩
def hi0901b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨56,by decide⟩
def hi0901 : CheckedMoment :=
  CheckedMoment.ofBessel hi0901b1 hi0901b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0901 : meanBracketCheck (383/1000) lo0901 hi0901=true := by decide +kernel
def bracket0901 : MeanBracket := meanBracketOfMoments (383/1000) lo0901 hi0901 accepted0901
def lo0902b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨60,by decide⟩
def lo0902b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨61,by decide⟩
def lo0902 : CheckedMoment :=
  CheckedMoment.ofBessel lo0902b1 lo0902b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0902b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨1,by decide⟩
def hi0902b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨2,by decide⟩
def hi0902 : CheckedMoment :=
  CheckedMoment.ofBessel hi0902b1 hi0902b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0902 : meanBracketCheck (48/125) lo0902 hi0902=true := by decide +kernel
def bracket0902 : MeanBracket := meanBracketOfMoments (48/125) lo0902 hi0902 accepted0902
def lo0903b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨6,by decide⟩
def lo0903b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨7,by decide⟩
def lo0903 : CheckedMoment :=
  CheckedMoment.ofBessel lo0903b1 lo0903b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0903b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨11,by decide⟩
def hi0903b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨12,by decide⟩
def hi0903 : CheckedMoment :=
  CheckedMoment.ofBessel hi0903b1 hi0903b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0903 : meanBracketCheck (77/200) lo0903 hi0903=true := by decide +kernel
def bracket0903 : MeanBracket := meanBracketOfMoments (77/200) lo0903 hi0903 accepted0903
def lo0904b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨16,by decide⟩
def lo0904b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨17,by decide⟩
def lo0904 : CheckedMoment :=
  CheckedMoment.ofBessel lo0904b1 lo0904b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0904b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨21,by decide⟩
def hi0904b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨22,by decide⟩
def hi0904 : CheckedMoment :=
  CheckedMoment.ofBessel hi0904b1 hi0904b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0904 : meanBracketCheck (193/500) lo0904 hi0904=true := by decide +kernel
def bracket0904 : MeanBracket := meanBracketOfMoments (193/500) lo0904 hi0904 accepted0904
def lo0905b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨26,by decide⟩
def lo0905b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨27,by decide⟩
def lo0905 : CheckedMoment :=
  CheckedMoment.ofBessel lo0905b1 lo0905b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0905b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨31,by decide⟩
def hi0905b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨32,by decide⟩
def hi0905 : CheckedMoment :=
  CheckedMoment.ofBessel hi0905b1 hi0905b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0905 : meanBracketCheck (387/1000) lo0905 hi0905=true := by decide +kernel
def bracket0905 : MeanBracket := meanBracketOfMoments (387/1000) lo0905 hi0905 accepted0905
def lo0906b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨36,by decide⟩
def lo0906b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨37,by decide⟩
def lo0906 : CheckedMoment :=
  CheckedMoment.ofBessel lo0906b1 lo0906b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0906b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨41,by decide⟩
def hi0906b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨42,by decide⟩
def hi0906 : CheckedMoment :=
  CheckedMoment.ofBessel hi0906b1 hi0906b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0906 : meanBracketCheck (97/250) lo0906 hi0906=true := by decide +kernel
def bracket0906 : MeanBracket := meanBracketOfMoments (97/250) lo0906 hi0906 accepted0906
def lo0907b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨46,by decide⟩
def lo0907b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨47,by decide⟩
def lo0907 : CheckedMoment :=
  CheckedMoment.ofBessel lo0907b1 lo0907b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0907b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨51,by decide⟩
def hi0907b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨52,by decide⟩
def hi0907 : CheckedMoment :=
  CheckedMoment.ofBessel hi0907b1 hi0907b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0907 : meanBracketCheck (389/1000) lo0907 hi0907=true := by decide +kernel
def bracket0907 : MeanBracket := meanBracketOfMoments (389/1000) lo0907 hi0907 accepted0907
def lo0908b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨56,by decide⟩
def lo0908b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨57,by decide⟩
def lo0908 : CheckedMoment :=
  CheckedMoment.ofBessel lo0908b1 lo0908b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0908b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨61,by decide⟩
def hi0908b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨62,by decide⟩
def hi0908 : CheckedMoment :=
  CheckedMoment.ofBessel hi0908b1 hi0908b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0908 : meanBracketCheck (39/100) lo0908 hi0908=true := by decide +kernel
def bracket0908 : MeanBracket := meanBracketOfMoments (39/100) lo0908 hi0908 accepted0908
def lo0909b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨2,by decide⟩
def lo0909b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨3,by decide⟩
def lo0909 : CheckedMoment :=
  CheckedMoment.ofBessel lo0909b1 lo0909b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0909b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨7,by decide⟩
def hi0909b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨8,by decide⟩
def hi0909 : CheckedMoment :=
  CheckedMoment.ofBessel hi0909b1 hi0909b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0909 : meanBracketCheck (391/1000) lo0909 hi0909=true := by decide +kernel
def bracket0909 : MeanBracket := meanBracketOfMoments (391/1000) lo0909 hi0909 accepted0909
def lo0910b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨12,by decide⟩
def lo0910b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨13,by decide⟩
def lo0910 : CheckedMoment :=
  CheckedMoment.ofBessel lo0910b1 lo0910b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0910b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨17,by decide⟩
def hi0910b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨18,by decide⟩
def hi0910 : CheckedMoment :=
  CheckedMoment.ofBessel hi0910b1 hi0910b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0910 : meanBracketCheck (49/125) lo0910 hi0910=true := by decide +kernel
def bracket0910 : MeanBracket := meanBracketOfMoments (49/125) lo0910 hi0910 accepted0910
def lo0911b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨22,by decide⟩
def lo0911b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨23,by decide⟩
def lo0911 : CheckedMoment :=
  CheckedMoment.ofBessel lo0911b1 lo0911b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0911b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨27,by decide⟩
def hi0911b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨28,by decide⟩
def hi0911 : CheckedMoment :=
  CheckedMoment.ofBessel hi0911b1 hi0911b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0911 : meanBracketCheck (393/1000) lo0911 hi0911=true := by decide +kernel
def bracket0911 : MeanBracket := meanBracketOfMoments (393/1000) lo0911 hi0911 accepted0911
#print axioms bracket0896
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0056
