import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0010
import BecknerOnofri.EntropyScalarCertificate.Bessel0011
import BecknerOnofri.EntropyScalarCertificate.Bessel0012
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0004
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0064b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨0,by decide⟩
def lo0064b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨1,by decide⟩
def lo0064 : CheckedMoment :=
  CheckedMoment.ofBessel lo0064b1 lo0064b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0064b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨5,by decide⟩
def hi0064b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨6,by decide⟩
def hi0064 : CheckedMoment :=
  CheckedMoment.ofBessel hi0064b1 hi0064b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0064 : meanBracketCheck (693/10000) lo0064 hi0064=true := by decide +kernel
def bracket0064 : MeanBracket := meanBracketOfMoments (693/10000) lo0064 hi0064 accepted0064
def lo0065b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨10,by decide⟩
def lo0065b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨11,by decide⟩
def lo0065 : CheckedMoment :=
  CheckedMoment.ofBessel lo0065b1 lo0065b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0065b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨15,by decide⟩
def hi0065b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨16,by decide⟩
def hi0065 : CheckedMoment :=
  CheckedMoment.ofBessel hi0065b1 hi0065b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0065 : meanBracketCheck (139/2000) lo0065 hi0065=true := by decide +kernel
def bracket0065 : MeanBracket := meanBracketOfMoments (139/2000) lo0065 hi0065 accepted0065
def lo0066b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨20,by decide⟩
def lo0066b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨21,by decide⟩
def lo0066 : CheckedMoment :=
  CheckedMoment.ofBessel lo0066b1 lo0066b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0066b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨25,by decide⟩
def hi0066b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨26,by decide⟩
def hi0066 : CheckedMoment :=
  CheckedMoment.ofBessel hi0066b1 hi0066b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0066 : meanBracketCheck (697/10000) lo0066 hi0066=true := by decide +kernel
def bracket0066 : MeanBracket := meanBracketOfMoments (697/10000) lo0066 hi0066 accepted0066
def lo0067b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨30,by decide⟩
def lo0067b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨31,by decide⟩
def lo0067 : CheckedMoment :=
  CheckedMoment.ofBessel lo0067b1 lo0067b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0067b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨35,by decide⟩
def hi0067b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨36,by decide⟩
def hi0067 : CheckedMoment :=
  CheckedMoment.ofBessel hi0067b1 hi0067b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0067 : meanBracketCheck (699/10000) lo0067 hi0067=true := by decide +kernel
def bracket0067 : MeanBracket := meanBracketOfMoments (699/10000) lo0067 hi0067 accepted0067
def lo0068b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨40,by decide⟩
def lo0068b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨41,by decide⟩
def lo0068 : CheckedMoment :=
  CheckedMoment.ofBessel lo0068b1 lo0068b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0068b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨45,by decide⟩
def hi0068b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨46,by decide⟩
def hi0068 : CheckedMoment :=
  CheckedMoment.ofBessel hi0068b1 hi0068b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0068 : meanBracketCheck (701/10000) lo0068 hi0068=true := by decide +kernel
def bracket0068 : MeanBracket := meanBracketOfMoments (701/10000) lo0068 hi0068 accepted0068
def lo0069b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨50,by decide⟩
def lo0069b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨51,by decide⟩
def lo0069 : CheckedMoment :=
  CheckedMoment.ofBessel lo0069b1 lo0069b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0069b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨55,by decide⟩
def hi0069b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨56,by decide⟩
def hi0069 : CheckedMoment :=
  CheckedMoment.ofBessel hi0069b1 hi0069b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0069 : meanBracketCheck (703/10000) lo0069 hi0069=true := by decide +kernel
def bracket0069 : MeanBracket := meanBracketOfMoments (703/10000) lo0069 hi0069 accepted0069
def lo0070b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨60,by decide⟩
def lo0070b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨61,by decide⟩
def lo0070 : CheckedMoment :=
  CheckedMoment.ofBessel lo0070b1 lo0070b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0070b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨1,by decide⟩
def hi0070b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨2,by decide⟩
def hi0070 : CheckedMoment :=
  CheckedMoment.ofBessel hi0070b1 hi0070b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0070 : meanBracketCheck (141/2000) lo0070 hi0070=true := by decide +kernel
def bracket0070 : MeanBracket := meanBracketOfMoments (141/2000) lo0070 hi0070 accepted0070
def lo0071b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨6,by decide⟩
def lo0071b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨7,by decide⟩
def lo0071 : CheckedMoment :=
  CheckedMoment.ofBessel lo0071b1 lo0071b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0071b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨11,by decide⟩
def hi0071b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨12,by decide⟩
def hi0071 : CheckedMoment :=
  CheckedMoment.ofBessel hi0071b1 hi0071b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0071 : meanBracketCheck (707/10000) lo0071 hi0071=true := by decide +kernel
def bracket0071 : MeanBracket := meanBracketOfMoments (707/10000) lo0071 hi0071 accepted0071
def lo0072b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨16,by decide⟩
def lo0072b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨17,by decide⟩
def lo0072 : CheckedMoment :=
  CheckedMoment.ofBessel lo0072b1 lo0072b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0072b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨21,by decide⟩
def hi0072b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨22,by decide⟩
def hi0072 : CheckedMoment :=
  CheckedMoment.ofBessel hi0072b1 hi0072b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0072 : meanBracketCheck (709/10000) lo0072 hi0072=true := by decide +kernel
def bracket0072 : MeanBracket := meanBracketOfMoments (709/10000) lo0072 hi0072 accepted0072
def lo0073b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨26,by decide⟩
def lo0073b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨27,by decide⟩
def lo0073 : CheckedMoment :=
  CheckedMoment.ofBessel lo0073b1 lo0073b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0073b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨31,by decide⟩
def hi0073b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨32,by decide⟩
def hi0073 : CheckedMoment :=
  CheckedMoment.ofBessel hi0073b1 hi0073b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0073 : meanBracketCheck (711/10000) lo0073 hi0073=true := by decide +kernel
def bracket0073 : MeanBracket := meanBracketOfMoments (711/10000) lo0073 hi0073 accepted0073
def lo0074b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨36,by decide⟩
def lo0074b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨37,by decide⟩
def lo0074 : CheckedMoment :=
  CheckedMoment.ofBessel lo0074b1 lo0074b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0074b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨41,by decide⟩
def hi0074b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨42,by decide⟩
def hi0074 : CheckedMoment :=
  CheckedMoment.ofBessel hi0074b1 hi0074b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0074 : meanBracketCheck (713/10000) lo0074 hi0074=true := by decide +kernel
def bracket0074 : MeanBracket := meanBracketOfMoments (713/10000) lo0074 hi0074 accepted0074
def lo0075b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨46,by decide⟩
def lo0075b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨47,by decide⟩
def lo0075 : CheckedMoment :=
  CheckedMoment.ofBessel lo0075b1 lo0075b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0075b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨51,by decide⟩
def hi0075b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨52,by decide⟩
def hi0075 : CheckedMoment :=
  CheckedMoment.ofBessel hi0075b1 hi0075b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0075 : meanBracketCheck (143/2000) lo0075 hi0075=true := by decide +kernel
def bracket0075 : MeanBracket := meanBracketOfMoments (143/2000) lo0075 hi0075 accepted0075
def lo0076b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨56,by decide⟩
def lo0076b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨57,by decide⟩
def lo0076 : CheckedMoment :=
  CheckedMoment.ofBessel lo0076b1 lo0076b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0076b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨61,by decide⟩
def hi0076b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨62,by decide⟩
def hi0076 : CheckedMoment :=
  CheckedMoment.ofBessel hi0076b1 hi0076b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0076 : meanBracketCheck (717/10000) lo0076 hi0076=true := by decide +kernel
def bracket0076 : MeanBracket := meanBracketOfMoments (717/10000) lo0076 hi0076 accepted0076
def lo0077b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨2,by decide⟩
def lo0077b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨3,by decide⟩
def lo0077 : CheckedMoment :=
  CheckedMoment.ofBessel lo0077b1 lo0077b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0077b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨7,by decide⟩
def hi0077b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨8,by decide⟩
def hi0077 : CheckedMoment :=
  CheckedMoment.ofBessel hi0077b1 hi0077b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0077 : meanBracketCheck (719/10000) lo0077 hi0077=true := by decide +kernel
def bracket0077 : MeanBracket := meanBracketOfMoments (719/10000) lo0077 hi0077 accepted0077
def lo0078b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨12,by decide⟩
def lo0078b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨13,by decide⟩
def lo0078 : CheckedMoment :=
  CheckedMoment.ofBessel lo0078b1 lo0078b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0078b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨17,by decide⟩
def hi0078b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨18,by decide⟩
def hi0078 : CheckedMoment :=
  CheckedMoment.ofBessel hi0078b1 hi0078b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0078 : meanBracketCheck (721/10000) lo0078 hi0078=true := by decide +kernel
def bracket0078 : MeanBracket := meanBracketOfMoments (721/10000) lo0078 hi0078 accepted0078
def lo0079b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨22,by decide⟩
def lo0079b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨23,by decide⟩
def lo0079 : CheckedMoment :=
  CheckedMoment.ofBessel lo0079b1 lo0079b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0079b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨27,by decide⟩
def hi0079b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨28,by decide⟩
def hi0079 : CheckedMoment :=
  CheckedMoment.ofBessel hi0079b1 hi0079b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0079 : meanBracketCheck (723/10000) lo0079 hi0079=true := by decide +kernel
def bracket0079 : MeanBracket := meanBracketOfMoments (723/10000) lo0079 hi0079 accepted0079
#print axioms bracket0064
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0004
