module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0152
public import BecknerOnofri.EntropyScalarCertificate.Bessel0153
public import BecknerOnofri.EntropyScalarCertificate.Bessel0154

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0061
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0976b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨32,by decide⟩
def lo0976b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨33,by decide⟩
def lo0976 : CheckedMoment :=
  CheckedMoment.ofBessel lo0976b1 lo0976b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0976b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨37,by decide⟩
def hi0976b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨38,by decide⟩
def hi0976 : CheckedMoment :=
  CheckedMoment.ofBessel hi0976b1 hi0976b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0976 : meanBracketCheck (229/500) lo0976 hi0976=true := by decide +kernel
def bracket0976 : MeanBracket := meanBracketOfMoments (229/500) lo0976 hi0976 accepted0976
def lo0977b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨42,by decide⟩
def lo0977b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨43,by decide⟩
def lo0977 : CheckedMoment :=
  CheckedMoment.ofBessel lo0977b1 lo0977b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0977b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨47,by decide⟩
def hi0977b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨48,by decide⟩
def hi0977 : CheckedMoment :=
  CheckedMoment.ofBessel hi0977b1 hi0977b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0977 : meanBracketCheck (459/1000) lo0977 hi0977=true := by decide +kernel
def bracket0977 : MeanBracket := meanBracketOfMoments (459/1000) lo0977 hi0977 accepted0977
def lo0978b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨52,by decide⟩
def lo0978b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨53,by decide⟩
def lo0978 : CheckedMoment :=
  CheckedMoment.ofBessel lo0978b1 lo0978b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0978b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨57,by decide⟩
def hi0978b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨58,by decide⟩
def hi0978 : CheckedMoment :=
  CheckedMoment.ofBessel hi0978b1 hi0978b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0978 : meanBracketCheck (23/50) lo0978 hi0978=true := by decide +kernel
def bracket0978 : MeanBracket := meanBracketOfMoments (23/50) lo0978 hi0978 accepted0978
def lo0979b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨62,by decide⟩
def lo0979b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨63,by decide⟩
def lo0979 : CheckedMoment :=
  CheckedMoment.ofBessel lo0979b1 lo0979b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0979b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨3,by decide⟩
def hi0979b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨4,by decide⟩
def hi0979 : CheckedMoment :=
  CheckedMoment.ofBessel hi0979b1 hi0979b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0979 : meanBracketCheck (461/1000) lo0979 hi0979=true := by decide +kernel
def bracket0979 : MeanBracket := meanBracketOfMoments (461/1000) lo0979 hi0979 accepted0979
def lo0980b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨8,by decide⟩
def lo0980b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨9,by decide⟩
def lo0980 : CheckedMoment :=
  CheckedMoment.ofBessel lo0980b1 lo0980b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0980b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨13,by decide⟩
def hi0980b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨14,by decide⟩
def hi0980 : CheckedMoment :=
  CheckedMoment.ofBessel hi0980b1 hi0980b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0980 : meanBracketCheck (231/500) lo0980 hi0980=true := by decide +kernel
def bracket0980 : MeanBracket := meanBracketOfMoments (231/500) lo0980 hi0980 accepted0980
def lo0981b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨18,by decide⟩
def lo0981b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨19,by decide⟩
def lo0981 : CheckedMoment :=
  CheckedMoment.ofBessel lo0981b1 lo0981b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0981b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨23,by decide⟩
def hi0981b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨24,by decide⟩
def hi0981 : CheckedMoment :=
  CheckedMoment.ofBessel hi0981b1 hi0981b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0981 : meanBracketCheck (463/1000) lo0981 hi0981=true := by decide +kernel
def bracket0981 : MeanBracket := meanBracketOfMoments (463/1000) lo0981 hi0981 accepted0981
def lo0982b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨28,by decide⟩
def lo0982b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨29,by decide⟩
def lo0982 : CheckedMoment :=
  CheckedMoment.ofBessel lo0982b1 lo0982b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0982b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨33,by decide⟩
def hi0982b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨34,by decide⟩
def hi0982 : CheckedMoment :=
  CheckedMoment.ofBessel hi0982b1 hi0982b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0982 : meanBracketCheck (58/125) lo0982 hi0982=true := by decide +kernel
def bracket0982 : MeanBracket := meanBracketOfMoments (58/125) lo0982 hi0982 accepted0982
def lo0983b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨38,by decide⟩
def lo0983b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨39,by decide⟩
def lo0983 : CheckedMoment :=
  CheckedMoment.ofBessel lo0983b1 lo0983b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0983b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨43,by decide⟩
def hi0983b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨44,by decide⟩
def hi0983 : CheckedMoment :=
  CheckedMoment.ofBessel hi0983b1 hi0983b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0983 : meanBracketCheck (93/200) lo0983 hi0983=true := by decide +kernel
def bracket0983 : MeanBracket := meanBracketOfMoments (93/200) lo0983 hi0983 accepted0983
def lo0984b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨48,by decide⟩
def lo0984b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨49,by decide⟩
def lo0984 : CheckedMoment :=
  CheckedMoment.ofBessel lo0984b1 lo0984b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0984b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨53,by decide⟩
def hi0984b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨54,by decide⟩
def hi0984 : CheckedMoment :=
  CheckedMoment.ofBessel hi0984b1 hi0984b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0984 : meanBracketCheck (233/500) lo0984 hi0984=true := by decide +kernel
def bracket0984 : MeanBracket := meanBracketOfMoments (233/500) lo0984 hi0984 accepted0984
def lo0985b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨58,by decide⟩
def lo0985b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨59,by decide⟩
def lo0985 : CheckedMoment :=
  CheckedMoment.ofBessel lo0985b1 lo0985b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0985b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨63,by decide⟩
def hi0985b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨0,by decide⟩
def hi0985 : CheckedMoment :=
  CheckedMoment.ofBessel hi0985b1 hi0985b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0985 : meanBracketCheck (467/1000) lo0985 hi0985=true := by decide +kernel
def bracket0985 : MeanBracket := meanBracketOfMoments (467/1000) lo0985 hi0985 accepted0985
def lo0986b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨4,by decide⟩
def lo0986b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨5,by decide⟩
def lo0986 : CheckedMoment :=
  CheckedMoment.ofBessel lo0986b1 lo0986b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0986b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨9,by decide⟩
def hi0986b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨10,by decide⟩
def hi0986 : CheckedMoment :=
  CheckedMoment.ofBessel hi0986b1 hi0986b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0986 : meanBracketCheck (117/250) lo0986 hi0986=true := by decide +kernel
def bracket0986 : MeanBracket := meanBracketOfMoments (117/250) lo0986 hi0986 accepted0986
def lo0987b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨14,by decide⟩
def lo0987b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨15,by decide⟩
def lo0987 : CheckedMoment :=
  CheckedMoment.ofBessel lo0987b1 lo0987b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0987b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨19,by decide⟩
def hi0987b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨20,by decide⟩
def hi0987 : CheckedMoment :=
  CheckedMoment.ofBessel hi0987b1 hi0987b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0987 : meanBracketCheck (469/1000) lo0987 hi0987=true := by decide +kernel
def bracket0987 : MeanBracket := meanBracketOfMoments (469/1000) lo0987 hi0987 accepted0987
def lo0988b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨24,by decide⟩
def lo0988b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨25,by decide⟩
def lo0988 : CheckedMoment :=
  CheckedMoment.ofBessel lo0988b1 lo0988b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0988b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨29,by decide⟩
def hi0988b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨30,by decide⟩
def hi0988 : CheckedMoment :=
  CheckedMoment.ofBessel hi0988b1 hi0988b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0988 : meanBracketCheck (47/100) lo0988 hi0988=true := by decide +kernel
def bracket0988 : MeanBracket := meanBracketOfMoments (47/100) lo0988 hi0988 accepted0988
def lo0989b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨34,by decide⟩
def lo0989b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨35,by decide⟩
def lo0989 : CheckedMoment :=
  CheckedMoment.ofBessel lo0989b1 lo0989b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0989b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨39,by decide⟩
def hi0989b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨40,by decide⟩
def hi0989 : CheckedMoment :=
  CheckedMoment.ofBessel hi0989b1 hi0989b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0989 : meanBracketCheck (471/1000) lo0989 hi0989=true := by decide +kernel
def bracket0989 : MeanBracket := meanBracketOfMoments (471/1000) lo0989 hi0989 accepted0989
def lo0990b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨44,by decide⟩
def lo0990b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨45,by decide⟩
def lo0990 : CheckedMoment :=
  CheckedMoment.ofBessel lo0990b1 lo0990b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0990b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨49,by decide⟩
def hi0990b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨50,by decide⟩
def hi0990 : CheckedMoment :=
  CheckedMoment.ofBessel hi0990b1 hi0990b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0990 : meanBracketCheck (59/125) lo0990 hi0990=true := by decide +kernel
def bracket0990 : MeanBracket := meanBracketOfMoments (59/125) lo0990 hi0990 accepted0990
def lo0991b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨54,by decide⟩
def lo0991b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨55,by decide⟩
def lo0991 : CheckedMoment :=
  CheckedMoment.ofBessel lo0991b1 lo0991b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0991b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨59,by decide⟩
def hi0991b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0154.rows BesselBatch0154.accepted ⟨60,by decide⟩
def hi0991 : CheckedMoment :=
  CheckedMoment.ofBessel hi0991b1 hi0991b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0991 : meanBracketCheck (473/1000) lo0991 hi0991=true := by decide +kernel
def bracket0991 : MeanBracket := meanBracketOfMoments (473/1000) lo0991 hi0991 accepted0991
#print axioms bracket0976
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0061
