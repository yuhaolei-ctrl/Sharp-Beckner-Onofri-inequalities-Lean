module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0307
public import BecknerOnofri.EntropyScalarCertificate.Bessel0308
public import BecknerOnofri.EntropyScalarCertificate.Bessel0309

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0123
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1968b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨32,by decide⟩
def lo1968b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨33,by decide⟩
def lo1968 : CheckedMoment :=
  CheckedMoment.ofBessel lo1968b1 lo1968b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1968b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨37,by decide⟩
def hi1968b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨38,by decide⟩
def hi1968 : CheckedMoment :=
  CheckedMoment.ofBessel hi1968b1 hi1968b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1968 : meanBracketCheck (189/200) lo1968 hi1968=true := by decide +kernel
def bracket1968 : MeanBracket := meanBracketOfMoments (189/200) lo1968 hi1968 accepted1968
def lo1969b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨42,by decide⟩
def lo1969b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨43,by decide⟩
def lo1969 : CheckedMoment :=
  CheckedMoment.ofBessel lo1969b1 lo1969b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1969b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨47,by decide⟩
def hi1969b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨48,by decide⟩
def hi1969 : CheckedMoment :=
  CheckedMoment.ofBessel hi1969b1 hi1969b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1969 : meanBracketCheck (1891/2000) lo1969 hi1969=true := by decide +kernel
def bracket1969 : MeanBracket := meanBracketOfMoments (1891/2000) lo1969 hi1969 accepted1969
def lo1970b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨52,by decide⟩
def lo1970b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨53,by decide⟩
def lo1970 : CheckedMoment :=
  CheckedMoment.ofBessel lo1970b1 lo1970b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1970b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨57,by decide⟩
def hi1970b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨58,by decide⟩
def hi1970 : CheckedMoment :=
  CheckedMoment.ofBessel hi1970b1 hi1970b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1970 : meanBracketCheck (473/500) lo1970 hi1970=true := by decide +kernel
def bracket1970 : MeanBracket := meanBracketOfMoments (473/500) lo1970 hi1970 accepted1970
def lo1971b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨62,by decide⟩
def lo1971b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨63,by decide⟩
def lo1971 : CheckedMoment :=
  CheckedMoment.ofBessel lo1971b1 lo1971b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1971b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨3,by decide⟩
def hi1971b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨4,by decide⟩
def hi1971 : CheckedMoment :=
  CheckedMoment.ofBessel hi1971b1 hi1971b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1971 : meanBracketCheck (1893/2000) lo1971 hi1971=true := by decide +kernel
def bracket1971 : MeanBracket := meanBracketOfMoments (1893/2000) lo1971 hi1971 accepted1971
def lo1972b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨8,by decide⟩
def lo1972b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨9,by decide⟩
def lo1972 : CheckedMoment :=
  CheckedMoment.ofBessel lo1972b1 lo1972b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1972b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨13,by decide⟩
def hi1972b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨14,by decide⟩
def hi1972 : CheckedMoment :=
  CheckedMoment.ofBessel hi1972b1 hi1972b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1972 : meanBracketCheck (947/1000) lo1972 hi1972=true := by decide +kernel
def bracket1972 : MeanBracket := meanBracketOfMoments (947/1000) lo1972 hi1972 accepted1972
def lo1973b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨18,by decide⟩
def lo1973b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨19,by decide⟩
def lo1973 : CheckedMoment :=
  CheckedMoment.ofBessel lo1973b1 lo1973b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1973b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨23,by decide⟩
def hi1973b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨24,by decide⟩
def hi1973 : CheckedMoment :=
  CheckedMoment.ofBessel hi1973b1 hi1973b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1973 : meanBracketCheck (379/400) lo1973 hi1973=true := by decide +kernel
def bracket1973 : MeanBracket := meanBracketOfMoments (379/400) lo1973 hi1973 accepted1973
def lo1974b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨28,by decide⟩
def lo1974b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨29,by decide⟩
def lo1974 : CheckedMoment :=
  CheckedMoment.ofBessel lo1974b1 lo1974b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1974b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨33,by decide⟩
def hi1974b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨34,by decide⟩
def hi1974 : CheckedMoment :=
  CheckedMoment.ofBessel hi1974b1 hi1974b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1974 : meanBracketCheck (237/250) lo1974 hi1974=true := by decide +kernel
def bracket1974 : MeanBracket := meanBracketOfMoments (237/250) lo1974 hi1974 accepted1974
def lo1975b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨38,by decide⟩
def lo1975b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨39,by decide⟩
def lo1975 : CheckedMoment :=
  CheckedMoment.ofBessel lo1975b1 lo1975b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1975b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨43,by decide⟩
def hi1975b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨44,by decide⟩
def hi1975 : CheckedMoment :=
  CheckedMoment.ofBessel hi1975b1 hi1975b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1975 : meanBracketCheck (1897/2000) lo1975 hi1975=true := by decide +kernel
def bracket1975 : MeanBracket := meanBracketOfMoments (1897/2000) lo1975 hi1975 accepted1975
def lo1976b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨48,by decide⟩
def lo1976b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨49,by decide⟩
def lo1976 : CheckedMoment :=
  CheckedMoment.ofBessel lo1976b1 lo1976b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1976b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨53,by decide⟩
def hi1976b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨54,by decide⟩
def hi1976 : CheckedMoment :=
  CheckedMoment.ofBessel hi1976b1 hi1976b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1976 : meanBracketCheck (949/1000) lo1976 hi1976=true := by decide +kernel
def bracket1976 : MeanBracket := meanBracketOfMoments (949/1000) lo1976 hi1976 accepted1976
def lo1977b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨58,by decide⟩
def lo1977b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨59,by decide⟩
def lo1977 : CheckedMoment :=
  CheckedMoment.ofBessel lo1977b1 lo1977b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1977b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨63,by decide⟩
def hi1977b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨0,by decide⟩
def hi1977 : CheckedMoment :=
  CheckedMoment.ofBessel hi1977b1 hi1977b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1977 : meanBracketCheck (1899/2000) lo1977 hi1977=true := by decide +kernel
def bracket1977 : MeanBracket := meanBracketOfMoments (1899/2000) lo1977 hi1977 accepted1977
def lo1978b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨4,by decide⟩
def lo1978b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨5,by decide⟩
def lo1978 : CheckedMoment :=
  CheckedMoment.ofBessel lo1978b1 lo1978b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1978b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨9,by decide⟩
def hi1978b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨10,by decide⟩
def hi1978 : CheckedMoment :=
  CheckedMoment.ofBessel hi1978b1 hi1978b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1978 : meanBracketCheck (19/20) lo1978 hi1978=true := by decide +kernel
def bracket1978 : MeanBracket := meanBracketOfMoments (19/20) lo1978 hi1978 accepted1978
def lo1979b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨14,by decide⟩
def lo1979b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨15,by decide⟩
def lo1979 : CheckedMoment :=
  CheckedMoment.ofBessel lo1979b1 lo1979b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1979b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨19,by decide⟩
def hi1979b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨20,by decide⟩
def hi1979 : CheckedMoment :=
  CheckedMoment.ofBessel hi1979b1 hi1979b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1979 : meanBracketCheck (9501/10000) lo1979 hi1979=true := by decide +kernel
def bracket1979 : MeanBracket := meanBracketOfMoments (9501/10000) lo1979 hi1979 accepted1979
def lo1980b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨24,by decide⟩
def lo1980b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨25,by decide⟩
def lo1980 : CheckedMoment :=
  CheckedMoment.ofBessel lo1980b1 lo1980b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1980b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨29,by decide⟩
def hi1980b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨30,by decide⟩
def hi1980 : CheckedMoment :=
  CheckedMoment.ofBessel hi1980b1 hi1980b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1980 : meanBracketCheck (4751/5000) lo1980 hi1980=true := by decide +kernel
def bracket1980 : MeanBracket := meanBracketOfMoments (4751/5000) lo1980 hi1980 accepted1980
def lo1981b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨34,by decide⟩
def lo1981b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨35,by decide⟩
def lo1981 : CheckedMoment :=
  CheckedMoment.ofBessel lo1981b1 lo1981b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1981b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨39,by decide⟩
def hi1981b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨40,by decide⟩
def hi1981 : CheckedMoment :=
  CheckedMoment.ofBessel hi1981b1 hi1981b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1981 : meanBracketCheck (9503/10000) lo1981 hi1981=true := by decide +kernel
def bracket1981 : MeanBracket := meanBracketOfMoments (9503/10000) lo1981 hi1981 accepted1981
def lo1982b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨44,by decide⟩
def lo1982b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨45,by decide⟩
def lo1982 : CheckedMoment :=
  CheckedMoment.ofBessel lo1982b1 lo1982b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1982b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨49,by decide⟩
def hi1982b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨50,by decide⟩
def hi1982 : CheckedMoment :=
  CheckedMoment.ofBessel hi1982b1 hi1982b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1982 : meanBracketCheck (594/625) lo1982 hi1982=true := by decide +kernel
def bracket1982 : MeanBracket := meanBracketOfMoments (594/625) lo1982 hi1982 accepted1982
def lo1983b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨54,by decide⟩
def lo1983b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨55,by decide⟩
def lo1983 : CheckedMoment :=
  CheckedMoment.ofBessel lo1983b1 lo1983b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1983b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨59,by decide⟩
def hi1983b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0309.rows BesselBatch0309.accepted ⟨60,by decide⟩
def hi1983 : CheckedMoment :=
  CheckedMoment.ofBessel hi1983b1 hi1983b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1983 : meanBracketCheck (1901/2000) lo1983 hi1983=true := by decide +kernel
def bracket1983 : MeanBracket := meanBracketOfMoments (1901/2000) lo1983 hi1983 accepted1983
#print axioms bracket1968
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0123
