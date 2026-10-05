module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0320
public import BecknerOnofri.EntropyScalarCertificate.Bessel0321
public import BecknerOnofri.EntropyScalarCertificate.Bessel0322

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0128
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2048b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨0,by decide⟩
def lo2048b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨1,by decide⟩
def lo2048 : CheckedMoment :=
  CheckedMoment.ofBessel lo2048b1 lo2048b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2048b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨5,by decide⟩
def hi2048b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨6,by decide⟩
def hi2048 : CheckedMoment :=
  CheckedMoment.ofBessel hi2048b1 hi2048b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2048 : meanBracketCheck (957/1000) lo2048 hi2048=true := by decide +kernel
def bracket2048 : MeanBracket := meanBracketOfMoments (957/1000) lo2048 hi2048 accepted2048
def lo2049b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨10,by decide⟩
def lo2049b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨11,by decide⟩
def lo2049 : CheckedMoment :=
  CheckedMoment.ofBessel lo2049b1 lo2049b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2049b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨15,by decide⟩
def hi2049b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨16,by decide⟩
def hi2049 : CheckedMoment :=
  CheckedMoment.ofBessel hi2049b1 hi2049b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2049 : meanBracketCheck (9571/10000) lo2049 hi2049=true := by decide +kernel
def bracket2049 : MeanBracket := meanBracketOfMoments (9571/10000) lo2049 hi2049 accepted2049
def lo2050b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨20,by decide⟩
def lo2050b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨21,by decide⟩
def lo2050 : CheckedMoment :=
  CheckedMoment.ofBessel lo2050b1 lo2050b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2050b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨25,by decide⟩
def hi2050b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨26,by decide⟩
def hi2050 : CheckedMoment :=
  CheckedMoment.ofBessel hi2050b1 hi2050b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2050 : meanBracketCheck (2393/2500) lo2050 hi2050=true := by decide +kernel
def bracket2050 : MeanBracket := meanBracketOfMoments (2393/2500) lo2050 hi2050 accepted2050
def lo2051b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨30,by decide⟩
def lo2051b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨31,by decide⟩
def lo2051 : CheckedMoment :=
  CheckedMoment.ofBessel lo2051b1 lo2051b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2051b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨35,by decide⟩
def hi2051b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨36,by decide⟩
def hi2051 : CheckedMoment :=
  CheckedMoment.ofBessel hi2051b1 hi2051b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2051 : meanBracketCheck (9573/10000) lo2051 hi2051=true := by decide +kernel
def bracket2051 : MeanBracket := meanBracketOfMoments (9573/10000) lo2051 hi2051 accepted2051
def lo2052b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨40,by decide⟩
def lo2052b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨41,by decide⟩
def lo2052 : CheckedMoment :=
  CheckedMoment.ofBessel lo2052b1 lo2052b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2052b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨45,by decide⟩
def hi2052b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨46,by decide⟩
def hi2052 : CheckedMoment :=
  CheckedMoment.ofBessel hi2052b1 hi2052b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2052 : meanBracketCheck (4787/5000) lo2052 hi2052=true := by decide +kernel
def bracket2052 : MeanBracket := meanBracketOfMoments (4787/5000) lo2052 hi2052 accepted2052
def lo2053b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨50,by decide⟩
def lo2053b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨51,by decide⟩
def lo2053 : CheckedMoment :=
  CheckedMoment.ofBessel lo2053b1 lo2053b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2053b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨55,by decide⟩
def hi2053b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨56,by decide⟩
def hi2053 : CheckedMoment :=
  CheckedMoment.ofBessel hi2053b1 hi2053b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2053 : meanBracketCheck (383/400) lo2053 hi2053=true := by decide +kernel
def bracket2053 : MeanBracket := meanBracketOfMoments (383/400) lo2053 hi2053 accepted2053
def lo2054b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨60,by decide⟩
def lo2054b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨61,by decide⟩
def lo2054 : CheckedMoment :=
  CheckedMoment.ofBessel lo2054b1 lo2054b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2054b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨1,by decide⟩
def hi2054b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨2,by decide⟩
def hi2054 : CheckedMoment :=
  CheckedMoment.ofBessel hi2054b1 hi2054b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2054 : meanBracketCheck (1197/1250) lo2054 hi2054=true := by decide +kernel
def bracket2054 : MeanBracket := meanBracketOfMoments (1197/1250) lo2054 hi2054 accepted2054
def lo2055b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨6,by decide⟩
def lo2055b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨7,by decide⟩
def lo2055 : CheckedMoment :=
  CheckedMoment.ofBessel lo2055b1 lo2055b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2055b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨11,by decide⟩
def hi2055b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨12,by decide⟩
def hi2055 : CheckedMoment :=
  CheckedMoment.ofBessel hi2055b1 hi2055b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2055 : meanBracketCheck (9577/10000) lo2055 hi2055=true := by decide +kernel
def bracket2055 : MeanBracket := meanBracketOfMoments (9577/10000) lo2055 hi2055 accepted2055
def lo2056b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨16,by decide⟩
def lo2056b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨17,by decide⟩
def lo2056 : CheckedMoment :=
  CheckedMoment.ofBessel lo2056b1 lo2056b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2056b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨21,by decide⟩
def hi2056b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨22,by decide⟩
def hi2056 : CheckedMoment :=
  CheckedMoment.ofBessel hi2056b1 hi2056b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2056 : meanBracketCheck (4789/5000) lo2056 hi2056=true := by decide +kernel
def bracket2056 : MeanBracket := meanBracketOfMoments (4789/5000) lo2056 hi2056 accepted2056
def lo2057b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨26,by decide⟩
def lo2057b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨27,by decide⟩
def lo2057 : CheckedMoment :=
  CheckedMoment.ofBessel lo2057b1 lo2057b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2057b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨31,by decide⟩
def hi2057b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨32,by decide⟩
def hi2057 : CheckedMoment :=
  CheckedMoment.ofBessel hi2057b1 hi2057b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2057 : meanBracketCheck (9579/10000) lo2057 hi2057=true := by decide +kernel
def bracket2057 : MeanBracket := meanBracketOfMoments (9579/10000) lo2057 hi2057 accepted2057
def lo2058b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨36,by decide⟩
def lo2058b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨37,by decide⟩
def lo2058 : CheckedMoment :=
  CheckedMoment.ofBessel lo2058b1 lo2058b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2058b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨41,by decide⟩
def hi2058b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨42,by decide⟩
def hi2058 : CheckedMoment :=
  CheckedMoment.ofBessel hi2058b1 hi2058b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2058 : meanBracketCheck (479/500) lo2058 hi2058=true := by decide +kernel
def bracket2058 : MeanBracket := meanBracketOfMoments (479/500) lo2058 hi2058 accepted2058
def lo2059b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨46,by decide⟩
def lo2059b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨47,by decide⟩
def lo2059 : CheckedMoment :=
  CheckedMoment.ofBessel lo2059b1 lo2059b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2059b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨51,by decide⟩
def hi2059b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨52,by decide⟩
def hi2059 : CheckedMoment :=
  CheckedMoment.ofBessel hi2059b1 hi2059b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2059 : meanBracketCheck (9581/10000) lo2059 hi2059=true := by decide +kernel
def bracket2059 : MeanBracket := meanBracketOfMoments (9581/10000) lo2059 hi2059 accepted2059
def lo2060b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨56,by decide⟩
def lo2060b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨57,by decide⟩
def lo2060 : CheckedMoment :=
  CheckedMoment.ofBessel lo2060b1 lo2060b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2060b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨61,by decide⟩
def hi2060b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨62,by decide⟩
def hi2060 : CheckedMoment :=
  CheckedMoment.ofBessel hi2060b1 hi2060b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2060 : meanBracketCheck (4791/5000) lo2060 hi2060=true := by decide +kernel
def bracket2060 : MeanBracket := meanBracketOfMoments (4791/5000) lo2060 hi2060 accepted2060
def lo2061b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨2,by decide⟩
def lo2061b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨3,by decide⟩
def lo2061 : CheckedMoment :=
  CheckedMoment.ofBessel lo2061b1 lo2061b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2061b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨7,by decide⟩
def hi2061b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨8,by decide⟩
def hi2061 : CheckedMoment :=
  CheckedMoment.ofBessel hi2061b1 hi2061b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2061 : meanBracketCheck (9583/10000) lo2061 hi2061=true := by decide +kernel
def bracket2061 : MeanBracket := meanBracketOfMoments (9583/10000) lo2061 hi2061 accepted2061
def lo2062b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨12,by decide⟩
def lo2062b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨13,by decide⟩
def lo2062 : CheckedMoment :=
  CheckedMoment.ofBessel lo2062b1 lo2062b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2062b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨17,by decide⟩
def hi2062b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨18,by decide⟩
def hi2062 : CheckedMoment :=
  CheckedMoment.ofBessel hi2062b1 hi2062b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2062 : meanBracketCheck (599/625) lo2062 hi2062=true := by decide +kernel
def bracket2062 : MeanBracket := meanBracketOfMoments (599/625) lo2062 hi2062 accepted2062
def lo2063b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨22,by decide⟩
def lo2063b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨23,by decide⟩
def lo2063 : CheckedMoment :=
  CheckedMoment.ofBessel lo2063b1 lo2063b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2063b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨27,by decide⟩
def hi2063b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨28,by decide⟩
def hi2063 : CheckedMoment :=
  CheckedMoment.ofBessel hi2063b1 hi2063b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2063 : meanBracketCheck (1917/2000) lo2063 hi2063=true := by decide +kernel
def bracket2063 : MeanBracket := meanBracketOfMoments (1917/2000) lo2063 hi2063 accepted2063
#print axioms bracket2048
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0128
