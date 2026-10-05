module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0322
public import BecknerOnofri.EntropyScalarCertificate.Bessel0323
public import BecknerOnofri.EntropyScalarCertificate.Bessel0324

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0129
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2064b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨32,by decide⟩
def lo2064b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨33,by decide⟩
def lo2064 : CheckedMoment :=
  CheckedMoment.ofBessel lo2064b1 lo2064b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2064b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨37,by decide⟩
def hi2064b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨38,by decide⟩
def hi2064 : CheckedMoment :=
  CheckedMoment.ofBessel hi2064b1 hi2064b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2064 : meanBracketCheck (4793/5000) lo2064 hi2064=true := by decide +kernel
def bracket2064 : MeanBracket := meanBracketOfMoments (4793/5000) lo2064 hi2064 accepted2064
def lo2065b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨42,by decide⟩
def lo2065b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨43,by decide⟩
def lo2065 : CheckedMoment :=
  CheckedMoment.ofBessel lo2065b1 lo2065b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2065b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨47,by decide⟩
def hi2065b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨48,by decide⟩
def hi2065 : CheckedMoment :=
  CheckedMoment.ofBessel hi2065b1 hi2065b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2065 : meanBracketCheck (9587/10000) lo2065 hi2065=true := by decide +kernel
def bracket2065 : MeanBracket := meanBracketOfMoments (9587/10000) lo2065 hi2065 accepted2065
def lo2066b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨52,by decide⟩
def lo2066b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨53,by decide⟩
def lo2066 : CheckedMoment :=
  CheckedMoment.ofBessel lo2066b1 lo2066b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2066b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨57,by decide⟩
def hi2066b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨58,by decide⟩
def hi2066 : CheckedMoment :=
  CheckedMoment.ofBessel hi2066b1 hi2066b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2066 : meanBracketCheck (2397/2500) lo2066 hi2066=true := by decide +kernel
def bracket2066 : MeanBracket := meanBracketOfMoments (2397/2500) lo2066 hi2066 accepted2066
def lo2067b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨62,by decide⟩
def lo2067b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0322.rows BesselBatch0322.accepted ⟨63,by decide⟩
def lo2067 : CheckedMoment :=
  CheckedMoment.ofBessel lo2067b1 lo2067b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2067b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨3,by decide⟩
def hi2067b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨4,by decide⟩
def hi2067 : CheckedMoment :=
  CheckedMoment.ofBessel hi2067b1 hi2067b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2067 : meanBracketCheck (9589/10000) lo2067 hi2067=true := by decide +kernel
def bracket2067 : MeanBracket := meanBracketOfMoments (9589/10000) lo2067 hi2067 accepted2067
def lo2068b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨8,by decide⟩
def lo2068b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨9,by decide⟩
def lo2068 : CheckedMoment :=
  CheckedMoment.ofBessel lo2068b1 lo2068b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2068b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨13,by decide⟩
def hi2068b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨14,by decide⟩
def hi2068 : CheckedMoment :=
  CheckedMoment.ofBessel hi2068b1 hi2068b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2068 : meanBracketCheck (959/1000) lo2068 hi2068=true := by decide +kernel
def bracket2068 : MeanBracket := meanBracketOfMoments (959/1000) lo2068 hi2068 accepted2068
def lo2069b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨18,by decide⟩
def lo2069b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨19,by decide⟩
def lo2069 : CheckedMoment :=
  CheckedMoment.ofBessel lo2069b1 lo2069b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2069b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨23,by decide⟩
def hi2069b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨24,by decide⟩
def hi2069 : CheckedMoment :=
  CheckedMoment.ofBessel hi2069b1 hi2069b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2069 : meanBracketCheck (9591/10000) lo2069 hi2069=true := by decide +kernel
def bracket2069 : MeanBracket := meanBracketOfMoments (9591/10000) lo2069 hi2069 accepted2069
def lo2070b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨28,by decide⟩
def lo2070b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨29,by decide⟩
def lo2070 : CheckedMoment :=
  CheckedMoment.ofBessel lo2070b1 lo2070b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2070b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨33,by decide⟩
def hi2070b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨34,by decide⟩
def hi2070 : CheckedMoment :=
  CheckedMoment.ofBessel hi2070b1 hi2070b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2070 : meanBracketCheck (1199/1250) lo2070 hi2070=true := by decide +kernel
def bracket2070 : MeanBracket := meanBracketOfMoments (1199/1250) lo2070 hi2070 accepted2070
def lo2071b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨38,by decide⟩
def lo2071b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨39,by decide⟩
def lo2071 : CheckedMoment :=
  CheckedMoment.ofBessel lo2071b1 lo2071b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2071b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨43,by decide⟩
def hi2071b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨44,by decide⟩
def hi2071 : CheckedMoment :=
  CheckedMoment.ofBessel hi2071b1 hi2071b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2071 : meanBracketCheck (9593/10000) lo2071 hi2071=true := by decide +kernel
def bracket2071 : MeanBracket := meanBracketOfMoments (9593/10000) lo2071 hi2071 accepted2071
def lo2072b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨48,by decide⟩
def lo2072b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨49,by decide⟩
def lo2072 : CheckedMoment :=
  CheckedMoment.ofBessel lo2072b1 lo2072b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2072b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨53,by decide⟩
def hi2072b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨54,by decide⟩
def hi2072 : CheckedMoment :=
  CheckedMoment.ofBessel hi2072b1 hi2072b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2072 : meanBracketCheck (4797/5000) lo2072 hi2072=true := by decide +kernel
def bracket2072 : MeanBracket := meanBracketOfMoments (4797/5000) lo2072 hi2072 accepted2072
def lo2073b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨58,by decide⟩
def lo2073b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨59,by decide⟩
def lo2073 : CheckedMoment :=
  CheckedMoment.ofBessel lo2073b1 lo2073b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2073b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨63,by decide⟩
def hi2073b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨0,by decide⟩
def hi2073 : CheckedMoment :=
  CheckedMoment.ofBessel hi2073b1 hi2073b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2073 : meanBracketCheck (1919/2000) lo2073 hi2073=true := by decide +kernel
def bracket2073 : MeanBracket := meanBracketOfMoments (1919/2000) lo2073 hi2073 accepted2073
def lo2074b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨4,by decide⟩
def lo2074b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨5,by decide⟩
def lo2074 : CheckedMoment :=
  CheckedMoment.ofBessel lo2074b1 lo2074b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2074b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨9,by decide⟩
def hi2074b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨10,by decide⟩
def hi2074 : CheckedMoment :=
  CheckedMoment.ofBessel hi2074b1 hi2074b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2074 : meanBracketCheck (2399/2500) lo2074 hi2074=true := by decide +kernel
def bracket2074 : MeanBracket := meanBracketOfMoments (2399/2500) lo2074 hi2074 accepted2074
def lo2075b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨14,by decide⟩
def lo2075b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨15,by decide⟩
def lo2075 : CheckedMoment :=
  CheckedMoment.ofBessel lo2075b1 lo2075b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2075b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨19,by decide⟩
def hi2075b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨20,by decide⟩
def hi2075 : CheckedMoment :=
  CheckedMoment.ofBessel hi2075b1 hi2075b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2075 : meanBracketCheck (9597/10000) lo2075 hi2075=true := by decide +kernel
def bracket2075 : MeanBracket := meanBracketOfMoments (9597/10000) lo2075 hi2075 accepted2075
def lo2076b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨24,by decide⟩
def lo2076b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨25,by decide⟩
def lo2076 : CheckedMoment :=
  CheckedMoment.ofBessel lo2076b1 lo2076b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2076b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨29,by decide⟩
def hi2076b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨30,by decide⟩
def hi2076 : CheckedMoment :=
  CheckedMoment.ofBessel hi2076b1 hi2076b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2076 : meanBracketCheck (4799/5000) lo2076 hi2076=true := by decide +kernel
def bracket2076 : MeanBracket := meanBracketOfMoments (4799/5000) lo2076 hi2076 accepted2076
def lo2077b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨34,by decide⟩
def lo2077b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨35,by decide⟩
def lo2077 : CheckedMoment :=
  CheckedMoment.ofBessel lo2077b1 lo2077b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2077b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨39,by decide⟩
def hi2077b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨40,by decide⟩
def hi2077 : CheckedMoment :=
  CheckedMoment.ofBessel hi2077b1 hi2077b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2077 : meanBracketCheck (9599/10000) lo2077 hi2077=true := by decide +kernel
def bracket2077 : MeanBracket := meanBracketOfMoments (9599/10000) lo2077 hi2077 accepted2077
def lo2078b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨44,by decide⟩
def lo2078b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨45,by decide⟩
def lo2078 : CheckedMoment :=
  CheckedMoment.ofBessel lo2078b1 lo2078b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2078b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨49,by decide⟩
def hi2078b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨50,by decide⟩
def hi2078 : CheckedMoment :=
  CheckedMoment.ofBessel hi2078b1 hi2078b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2078 : meanBracketCheck (24/25) lo2078 hi2078=true := by decide +kernel
def bracket2078 : MeanBracket := meanBracketOfMoments (24/25) lo2078 hi2078 accepted2078
def lo2079b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨54,by decide⟩
def lo2079b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨55,by decide⟩
def lo2079 : CheckedMoment :=
  CheckedMoment.ofBessel lo2079b1 lo2079b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2079b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨59,by decide⟩
def hi2079b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨60,by decide⟩
def hi2079 : CheckedMoment :=
  CheckedMoment.ofBessel hi2079b1 hi2079b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2079 : meanBracketCheck (9601/10000) lo2079 hi2079=true := by decide +kernel
def bracket2079 : MeanBracket := meanBracketOfMoments (9601/10000) lo2079 hi2079 accepted2079
#print axioms bracket2064
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0129
