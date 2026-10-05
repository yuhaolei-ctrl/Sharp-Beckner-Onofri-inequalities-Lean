module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0302
public import BecknerOnofri.EntropyScalarCertificate.Bessel0303
public import BecknerOnofri.EntropyScalarCertificate.Bessel0304

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0121
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1936b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨32,by decide⟩
def lo1936b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨33,by decide⟩
def lo1936 : CheckedMoment :=
  CheckedMoment.ofBessel lo1936b1 lo1936b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1936b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨37,by decide⟩
def hi1936b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨38,by decide⟩
def hi1936 : CheckedMoment :=
  CheckedMoment.ofBessel hi1936b1 hi1936b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1936 : meanBracketCheck (929/1000) lo1936 hi1936=true := by decide +kernel
def bracket1936 : MeanBracket := meanBracketOfMoments (929/1000) lo1936 hi1936 accepted1936
def lo1937b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨42,by decide⟩
def lo1937b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨43,by decide⟩
def lo1937 : CheckedMoment :=
  CheckedMoment.ofBessel lo1937b1 lo1937b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1937b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨47,by decide⟩
def hi1937b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨48,by decide⟩
def hi1937 : CheckedMoment :=
  CheckedMoment.ofBessel hi1937b1 hi1937b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1937 : meanBracketCheck (1859/2000) lo1937 hi1937=true := by decide +kernel
def bracket1937 : MeanBracket := meanBracketOfMoments (1859/2000) lo1937 hi1937 accepted1937
def lo1938b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨52,by decide⟩
def lo1938b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨53,by decide⟩
def lo1938 : CheckedMoment :=
  CheckedMoment.ofBessel lo1938b1 lo1938b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1938b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨57,by decide⟩
def hi1938b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨58,by decide⟩
def hi1938 : CheckedMoment :=
  CheckedMoment.ofBessel hi1938b1 hi1938b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1938 : meanBracketCheck (93/100) lo1938 hi1938=true := by decide +kernel
def bracket1938 : MeanBracket := meanBracketOfMoments (93/100) lo1938 hi1938 accepted1938
def lo1939b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨62,by decide⟩
def lo1939b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0302.rows BesselBatch0302.accepted ⟨63,by decide⟩
def lo1939 : CheckedMoment :=
  CheckedMoment.ofBessel lo1939b1 lo1939b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1939b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨3,by decide⟩
def hi1939b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨4,by decide⟩
def hi1939 : CheckedMoment :=
  CheckedMoment.ofBessel hi1939b1 hi1939b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1939 : meanBracketCheck (1861/2000) lo1939 hi1939=true := by decide +kernel
def bracket1939 : MeanBracket := meanBracketOfMoments (1861/2000) lo1939 hi1939 accepted1939
def lo1940b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨8,by decide⟩
def lo1940b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨9,by decide⟩
def lo1940 : CheckedMoment :=
  CheckedMoment.ofBessel lo1940b1 lo1940b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1940b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨13,by decide⟩
def hi1940b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨14,by decide⟩
def hi1940 : CheckedMoment :=
  CheckedMoment.ofBessel hi1940b1 hi1940b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1940 : meanBracketCheck (931/1000) lo1940 hi1940=true := by decide +kernel
def bracket1940 : MeanBracket := meanBracketOfMoments (931/1000) lo1940 hi1940 accepted1940
def lo1941b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨18,by decide⟩
def lo1941b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨19,by decide⟩
def lo1941 : CheckedMoment :=
  CheckedMoment.ofBessel lo1941b1 lo1941b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1941b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨23,by decide⟩
def hi1941b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨24,by decide⟩
def hi1941 : CheckedMoment :=
  CheckedMoment.ofBessel hi1941b1 hi1941b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1941 : meanBracketCheck (1863/2000) lo1941 hi1941=true := by decide +kernel
def bracket1941 : MeanBracket := meanBracketOfMoments (1863/2000) lo1941 hi1941 accepted1941
def lo1942b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨28,by decide⟩
def lo1942b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨29,by decide⟩
def lo1942 : CheckedMoment :=
  CheckedMoment.ofBessel lo1942b1 lo1942b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1942b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨33,by decide⟩
def hi1942b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨34,by decide⟩
def hi1942 : CheckedMoment :=
  CheckedMoment.ofBessel hi1942b1 hi1942b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1942 : meanBracketCheck (233/250) lo1942 hi1942=true := by decide +kernel
def bracket1942 : MeanBracket := meanBracketOfMoments (233/250) lo1942 hi1942 accepted1942
def lo1943b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨38,by decide⟩
def lo1943b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨39,by decide⟩
def lo1943 : CheckedMoment :=
  CheckedMoment.ofBessel lo1943b1 lo1943b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1943b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨43,by decide⟩
def hi1943b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨44,by decide⟩
def hi1943 : CheckedMoment :=
  CheckedMoment.ofBessel hi1943b1 hi1943b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1943 : meanBracketCheck (373/400) lo1943 hi1943=true := by decide +kernel
def bracket1943 : MeanBracket := meanBracketOfMoments (373/400) lo1943 hi1943 accepted1943
def lo1944b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨48,by decide⟩
def lo1944b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨49,by decide⟩
def lo1944 : CheckedMoment :=
  CheckedMoment.ofBessel lo1944b1 lo1944b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1944b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨53,by decide⟩
def hi1944b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨54,by decide⟩
def hi1944 : CheckedMoment :=
  CheckedMoment.ofBessel hi1944b1 hi1944b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1944 : meanBracketCheck (933/1000) lo1944 hi1944=true := by decide +kernel
def bracket1944 : MeanBracket := meanBracketOfMoments (933/1000) lo1944 hi1944 accepted1944
def lo1945b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨58,by decide⟩
def lo1945b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨59,by decide⟩
def lo1945 : CheckedMoment :=
  CheckedMoment.ofBessel lo1945b1 lo1945b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1945b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨63,by decide⟩
def hi1945b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨0,by decide⟩
def hi1945 : CheckedMoment :=
  CheckedMoment.ofBessel hi1945b1 hi1945b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1945 : meanBracketCheck (1867/2000) lo1945 hi1945=true := by decide +kernel
def bracket1945 : MeanBracket := meanBracketOfMoments (1867/2000) lo1945 hi1945 accepted1945
def lo1946b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨4,by decide⟩
def lo1946b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨5,by decide⟩
def lo1946 : CheckedMoment :=
  CheckedMoment.ofBessel lo1946b1 lo1946b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1946b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨9,by decide⟩
def hi1946b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨10,by decide⟩
def hi1946 : CheckedMoment :=
  CheckedMoment.ofBessel hi1946b1 hi1946b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1946 : meanBracketCheck (467/500) lo1946 hi1946=true := by decide +kernel
def bracket1946 : MeanBracket := meanBracketOfMoments (467/500) lo1946 hi1946 accepted1946
def lo1947b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨14,by decide⟩
def lo1947b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨15,by decide⟩
def lo1947 : CheckedMoment :=
  CheckedMoment.ofBessel lo1947b1 lo1947b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1947b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨19,by decide⟩
def hi1947b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨20,by decide⟩
def hi1947 : CheckedMoment :=
  CheckedMoment.ofBessel hi1947b1 hi1947b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1947 : meanBracketCheck (1869/2000) lo1947 hi1947=true := by decide +kernel
def bracket1947 : MeanBracket := meanBracketOfMoments (1869/2000) lo1947 hi1947 accepted1947
def lo1948b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨24,by decide⟩
def lo1948b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨25,by decide⟩
def lo1948 : CheckedMoment :=
  CheckedMoment.ofBessel lo1948b1 lo1948b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1948b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨29,by decide⟩
def hi1948b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨30,by decide⟩
def hi1948 : CheckedMoment :=
  CheckedMoment.ofBessel hi1948b1 hi1948b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1948 : meanBracketCheck (187/200) lo1948 hi1948=true := by decide +kernel
def bracket1948 : MeanBracket := meanBracketOfMoments (187/200) lo1948 hi1948 accepted1948
def lo1949b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨34,by decide⟩
def lo1949b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨35,by decide⟩
def lo1949 : CheckedMoment :=
  CheckedMoment.ofBessel lo1949b1 lo1949b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1949b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨39,by decide⟩
def hi1949b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨40,by decide⟩
def hi1949 : CheckedMoment :=
  CheckedMoment.ofBessel hi1949b1 hi1949b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1949 : meanBracketCheck (1871/2000) lo1949 hi1949=true := by decide +kernel
def bracket1949 : MeanBracket := meanBracketOfMoments (1871/2000) lo1949 hi1949 accepted1949
def lo1950b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨44,by decide⟩
def lo1950b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨45,by decide⟩
def lo1950 : CheckedMoment :=
  CheckedMoment.ofBessel lo1950b1 lo1950b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1950b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨49,by decide⟩
def hi1950b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨50,by decide⟩
def hi1950 : CheckedMoment :=
  CheckedMoment.ofBessel hi1950b1 hi1950b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1950 : meanBracketCheck (117/125) lo1950 hi1950=true := by decide +kernel
def bracket1950 : MeanBracket := meanBracketOfMoments (117/125) lo1950 hi1950 accepted1950
def lo1951b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨54,by decide⟩
def lo1951b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨55,by decide⟩
def lo1951 : CheckedMoment :=
  CheckedMoment.ofBessel lo1951b1 lo1951b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1951b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨59,by decide⟩
def hi1951b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨60,by decide⟩
def hi1951 : CheckedMoment :=
  CheckedMoment.ofBessel hi1951b1 hi1951b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1951 : meanBracketCheck (1873/2000) lo1951 hi1951=true := by decide +kernel
def bracket1951 : MeanBracket := meanBracketOfMoments (1873/2000) lo1951 hi1951 accepted1951
#print axioms bracket1936
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0121
