module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0305
public import BecknerOnofri.EntropyScalarCertificate.Bessel0306
public import BecknerOnofri.EntropyScalarCertificate.Bessel0307

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0122
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1952b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨0,by decide⟩
def lo1952b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨1,by decide⟩
def lo1952 : CheckedMoment :=
  CheckedMoment.ofBessel lo1952b1 lo1952b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1952b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨5,by decide⟩
def hi1952b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨6,by decide⟩
def hi1952 : CheckedMoment :=
  CheckedMoment.ofBessel hi1952b1 hi1952b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1952 : meanBracketCheck (937/1000) lo1952 hi1952=true := by decide +kernel
def bracket1952 : MeanBracket := meanBracketOfMoments (937/1000) lo1952 hi1952 accepted1952
def lo1953b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨10,by decide⟩
def lo1953b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨11,by decide⟩
def lo1953 : CheckedMoment :=
  CheckedMoment.ofBessel lo1953b1 lo1953b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1953b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨15,by decide⟩
def hi1953b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨16,by decide⟩
def hi1953 : CheckedMoment :=
  CheckedMoment.ofBessel hi1953b1 hi1953b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1953 : meanBracketCheck (15/16) lo1953 hi1953=true := by decide +kernel
def bracket1953 : MeanBracket := meanBracketOfMoments (15/16) lo1953 hi1953 accepted1953
def lo1954b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨20,by decide⟩
def lo1954b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨21,by decide⟩
def lo1954 : CheckedMoment :=
  CheckedMoment.ofBessel lo1954b1 lo1954b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1954b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨25,by decide⟩
def hi1954b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨26,by decide⟩
def hi1954 : CheckedMoment :=
  CheckedMoment.ofBessel hi1954b1 hi1954b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1954 : meanBracketCheck (469/500) lo1954 hi1954=true := by decide +kernel
def bracket1954 : MeanBracket := meanBracketOfMoments (469/500) lo1954 hi1954 accepted1954
def lo1955b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨30,by decide⟩
def lo1955b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨31,by decide⟩
def lo1955 : CheckedMoment :=
  CheckedMoment.ofBessel lo1955b1 lo1955b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1955b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨35,by decide⟩
def hi1955b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨36,by decide⟩
def hi1955 : CheckedMoment :=
  CheckedMoment.ofBessel hi1955b1 hi1955b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1955 : meanBracketCheck (1877/2000) lo1955 hi1955=true := by decide +kernel
def bracket1955 : MeanBracket := meanBracketOfMoments (1877/2000) lo1955 hi1955 accepted1955
def lo1956b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨40,by decide⟩
def lo1956b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨41,by decide⟩
def lo1956 : CheckedMoment :=
  CheckedMoment.ofBessel lo1956b1 lo1956b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1956b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨45,by decide⟩
def hi1956b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨46,by decide⟩
def hi1956 : CheckedMoment :=
  CheckedMoment.ofBessel hi1956b1 hi1956b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1956 : meanBracketCheck (939/1000) lo1956 hi1956=true := by decide +kernel
def bracket1956 : MeanBracket := meanBracketOfMoments (939/1000) lo1956 hi1956 accepted1956
def lo1957b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨50,by decide⟩
def lo1957b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨51,by decide⟩
def lo1957 : CheckedMoment :=
  CheckedMoment.ofBessel lo1957b1 lo1957b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1957b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨55,by decide⟩
def hi1957b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨56,by decide⟩
def hi1957 : CheckedMoment :=
  CheckedMoment.ofBessel hi1957b1 hi1957b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1957 : meanBracketCheck (1879/2000) lo1957 hi1957=true := by decide +kernel
def bracket1957 : MeanBracket := meanBracketOfMoments (1879/2000) lo1957 hi1957 accepted1957
def lo1958b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨60,by decide⟩
def lo1958b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨61,by decide⟩
def lo1958 : CheckedMoment :=
  CheckedMoment.ofBessel lo1958b1 lo1958b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1958b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨1,by decide⟩
def hi1958b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨2,by decide⟩
def hi1958 : CheckedMoment :=
  CheckedMoment.ofBessel hi1958b1 hi1958b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1958 : meanBracketCheck (47/50) lo1958 hi1958=true := by decide +kernel
def bracket1958 : MeanBracket := meanBracketOfMoments (47/50) lo1958 hi1958 accepted1958
def lo1959b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨6,by decide⟩
def lo1959b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨7,by decide⟩
def lo1959 : CheckedMoment :=
  CheckedMoment.ofBessel lo1959b1 lo1959b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1959b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨11,by decide⟩
def hi1959b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨12,by decide⟩
def hi1959 : CheckedMoment :=
  CheckedMoment.ofBessel hi1959b1 hi1959b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1959 : meanBracketCheck (1881/2000) lo1959 hi1959=true := by decide +kernel
def bracket1959 : MeanBracket := meanBracketOfMoments (1881/2000) lo1959 hi1959 accepted1959
def lo1960b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨16,by decide⟩
def lo1960b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨17,by decide⟩
def lo1960 : CheckedMoment :=
  CheckedMoment.ofBessel lo1960b1 lo1960b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1960b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨21,by decide⟩
def hi1960b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨22,by decide⟩
def hi1960 : CheckedMoment :=
  CheckedMoment.ofBessel hi1960b1 hi1960b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1960 : meanBracketCheck (941/1000) lo1960 hi1960=true := by decide +kernel
def bracket1960 : MeanBracket := meanBracketOfMoments (941/1000) lo1960 hi1960 accepted1960
def lo1961b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨26,by decide⟩
def lo1961b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨27,by decide⟩
def lo1961 : CheckedMoment :=
  CheckedMoment.ofBessel lo1961b1 lo1961b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1961b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨31,by decide⟩
def hi1961b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨32,by decide⟩
def hi1961 : CheckedMoment :=
  CheckedMoment.ofBessel hi1961b1 hi1961b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1961 : meanBracketCheck (1883/2000) lo1961 hi1961=true := by decide +kernel
def bracket1961 : MeanBracket := meanBracketOfMoments (1883/2000) lo1961 hi1961 accepted1961
def lo1962b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨36,by decide⟩
def lo1962b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨37,by decide⟩
def lo1962 : CheckedMoment :=
  CheckedMoment.ofBessel lo1962b1 lo1962b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1962b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨41,by decide⟩
def hi1962b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨42,by decide⟩
def hi1962 : CheckedMoment :=
  CheckedMoment.ofBessel hi1962b1 hi1962b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1962 : meanBracketCheck (471/500) lo1962 hi1962=true := by decide +kernel
def bracket1962 : MeanBracket := meanBracketOfMoments (471/500) lo1962 hi1962 accepted1962
def lo1963b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨46,by decide⟩
def lo1963b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨47,by decide⟩
def lo1963 : CheckedMoment :=
  CheckedMoment.ofBessel lo1963b1 lo1963b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1963b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨51,by decide⟩
def hi1963b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨52,by decide⟩
def hi1963 : CheckedMoment :=
  CheckedMoment.ofBessel hi1963b1 hi1963b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1963 : meanBracketCheck (377/400) lo1963 hi1963=true := by decide +kernel
def bracket1963 : MeanBracket := meanBracketOfMoments (377/400) lo1963 hi1963 accepted1963
def lo1964b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨56,by decide⟩
def lo1964b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨57,by decide⟩
def lo1964 : CheckedMoment :=
  CheckedMoment.ofBessel lo1964b1 lo1964b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1964b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨61,by decide⟩
def hi1964b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨62,by decide⟩
def hi1964 : CheckedMoment :=
  CheckedMoment.ofBessel hi1964b1 hi1964b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1964 : meanBracketCheck (943/1000) lo1964 hi1964=true := by decide +kernel
def bracket1964 : MeanBracket := meanBracketOfMoments (943/1000) lo1964 hi1964 accepted1964
def lo1965b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨2,by decide⟩
def lo1965b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨3,by decide⟩
def lo1965 : CheckedMoment :=
  CheckedMoment.ofBessel lo1965b1 lo1965b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1965b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨7,by decide⟩
def hi1965b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨8,by decide⟩
def hi1965 : CheckedMoment :=
  CheckedMoment.ofBessel hi1965b1 hi1965b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1965 : meanBracketCheck (1887/2000) lo1965 hi1965=true := by decide +kernel
def bracket1965 : MeanBracket := meanBracketOfMoments (1887/2000) lo1965 hi1965 accepted1965
def lo1966b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨12,by decide⟩
def lo1966b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨13,by decide⟩
def lo1966 : CheckedMoment :=
  CheckedMoment.ofBessel lo1966b1 lo1966b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1966b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨17,by decide⟩
def hi1966b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨18,by decide⟩
def hi1966 : CheckedMoment :=
  CheckedMoment.ofBessel hi1966b1 hi1966b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1966 : meanBracketCheck (118/125) lo1966 hi1966=true := by decide +kernel
def bracket1966 : MeanBracket := meanBracketOfMoments (118/125) lo1966 hi1966 accepted1966
def lo1967b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨22,by decide⟩
def lo1967b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨23,by decide⟩
def lo1967 : CheckedMoment :=
  CheckedMoment.ofBessel lo1967b1 lo1967b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1967b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨27,by decide⟩
def hi1967b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨28,by decide⟩
def hi1967 : CheckedMoment :=
  CheckedMoment.ofBessel hi1967b1 hi1967b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1967 : meanBracketCheck (1889/2000) lo1967 hi1967=true := by decide +kernel
def bracket1967 : MeanBracket := meanBracketOfMoments (1889/2000) lo1967 hi1967 accepted1967
#print axioms bracket1952
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0122
