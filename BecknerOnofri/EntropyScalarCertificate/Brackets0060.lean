module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0150
public import BecknerOnofri.EntropyScalarCertificate.Bessel0151
public import BecknerOnofri.EntropyScalarCertificate.Bessel0152

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0060
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0960b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨0,by decide⟩
def lo0960b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨1,by decide⟩
def lo0960 : CheckedMoment :=
  CheckedMoment.ofBessel lo0960b1 lo0960b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0960b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨5,by decide⟩
def hi0960b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨6,by decide⟩
def hi0960 : CheckedMoment :=
  CheckedMoment.ofBessel hi0960b1 hi0960b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0960 : meanBracketCheck (221/500) lo0960 hi0960=true := by decide +kernel
def bracket0960 : MeanBracket := meanBracketOfMoments (221/500) lo0960 hi0960 accepted0960
def lo0961b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨10,by decide⟩
def lo0961b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨11,by decide⟩
def lo0961 : CheckedMoment :=
  CheckedMoment.ofBessel lo0961b1 lo0961b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0961b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨15,by decide⟩
def hi0961b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨16,by decide⟩
def hi0961 : CheckedMoment :=
  CheckedMoment.ofBessel hi0961b1 hi0961b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0961 : meanBracketCheck (443/1000) lo0961 hi0961=true := by decide +kernel
def bracket0961 : MeanBracket := meanBracketOfMoments (443/1000) lo0961 hi0961 accepted0961
def lo0962b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨20,by decide⟩
def lo0962b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨21,by decide⟩
def lo0962 : CheckedMoment :=
  CheckedMoment.ofBessel lo0962b1 lo0962b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0962b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨25,by decide⟩
def hi0962b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨26,by decide⟩
def hi0962 : CheckedMoment :=
  CheckedMoment.ofBessel hi0962b1 hi0962b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0962 : meanBracketCheck (111/250) lo0962 hi0962=true := by decide +kernel
def bracket0962 : MeanBracket := meanBracketOfMoments (111/250) lo0962 hi0962 accepted0962
def lo0963b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨30,by decide⟩
def lo0963b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨31,by decide⟩
def lo0963 : CheckedMoment :=
  CheckedMoment.ofBessel lo0963b1 lo0963b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0963b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨35,by decide⟩
def hi0963b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨36,by decide⟩
def hi0963 : CheckedMoment :=
  CheckedMoment.ofBessel hi0963b1 hi0963b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0963 : meanBracketCheck (89/200) lo0963 hi0963=true := by decide +kernel
def bracket0963 : MeanBracket := meanBracketOfMoments (89/200) lo0963 hi0963 accepted0963
def lo0964b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨40,by decide⟩
def lo0964b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨41,by decide⟩
def lo0964 : CheckedMoment :=
  CheckedMoment.ofBessel lo0964b1 lo0964b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0964b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨45,by decide⟩
def hi0964b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨46,by decide⟩
def hi0964 : CheckedMoment :=
  CheckedMoment.ofBessel hi0964b1 hi0964b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0964 : meanBracketCheck (223/500) lo0964 hi0964=true := by decide +kernel
def bracket0964 : MeanBracket := meanBracketOfMoments (223/500) lo0964 hi0964 accepted0964
def lo0965b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨50,by decide⟩
def lo0965b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨51,by decide⟩
def lo0965 : CheckedMoment :=
  CheckedMoment.ofBessel lo0965b1 lo0965b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0965b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨55,by decide⟩
def hi0965b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨56,by decide⟩
def hi0965 : CheckedMoment :=
  CheckedMoment.ofBessel hi0965b1 hi0965b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0965 : meanBracketCheck (447/1000) lo0965 hi0965=true := by decide +kernel
def bracket0965 : MeanBracket := meanBracketOfMoments (447/1000) lo0965 hi0965 accepted0965
def lo0966b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨60,by decide⟩
def lo0966b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0150.rows BesselBatch0150.accepted ⟨61,by decide⟩
def lo0966 : CheckedMoment :=
  CheckedMoment.ofBessel lo0966b1 lo0966b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0966b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨1,by decide⟩
def hi0966b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨2,by decide⟩
def hi0966 : CheckedMoment :=
  CheckedMoment.ofBessel hi0966b1 hi0966b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0966 : meanBracketCheck (56/125) lo0966 hi0966=true := by decide +kernel
def bracket0966 : MeanBracket := meanBracketOfMoments (56/125) lo0966 hi0966 accepted0966
def lo0967b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨6,by decide⟩
def lo0967b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨7,by decide⟩
def lo0967 : CheckedMoment :=
  CheckedMoment.ofBessel lo0967b1 lo0967b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0967b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨11,by decide⟩
def hi0967b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨12,by decide⟩
def hi0967 : CheckedMoment :=
  CheckedMoment.ofBessel hi0967b1 hi0967b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0967 : meanBracketCheck (449/1000) lo0967 hi0967=true := by decide +kernel
def bracket0967 : MeanBracket := meanBracketOfMoments (449/1000) lo0967 hi0967 accepted0967
def lo0968b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨16,by decide⟩
def lo0968b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨17,by decide⟩
def lo0968 : CheckedMoment :=
  CheckedMoment.ofBessel lo0968b1 lo0968b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0968b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨21,by decide⟩
def hi0968b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨22,by decide⟩
def hi0968 : CheckedMoment :=
  CheckedMoment.ofBessel hi0968b1 hi0968b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0968 : meanBracketCheck (9/20) lo0968 hi0968=true := by decide +kernel
def bracket0968 : MeanBracket := meanBracketOfMoments (9/20) lo0968 hi0968 accepted0968
def lo0969b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨26,by decide⟩
def lo0969b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨27,by decide⟩
def lo0969 : CheckedMoment :=
  CheckedMoment.ofBessel lo0969b1 lo0969b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0969b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨31,by decide⟩
def hi0969b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨32,by decide⟩
def hi0969 : CheckedMoment :=
  CheckedMoment.ofBessel hi0969b1 hi0969b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0969 : meanBracketCheck (451/1000) lo0969 hi0969=true := by decide +kernel
def bracket0969 : MeanBracket := meanBracketOfMoments (451/1000) lo0969 hi0969 accepted0969
def lo0970b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨36,by decide⟩
def lo0970b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨37,by decide⟩
def lo0970 : CheckedMoment :=
  CheckedMoment.ofBessel lo0970b1 lo0970b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0970b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨41,by decide⟩
def hi0970b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨42,by decide⟩
def hi0970 : CheckedMoment :=
  CheckedMoment.ofBessel hi0970b1 hi0970b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0970 : meanBracketCheck (113/250) lo0970 hi0970=true := by decide +kernel
def bracket0970 : MeanBracket := meanBracketOfMoments (113/250) lo0970 hi0970 accepted0970
def lo0971b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨46,by decide⟩
def lo0971b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨47,by decide⟩
def lo0971 : CheckedMoment :=
  CheckedMoment.ofBessel lo0971b1 lo0971b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0971b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨51,by decide⟩
def hi0971b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨52,by decide⟩
def hi0971 : CheckedMoment :=
  CheckedMoment.ofBessel hi0971b1 hi0971b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0971 : meanBracketCheck (453/1000) lo0971 hi0971=true := by decide +kernel
def bracket0971 : MeanBracket := meanBracketOfMoments (453/1000) lo0971 hi0971 accepted0971
def lo0972b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨56,by decide⟩
def lo0972b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨57,by decide⟩
def lo0972 : CheckedMoment :=
  CheckedMoment.ofBessel lo0972b1 lo0972b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0972b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨61,by decide⟩
def hi0972b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨62,by decide⟩
def hi0972 : CheckedMoment :=
  CheckedMoment.ofBessel hi0972b1 hi0972b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0972 : meanBracketCheck (227/500) lo0972 hi0972=true := by decide +kernel
def bracket0972 : MeanBracket := meanBracketOfMoments (227/500) lo0972 hi0972 accepted0972
def lo0973b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨2,by decide⟩
def lo0973b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨3,by decide⟩
def lo0973 : CheckedMoment :=
  CheckedMoment.ofBessel lo0973b1 lo0973b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0973b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨7,by decide⟩
def hi0973b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨8,by decide⟩
def hi0973 : CheckedMoment :=
  CheckedMoment.ofBessel hi0973b1 hi0973b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0973 : meanBracketCheck (91/200) lo0973 hi0973=true := by decide +kernel
def bracket0973 : MeanBracket := meanBracketOfMoments (91/200) lo0973 hi0973 accepted0973
def lo0974b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨12,by decide⟩
def lo0974b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨13,by decide⟩
def lo0974 : CheckedMoment :=
  CheckedMoment.ofBessel lo0974b1 lo0974b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0974b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨17,by decide⟩
def hi0974b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨18,by decide⟩
def hi0974 : CheckedMoment :=
  CheckedMoment.ofBessel hi0974b1 hi0974b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0974 : meanBracketCheck (57/125) lo0974 hi0974=true := by decide +kernel
def bracket0974 : MeanBracket := meanBracketOfMoments (57/125) lo0974 hi0974 accepted0974
def lo0975b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨22,by decide⟩
def lo0975b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨23,by decide⟩
def lo0975 : CheckedMoment :=
  CheckedMoment.ofBessel lo0975b1 lo0975b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0975b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨27,by decide⟩
def hi0975b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨28,by decide⟩
def hi0975 : CheckedMoment :=
  CheckedMoment.ofBessel hi0975b1 hi0975b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0975 : meanBracketCheck (457/1000) lo0975 hi0975=true := by decide +kernel
def bracket0975 : MeanBracket := meanBracketOfMoments (457/1000) lo0975 hi0975 accepted0975
#print axioms bracket0960
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0060
