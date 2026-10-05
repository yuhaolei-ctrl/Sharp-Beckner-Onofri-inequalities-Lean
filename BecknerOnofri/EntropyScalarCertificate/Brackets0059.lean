module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0147
public import BecknerOnofri.EntropyScalarCertificate.Bessel0148
public import BecknerOnofri.EntropyScalarCertificate.Bessel0149

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0059
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0944b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨32,by decide⟩
def lo0944b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨33,by decide⟩
def lo0944 : CheckedMoment :=
  CheckedMoment.ofBessel lo0944b1 lo0944b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0944b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨37,by decide⟩
def hi0944b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨38,by decide⟩
def hi0944 : CheckedMoment :=
  CheckedMoment.ofBessel hi0944b1 hi0944b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0944 : meanBracketCheck (213/500) lo0944 hi0944=true := by decide +kernel
def bracket0944 : MeanBracket := meanBracketOfMoments (213/500) lo0944 hi0944 accepted0944
def lo0945b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨42,by decide⟩
def lo0945b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨43,by decide⟩
def lo0945 : CheckedMoment :=
  CheckedMoment.ofBessel lo0945b1 lo0945b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0945b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨47,by decide⟩
def hi0945b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨48,by decide⟩
def hi0945 : CheckedMoment :=
  CheckedMoment.ofBessel hi0945b1 hi0945b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0945 : meanBracketCheck (427/1000) lo0945 hi0945=true := by decide +kernel
def bracket0945 : MeanBracket := meanBracketOfMoments (427/1000) lo0945 hi0945 accepted0945
def lo0946b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨52,by decide⟩
def lo0946b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨53,by decide⟩
def lo0946 : CheckedMoment :=
  CheckedMoment.ofBessel lo0946b1 lo0946b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0946b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨57,by decide⟩
def hi0946b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨58,by decide⟩
def hi0946 : CheckedMoment :=
  CheckedMoment.ofBessel hi0946b1 hi0946b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0946 : meanBracketCheck (107/250) lo0946 hi0946=true := by decide +kernel
def bracket0946 : MeanBracket := meanBracketOfMoments (107/250) lo0946 hi0946 accepted0946
def lo0947b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨62,by decide⟩
def lo0947b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0147.rows BesselBatch0147.accepted ⟨63,by decide⟩
def lo0947 : CheckedMoment :=
  CheckedMoment.ofBessel lo0947b1 lo0947b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0947b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨3,by decide⟩
def hi0947b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨4,by decide⟩
def hi0947 : CheckedMoment :=
  CheckedMoment.ofBessel hi0947b1 hi0947b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0947 : meanBracketCheck (429/1000) lo0947 hi0947=true := by decide +kernel
def bracket0947 : MeanBracket := meanBracketOfMoments (429/1000) lo0947 hi0947 accepted0947
def lo0948b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨8,by decide⟩
def lo0948b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨9,by decide⟩
def lo0948 : CheckedMoment :=
  CheckedMoment.ofBessel lo0948b1 lo0948b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0948b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨13,by decide⟩
def hi0948b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨14,by decide⟩
def hi0948 : CheckedMoment :=
  CheckedMoment.ofBessel hi0948b1 hi0948b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0948 : meanBracketCheck (43/100) lo0948 hi0948=true := by decide +kernel
def bracket0948 : MeanBracket := meanBracketOfMoments (43/100) lo0948 hi0948 accepted0948
def lo0949b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨18,by decide⟩
def lo0949b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨19,by decide⟩
def lo0949 : CheckedMoment :=
  CheckedMoment.ofBessel lo0949b1 lo0949b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0949b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨23,by decide⟩
def hi0949b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨24,by decide⟩
def hi0949 : CheckedMoment :=
  CheckedMoment.ofBessel hi0949b1 hi0949b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0949 : meanBracketCheck (431/1000) lo0949 hi0949=true := by decide +kernel
def bracket0949 : MeanBracket := meanBracketOfMoments (431/1000) lo0949 hi0949 accepted0949
def lo0950b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨28,by decide⟩
def lo0950b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨29,by decide⟩
def lo0950 : CheckedMoment :=
  CheckedMoment.ofBessel lo0950b1 lo0950b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0950b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨33,by decide⟩
def hi0950b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨34,by decide⟩
def hi0950 : CheckedMoment :=
  CheckedMoment.ofBessel hi0950b1 hi0950b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0950 : meanBracketCheck (54/125) lo0950 hi0950=true := by decide +kernel
def bracket0950 : MeanBracket := meanBracketOfMoments (54/125) lo0950 hi0950 accepted0950
def lo0951b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨38,by decide⟩
def lo0951b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨39,by decide⟩
def lo0951 : CheckedMoment :=
  CheckedMoment.ofBessel lo0951b1 lo0951b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0951b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨43,by decide⟩
def hi0951b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨44,by decide⟩
def hi0951 : CheckedMoment :=
  CheckedMoment.ofBessel hi0951b1 hi0951b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0951 : meanBracketCheck (433/1000) lo0951 hi0951=true := by decide +kernel
def bracket0951 : MeanBracket := meanBracketOfMoments (433/1000) lo0951 hi0951 accepted0951
def lo0952b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨48,by decide⟩
def lo0952b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨49,by decide⟩
def lo0952 : CheckedMoment :=
  CheckedMoment.ofBessel lo0952b1 lo0952b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0952b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨53,by decide⟩
def hi0952b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨54,by decide⟩
def hi0952 : CheckedMoment :=
  CheckedMoment.ofBessel hi0952b1 hi0952b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0952 : meanBracketCheck (217/500) lo0952 hi0952=true := by decide +kernel
def bracket0952 : MeanBracket := meanBracketOfMoments (217/500) lo0952 hi0952 accepted0952
def lo0953b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨58,by decide⟩
def lo0953b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨59,by decide⟩
def lo0953 : CheckedMoment :=
  CheckedMoment.ofBessel lo0953b1 lo0953b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0953b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0148.rows BesselBatch0148.accepted ⟨63,by decide⟩
def hi0953b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨0,by decide⟩
def hi0953 : CheckedMoment :=
  CheckedMoment.ofBessel hi0953b1 hi0953b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0953 : meanBracketCheck (87/200) lo0953 hi0953=true := by decide +kernel
def bracket0953 : MeanBracket := meanBracketOfMoments (87/200) lo0953 hi0953 accepted0953
def lo0954b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨4,by decide⟩
def lo0954b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨5,by decide⟩
def lo0954 : CheckedMoment :=
  CheckedMoment.ofBessel lo0954b1 lo0954b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0954b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨9,by decide⟩
def hi0954b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨10,by decide⟩
def hi0954 : CheckedMoment :=
  CheckedMoment.ofBessel hi0954b1 hi0954b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0954 : meanBracketCheck (109/250) lo0954 hi0954=true := by decide +kernel
def bracket0954 : MeanBracket := meanBracketOfMoments (109/250) lo0954 hi0954 accepted0954
def lo0955b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨14,by decide⟩
def lo0955b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨15,by decide⟩
def lo0955 : CheckedMoment :=
  CheckedMoment.ofBessel lo0955b1 lo0955b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0955b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨19,by decide⟩
def hi0955b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨20,by decide⟩
def hi0955 : CheckedMoment :=
  CheckedMoment.ofBessel hi0955b1 hi0955b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0955 : meanBracketCheck (437/1000) lo0955 hi0955=true := by decide +kernel
def bracket0955 : MeanBracket := meanBracketOfMoments (437/1000) lo0955 hi0955 accepted0955
def lo0956b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨24,by decide⟩
def lo0956b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨25,by decide⟩
def lo0956 : CheckedMoment :=
  CheckedMoment.ofBessel lo0956b1 lo0956b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0956b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨29,by decide⟩
def hi0956b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨30,by decide⟩
def hi0956 : CheckedMoment :=
  CheckedMoment.ofBessel hi0956b1 hi0956b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0956 : meanBracketCheck (219/500) lo0956 hi0956=true := by decide +kernel
def bracket0956 : MeanBracket := meanBracketOfMoments (219/500) lo0956 hi0956 accepted0956
def lo0957b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨34,by decide⟩
def lo0957b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨35,by decide⟩
def lo0957 : CheckedMoment :=
  CheckedMoment.ofBessel lo0957b1 lo0957b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0957b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨39,by decide⟩
def hi0957b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨40,by decide⟩
def hi0957 : CheckedMoment :=
  CheckedMoment.ofBessel hi0957b1 hi0957b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0957 : meanBracketCheck (439/1000) lo0957 hi0957=true := by decide +kernel
def bracket0957 : MeanBracket := meanBracketOfMoments (439/1000) lo0957 hi0957 accepted0957
def lo0958b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨44,by decide⟩
def lo0958b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨45,by decide⟩
def lo0958 : CheckedMoment :=
  CheckedMoment.ofBessel lo0958b1 lo0958b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0958b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨49,by decide⟩
def hi0958b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨50,by decide⟩
def hi0958 : CheckedMoment :=
  CheckedMoment.ofBessel hi0958b1 hi0958b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0958 : meanBracketCheck (11/25) lo0958 hi0958=true := by decide +kernel
def bracket0958 : MeanBracket := meanBracketOfMoments (11/25) lo0958 hi0958 accepted0958
def lo0959b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨54,by decide⟩
def lo0959b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨55,by decide⟩
def lo0959 : CheckedMoment :=
  CheckedMoment.ofBessel lo0959b1 lo0959b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0959b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨59,by decide⟩
def hi0959b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0149.rows BesselBatch0149.accepted ⟨60,by decide⟩
def hi0959 : CheckedMoment :=
  CheckedMoment.ofBessel hi0959b1 hi0959b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0959 : meanBracketCheck (441/1000) lo0959 hi0959=true := by decide +kernel
def bracket0959 : MeanBracket := meanBracketOfMoments (441/1000) lo0959 hi0959 accepted0959
#print axioms bracket0944
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0059
