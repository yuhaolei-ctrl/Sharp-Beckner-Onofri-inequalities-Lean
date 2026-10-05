module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0135
public import BecknerOnofri.EntropyScalarCertificate.Bessel0136
public import BecknerOnofri.EntropyScalarCertificate.Bessel0137

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0054
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0864b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨0,by decide⟩
def lo0864b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨1,by decide⟩
def lo0864 : CheckedMoment :=
  CheckedMoment.ofBessel lo0864b1 lo0864b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0864b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨5,by decide⟩
def hi0864b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨6,by decide⟩
def hi0864 : CheckedMoment :=
  CheckedMoment.ofBessel hi0864b1 hi0864b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0864 : meanBracketCheck (173/500) lo0864 hi0864=true := by decide +kernel
def bracket0864 : MeanBracket := meanBracketOfMoments (173/500) lo0864 hi0864 accepted0864
def lo0865b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨10,by decide⟩
def lo0865b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨11,by decide⟩
def lo0865 : CheckedMoment :=
  CheckedMoment.ofBessel lo0865b1 lo0865b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0865b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨15,by decide⟩
def hi0865b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨16,by decide⟩
def hi0865 : CheckedMoment :=
  CheckedMoment.ofBessel hi0865b1 hi0865b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0865 : meanBracketCheck (347/1000) lo0865 hi0865=true := by decide +kernel
def bracket0865 : MeanBracket := meanBracketOfMoments (347/1000) lo0865 hi0865 accepted0865
def lo0866b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨20,by decide⟩
def lo0866b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨21,by decide⟩
def lo0866 : CheckedMoment :=
  CheckedMoment.ofBessel lo0866b1 lo0866b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0866b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨25,by decide⟩
def hi0866b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨26,by decide⟩
def hi0866 : CheckedMoment :=
  CheckedMoment.ofBessel hi0866b1 hi0866b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0866 : meanBracketCheck (87/250) lo0866 hi0866=true := by decide +kernel
def bracket0866 : MeanBracket := meanBracketOfMoments (87/250) lo0866 hi0866 accepted0866
def lo0867b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨30,by decide⟩
def lo0867b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨31,by decide⟩
def lo0867 : CheckedMoment :=
  CheckedMoment.ofBessel lo0867b1 lo0867b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0867b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨35,by decide⟩
def hi0867b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨36,by decide⟩
def hi0867 : CheckedMoment :=
  CheckedMoment.ofBessel hi0867b1 hi0867b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0867 : meanBracketCheck (349/1000) lo0867 hi0867=true := by decide +kernel
def bracket0867 : MeanBracket := meanBracketOfMoments (349/1000) lo0867 hi0867 accepted0867
def lo0868b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨40,by decide⟩
def lo0868b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨41,by decide⟩
def lo0868 : CheckedMoment :=
  CheckedMoment.ofBessel lo0868b1 lo0868b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0868b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨45,by decide⟩
def hi0868b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨46,by decide⟩
def hi0868 : CheckedMoment :=
  CheckedMoment.ofBessel hi0868b1 hi0868b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0868 : meanBracketCheck (7/20) lo0868 hi0868=true := by decide +kernel
def bracket0868 : MeanBracket := meanBracketOfMoments (7/20) lo0868 hi0868 accepted0868
def lo0869b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨50,by decide⟩
def lo0869b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨51,by decide⟩
def lo0869 : CheckedMoment :=
  CheckedMoment.ofBessel lo0869b1 lo0869b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0869b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨55,by decide⟩
def hi0869b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨56,by decide⟩
def hi0869 : CheckedMoment :=
  CheckedMoment.ofBessel hi0869b1 hi0869b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0869 : meanBracketCheck (351/1000) lo0869 hi0869=true := by decide +kernel
def bracket0869 : MeanBracket := meanBracketOfMoments (351/1000) lo0869 hi0869 accepted0869
def lo0870b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨60,by decide⟩
def lo0870b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨61,by decide⟩
def lo0870 : CheckedMoment :=
  CheckedMoment.ofBessel lo0870b1 lo0870b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0870b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨1,by decide⟩
def hi0870b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨2,by decide⟩
def hi0870 : CheckedMoment :=
  CheckedMoment.ofBessel hi0870b1 hi0870b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0870 : meanBracketCheck (44/125) lo0870 hi0870=true := by decide +kernel
def bracket0870 : MeanBracket := meanBracketOfMoments (44/125) lo0870 hi0870 accepted0870
def lo0871b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨6,by decide⟩
def lo0871b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨7,by decide⟩
def lo0871 : CheckedMoment :=
  CheckedMoment.ofBessel lo0871b1 lo0871b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0871b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨11,by decide⟩
def hi0871b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨12,by decide⟩
def hi0871 : CheckedMoment :=
  CheckedMoment.ofBessel hi0871b1 hi0871b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0871 : meanBracketCheck (353/1000) lo0871 hi0871=true := by decide +kernel
def bracket0871 : MeanBracket := meanBracketOfMoments (353/1000) lo0871 hi0871 accepted0871
def lo0872b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨16,by decide⟩
def lo0872b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨17,by decide⟩
def lo0872 : CheckedMoment :=
  CheckedMoment.ofBessel lo0872b1 lo0872b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0872b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨21,by decide⟩
def hi0872b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨22,by decide⟩
def hi0872 : CheckedMoment :=
  CheckedMoment.ofBessel hi0872b1 hi0872b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0872 : meanBracketCheck (177/500) lo0872 hi0872=true := by decide +kernel
def bracket0872 : MeanBracket := meanBracketOfMoments (177/500) lo0872 hi0872 accepted0872
def lo0873b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨26,by decide⟩
def lo0873b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨27,by decide⟩
def lo0873 : CheckedMoment :=
  CheckedMoment.ofBessel lo0873b1 lo0873b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0873b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨31,by decide⟩
def hi0873b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨32,by decide⟩
def hi0873 : CheckedMoment :=
  CheckedMoment.ofBessel hi0873b1 hi0873b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0873 : meanBracketCheck (71/200) lo0873 hi0873=true := by decide +kernel
def bracket0873 : MeanBracket := meanBracketOfMoments (71/200) lo0873 hi0873 accepted0873
def lo0874b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨36,by decide⟩
def lo0874b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨37,by decide⟩
def lo0874 : CheckedMoment :=
  CheckedMoment.ofBessel lo0874b1 lo0874b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0874b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨41,by decide⟩
def hi0874b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨42,by decide⟩
def hi0874 : CheckedMoment :=
  CheckedMoment.ofBessel hi0874b1 hi0874b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0874 : meanBracketCheck (89/250) lo0874 hi0874=true := by decide +kernel
def bracket0874 : MeanBracket := meanBracketOfMoments (89/250) lo0874 hi0874 accepted0874
def lo0875b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨46,by decide⟩
def lo0875b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨47,by decide⟩
def lo0875 : CheckedMoment :=
  CheckedMoment.ofBessel lo0875b1 lo0875b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0875b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨51,by decide⟩
def hi0875b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨52,by decide⟩
def hi0875 : CheckedMoment :=
  CheckedMoment.ofBessel hi0875b1 hi0875b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0875 : meanBracketCheck (357/1000) lo0875 hi0875=true := by decide +kernel
def bracket0875 : MeanBracket := meanBracketOfMoments (357/1000) lo0875 hi0875 accepted0875
def lo0876b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨56,by decide⟩
def lo0876b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨57,by decide⟩
def lo0876 : CheckedMoment :=
  CheckedMoment.ofBessel lo0876b1 lo0876b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0876b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨61,by decide⟩
def hi0876b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨62,by decide⟩
def hi0876 : CheckedMoment :=
  CheckedMoment.ofBessel hi0876b1 hi0876b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0876 : meanBracketCheck (179/500) lo0876 hi0876=true := by decide +kernel
def bracket0876 : MeanBracket := meanBracketOfMoments (179/500) lo0876 hi0876 accepted0876
def lo0877b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨2,by decide⟩
def lo0877b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨3,by decide⟩
def lo0877 : CheckedMoment :=
  CheckedMoment.ofBessel lo0877b1 lo0877b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0877b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨7,by decide⟩
def hi0877b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨8,by decide⟩
def hi0877 : CheckedMoment :=
  CheckedMoment.ofBessel hi0877b1 hi0877b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0877 : meanBracketCheck (359/1000) lo0877 hi0877=true := by decide +kernel
def bracket0877 : MeanBracket := meanBracketOfMoments (359/1000) lo0877 hi0877 accepted0877
def lo0878b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨12,by decide⟩
def lo0878b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨13,by decide⟩
def lo0878 : CheckedMoment :=
  CheckedMoment.ofBessel lo0878b1 lo0878b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0878b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨17,by decide⟩
def hi0878b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨18,by decide⟩
def hi0878 : CheckedMoment :=
  CheckedMoment.ofBessel hi0878b1 hi0878b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0878 : meanBracketCheck (9/25) lo0878 hi0878=true := by decide +kernel
def bracket0878 : MeanBracket := meanBracketOfMoments (9/25) lo0878 hi0878 accepted0878
def lo0879b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨22,by decide⟩
def lo0879b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨23,by decide⟩
def lo0879 : CheckedMoment :=
  CheckedMoment.ofBessel lo0879b1 lo0879b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0879b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨27,by decide⟩
def hi0879b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨28,by decide⟩
def hi0879 : CheckedMoment :=
  CheckedMoment.ofBessel hi0879b1 hi0879b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0879 : meanBracketCheck (361/1000) lo0879 hi0879=true := by decide +kernel
def bracket0879 : MeanBracket := meanBracketOfMoments (361/1000) lo0879 hi0879 accepted0879
#print axioms bracket0864
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0054
