import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0137
import BecknerOnofri.EntropyScalarCertificate.Bessel0138
import BecknerOnofri.EntropyScalarCertificate.Bessel0139
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0055
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0880b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨32,by decide⟩
def lo0880b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨33,by decide⟩
def lo0880 : CheckedMoment :=
  CheckedMoment.ofBessel lo0880b1 lo0880b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0880b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨37,by decide⟩
def hi0880b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨38,by decide⟩
def hi0880 : CheckedMoment :=
  CheckedMoment.ofBessel hi0880b1 hi0880b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0880 : meanBracketCheck (181/500) lo0880 hi0880=true := by decide +kernel
def bracket0880 : MeanBracket := meanBracketOfMoments (181/500) lo0880 hi0880 accepted0880
def lo0881b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨42,by decide⟩
def lo0881b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨43,by decide⟩
def lo0881 : CheckedMoment :=
  CheckedMoment.ofBessel lo0881b1 lo0881b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0881b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨47,by decide⟩
def hi0881b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨48,by decide⟩
def hi0881 : CheckedMoment :=
  CheckedMoment.ofBessel hi0881b1 hi0881b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0881 : meanBracketCheck (363/1000) lo0881 hi0881=true := by decide +kernel
def bracket0881 : MeanBracket := meanBracketOfMoments (363/1000) lo0881 hi0881 accepted0881
def lo0882b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨52,by decide⟩
def lo0882b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨53,by decide⟩
def lo0882 : CheckedMoment :=
  CheckedMoment.ofBessel lo0882b1 lo0882b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0882b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨57,by decide⟩
def hi0882b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨58,by decide⟩
def hi0882 : CheckedMoment :=
  CheckedMoment.ofBessel hi0882b1 hi0882b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0882 : meanBracketCheck (91/250) lo0882 hi0882=true := by decide +kernel
def bracket0882 : MeanBracket := meanBracketOfMoments (91/250) lo0882 hi0882 accepted0882
def lo0883b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨62,by decide⟩
def lo0883b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨63,by decide⟩
def lo0883 : CheckedMoment :=
  CheckedMoment.ofBessel lo0883b1 lo0883b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0883b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨3,by decide⟩
def hi0883b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨4,by decide⟩
def hi0883 : CheckedMoment :=
  CheckedMoment.ofBessel hi0883b1 hi0883b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0883 : meanBracketCheck (73/200) lo0883 hi0883=true := by decide +kernel
def bracket0883 : MeanBracket := meanBracketOfMoments (73/200) lo0883 hi0883 accepted0883
def lo0884b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨8,by decide⟩
def lo0884b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨9,by decide⟩
def lo0884 : CheckedMoment :=
  CheckedMoment.ofBessel lo0884b1 lo0884b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0884b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨13,by decide⟩
def hi0884b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨14,by decide⟩
def hi0884 : CheckedMoment :=
  CheckedMoment.ofBessel hi0884b1 hi0884b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0884 : meanBracketCheck (183/500) lo0884 hi0884=true := by decide +kernel
def bracket0884 : MeanBracket := meanBracketOfMoments (183/500) lo0884 hi0884 accepted0884
def lo0885b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨18,by decide⟩
def lo0885b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨19,by decide⟩
def lo0885 : CheckedMoment :=
  CheckedMoment.ofBessel lo0885b1 lo0885b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0885b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨23,by decide⟩
def hi0885b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨24,by decide⟩
def hi0885 : CheckedMoment :=
  CheckedMoment.ofBessel hi0885b1 hi0885b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0885 : meanBracketCheck (367/1000) lo0885 hi0885=true := by decide +kernel
def bracket0885 : MeanBracket := meanBracketOfMoments (367/1000) lo0885 hi0885 accepted0885
def lo0886b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨28,by decide⟩
def lo0886b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨29,by decide⟩
def lo0886 : CheckedMoment :=
  CheckedMoment.ofBessel lo0886b1 lo0886b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0886b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨33,by decide⟩
def hi0886b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨34,by decide⟩
def hi0886 : CheckedMoment :=
  CheckedMoment.ofBessel hi0886b1 hi0886b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0886 : meanBracketCheck (46/125) lo0886 hi0886=true := by decide +kernel
def bracket0886 : MeanBracket := meanBracketOfMoments (46/125) lo0886 hi0886 accepted0886
def lo0887b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨38,by decide⟩
def lo0887b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨39,by decide⟩
def lo0887 : CheckedMoment :=
  CheckedMoment.ofBessel lo0887b1 lo0887b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0887b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨43,by decide⟩
def hi0887b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨44,by decide⟩
def hi0887 : CheckedMoment :=
  CheckedMoment.ofBessel hi0887b1 hi0887b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0887 : meanBracketCheck (369/1000) lo0887 hi0887=true := by decide +kernel
def bracket0887 : MeanBracket := meanBracketOfMoments (369/1000) lo0887 hi0887 accepted0887
def lo0888b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨48,by decide⟩
def lo0888b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨49,by decide⟩
def lo0888 : CheckedMoment :=
  CheckedMoment.ofBessel lo0888b1 lo0888b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0888b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨53,by decide⟩
def hi0888b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨54,by decide⟩
def hi0888 : CheckedMoment :=
  CheckedMoment.ofBessel hi0888b1 hi0888b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0888 : meanBracketCheck (37/100) lo0888 hi0888=true := by decide +kernel
def bracket0888 : MeanBracket := meanBracketOfMoments (37/100) lo0888 hi0888 accepted0888
def lo0889b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨58,by decide⟩
def lo0889b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨59,by decide⟩
def lo0889 : CheckedMoment :=
  CheckedMoment.ofBessel lo0889b1 lo0889b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0889b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨63,by decide⟩
def hi0889b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨0,by decide⟩
def hi0889 : CheckedMoment :=
  CheckedMoment.ofBessel hi0889b1 hi0889b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0889 : meanBracketCheck (371/1000) lo0889 hi0889=true := by decide +kernel
def bracket0889 : MeanBracket := meanBracketOfMoments (371/1000) lo0889 hi0889 accepted0889
def lo0890b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨4,by decide⟩
def lo0890b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨5,by decide⟩
def lo0890 : CheckedMoment :=
  CheckedMoment.ofBessel lo0890b1 lo0890b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0890b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨9,by decide⟩
def hi0890b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨10,by decide⟩
def hi0890 : CheckedMoment :=
  CheckedMoment.ofBessel hi0890b1 hi0890b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0890 : meanBracketCheck (93/250) lo0890 hi0890=true := by decide +kernel
def bracket0890 : MeanBracket := meanBracketOfMoments (93/250) lo0890 hi0890 accepted0890
def lo0891b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨14,by decide⟩
def lo0891b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨15,by decide⟩
def lo0891 : CheckedMoment :=
  CheckedMoment.ofBessel lo0891b1 lo0891b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0891b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨19,by decide⟩
def hi0891b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨20,by decide⟩
def hi0891 : CheckedMoment :=
  CheckedMoment.ofBessel hi0891b1 hi0891b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0891 : meanBracketCheck (373/1000) lo0891 hi0891=true := by decide +kernel
def bracket0891 : MeanBracket := meanBracketOfMoments (373/1000) lo0891 hi0891 accepted0891
def lo0892b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨24,by decide⟩
def lo0892b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨25,by decide⟩
def lo0892 : CheckedMoment :=
  CheckedMoment.ofBessel lo0892b1 lo0892b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0892b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨29,by decide⟩
def hi0892b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨30,by decide⟩
def hi0892 : CheckedMoment :=
  CheckedMoment.ofBessel hi0892b1 hi0892b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0892 : meanBracketCheck (187/500) lo0892 hi0892=true := by decide +kernel
def bracket0892 : MeanBracket := meanBracketOfMoments (187/500) lo0892 hi0892 accepted0892
def lo0893b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨34,by decide⟩
def lo0893b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨35,by decide⟩
def lo0893 : CheckedMoment :=
  CheckedMoment.ofBessel lo0893b1 lo0893b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0893b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨39,by decide⟩
def hi0893b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨40,by decide⟩
def hi0893 : CheckedMoment :=
  CheckedMoment.ofBessel hi0893b1 hi0893b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0893 : meanBracketCheck (3/8) lo0893 hi0893=true := by decide +kernel
def bracket0893 : MeanBracket := meanBracketOfMoments (3/8) lo0893 hi0893 accepted0893
def lo0894b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨44,by decide⟩
def lo0894b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨45,by decide⟩
def lo0894 : CheckedMoment :=
  CheckedMoment.ofBessel lo0894b1 lo0894b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0894b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨49,by decide⟩
def hi0894b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨50,by decide⟩
def hi0894 : CheckedMoment :=
  CheckedMoment.ofBessel hi0894b1 hi0894b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0894 : meanBracketCheck (47/125) lo0894 hi0894=true := by decide +kernel
def bracket0894 : MeanBracket := meanBracketOfMoments (47/125) lo0894 hi0894 accepted0894
def lo0895b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨54,by decide⟩
def lo0895b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨55,by decide⟩
def lo0895 : CheckedMoment :=
  CheckedMoment.ofBessel lo0895b1 lo0895b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0895b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨59,by decide⟩
def hi0895b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨60,by decide⟩
def hi0895 : CheckedMoment :=
  CheckedMoment.ofBessel hi0895b1 hi0895b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0895 : meanBracketCheck (377/1000) lo0895 hi0895=true := by decide +kernel
def bracket0895 : MeanBracket := meanBracketOfMoments (377/1000) lo0895 hi0895 accepted0895
#print axioms bracket0880
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0055
