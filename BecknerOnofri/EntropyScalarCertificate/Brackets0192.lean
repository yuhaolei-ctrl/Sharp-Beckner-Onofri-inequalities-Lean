import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0480
import BecknerOnofri.EntropyScalarCertificate.Bessel0481
import BecknerOnofri.EntropyScalarCertificate.Bessel0482
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0192
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo3072b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨0,by decide⟩
def lo3072b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨1,by decide⟩
def lo3072 : CheckedMoment :=
  CheckedMoment.ofBessel lo3072b1 lo3072b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3072b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨5,by decide⟩
def hi3072b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨6,by decide⟩
def hi3072 : CheckedMoment :=
  CheckedMoment.ofBessel hi3072b1 hi3072b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3072 : meanBracketCheck (3121/3125) lo3072 hi3072=true := by decide +kernel
def bracket3072 : MeanBracket := meanBracketOfMoments (3121/3125) lo3072 hi3072 accepted3072
def lo3073b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨10,by decide⟩
def lo3073b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨11,by decide⟩
def lo3073 : CheckedMoment :=
  CheckedMoment.ofBessel lo3073b1 lo3073b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3073b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨15,by decide⟩
def hi3073b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨16,by decide⟩
def hi3073 : CheckedMoment :=
  CheckedMoment.ofBessel hi3073b1 hi3073b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3073 : meanBracketCheck (39949/40000) lo3073 hi3073=true := by decide +kernel
def bracket3073 : MeanBracket := meanBracketOfMoments (39949/40000) lo3073 hi3073 accepted3073
def lo3074b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨20,by decide⟩
def lo3074b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨21,by decide⟩
def lo3074 : CheckedMoment :=
  CheckedMoment.ofBessel lo3074b1 lo3074b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3074b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨25,by decide⟩
def hi3074b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨26,by decide⟩
def hi3074 : CheckedMoment :=
  CheckedMoment.ofBessel hi3074b1 hi3074b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3074 : meanBracketCheck (99873/100000) lo3074 hi3074=true := by decide +kernel
def bracket3074 : MeanBracket := meanBracketOfMoments (99873/100000) lo3074 hi3074 accepted3074
def lo3075b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨30,by decide⟩
def lo3075b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨31,by decide⟩
def lo3075 : CheckedMoment :=
  CheckedMoment.ofBessel lo3075b1 lo3075b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3075b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨35,by decide⟩
def hi3075b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨36,by decide⟩
def hi3075 : CheckedMoment :=
  CheckedMoment.ofBessel hi3075b1 hi3075b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3075 : meanBracketCheck (199747/200000) lo3075 hi3075=true := by decide +kernel
def bracket3075 : MeanBracket := meanBracketOfMoments (199747/200000) lo3075 hi3075 accepted3075
def lo3076b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨40,by decide⟩
def lo3076b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨41,by decide⟩
def lo3076 : CheckedMoment :=
  CheckedMoment.ofBessel lo3076b1 lo3076b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3076b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨45,by decide⟩
def hi3076b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨46,by decide⟩
def hi3076 : CheckedMoment :=
  CheckedMoment.ofBessel hi3076b1 hi3076b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3076 : meanBracketCheck (49937/50000) lo3076 hi3076=true := by decide +kernel
def bracket3076 : MeanBracket := meanBracketOfMoments (49937/50000) lo3076 hi3076 accepted3076
def lo3077b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨50,by decide⟩
def lo3077b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨51,by decide⟩
def lo3077 : CheckedMoment :=
  CheckedMoment.ofBessel lo3077b1 lo3077b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3077b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨55,by decide⟩
def hi3077b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨56,by decide⟩
def hi3077 : CheckedMoment :=
  CheckedMoment.ofBessel hi3077b1 hi3077b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3077 : meanBracketCheck (199749/200000) lo3077 hi3077=true := by decide +kernel
def bracket3077 : MeanBracket := meanBracketOfMoments (199749/200000) lo3077 hi3077 accepted3077
def lo3078b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨60,by decide⟩
def lo3078b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨61,by decide⟩
def lo3078 : CheckedMoment :=
  CheckedMoment.ofBessel lo3078b1 lo3078b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3078b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨1,by decide⟩
def hi3078b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨2,by decide⟩
def hi3078 : CheckedMoment :=
  CheckedMoment.ofBessel hi3078b1 hi3078b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3078 : meanBracketCheck (799/800) lo3078 hi3078=true := by decide +kernel
def bracket3078 : MeanBracket := meanBracketOfMoments (799/800) lo3078 hi3078 accepted3078
def lo3079b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨6,by decide⟩
def lo3079b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨7,by decide⟩
def lo3079 : CheckedMoment :=
  CheckedMoment.ofBessel lo3079b1 lo3079b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3079b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨11,by decide⟩
def hi3079b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨12,by decide⟩
def hi3079 : CheckedMoment :=
  CheckedMoment.ofBessel hi3079b1 hi3079b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3079 : meanBracketCheck (199751/200000) lo3079 hi3079=true := by decide +kernel
def bracket3079 : MeanBracket := meanBracketOfMoments (199751/200000) lo3079 hi3079 accepted3079
def lo3080b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨16,by decide⟩
def lo3080b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨17,by decide⟩
def lo3080 : CheckedMoment :=
  CheckedMoment.ofBessel lo3080b1 lo3080b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3080b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨21,by decide⟩
def hi3080b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨22,by decide⟩
def hi3080 : CheckedMoment :=
  CheckedMoment.ofBessel hi3080b1 hi3080b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3080 : meanBracketCheck (24969/25000) lo3080 hi3080=true := by decide +kernel
def bracket3080 : MeanBracket := meanBracketOfMoments (24969/25000) lo3080 hi3080 accepted3080
def lo3081b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨26,by decide⟩
def lo3081b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨27,by decide⟩
def lo3081 : CheckedMoment :=
  CheckedMoment.ofBessel lo3081b1 lo3081b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3081b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨31,by decide⟩
def hi3081b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨32,by decide⟩
def hi3081 : CheckedMoment :=
  CheckedMoment.ofBessel hi3081b1 hi3081b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3081 : meanBracketCheck (199753/200000) lo3081 hi3081=true := by decide +kernel
def bracket3081 : MeanBracket := meanBracketOfMoments (199753/200000) lo3081 hi3081 accepted3081
def lo3082b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨36,by decide⟩
def lo3082b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨37,by decide⟩
def lo3082 : CheckedMoment :=
  CheckedMoment.ofBessel lo3082b1 lo3082b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3082b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨41,by decide⟩
def hi3082b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨42,by decide⟩
def hi3082 : CheckedMoment :=
  CheckedMoment.ofBessel hi3082b1 hi3082b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3082 : meanBracketCheck (99877/100000) lo3082 hi3082=true := by decide +kernel
def bracket3082 : MeanBracket := meanBracketOfMoments (99877/100000) lo3082 hi3082 accepted3082
def lo3083b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨46,by decide⟩
def lo3083b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨47,by decide⟩
def lo3083 : CheckedMoment :=
  CheckedMoment.ofBessel lo3083b1 lo3083b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3083b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨51,by decide⟩
def hi3083b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨52,by decide⟩
def hi3083 : CheckedMoment :=
  CheckedMoment.ofBessel hi3083b1 hi3083b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3083 : meanBracketCheck (39951/40000) lo3083 hi3083=true := by decide +kernel
def bracket3083 : MeanBracket := meanBracketOfMoments (39951/40000) lo3083 hi3083 accepted3083
def lo3084b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨56,by decide⟩
def lo3084b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨57,by decide⟩
def lo3084 : CheckedMoment :=
  CheckedMoment.ofBessel lo3084b1 lo3084b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3084b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨61,by decide⟩
def hi3084b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨62,by decide⟩
def hi3084 : CheckedMoment :=
  CheckedMoment.ofBessel hi3084b1 hi3084b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3084 : meanBracketCheck (49939/50000) lo3084 hi3084=true := by decide +kernel
def bracket3084 : MeanBracket := meanBracketOfMoments (49939/50000) lo3084 hi3084 accepted3084
def lo3085b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨2,by decide⟩
def lo3085b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨3,by decide⟩
def lo3085 : CheckedMoment :=
  CheckedMoment.ofBessel lo3085b1 lo3085b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3085b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨7,by decide⟩
def hi3085b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨8,by decide⟩
def hi3085 : CheckedMoment :=
  CheckedMoment.ofBessel hi3085b1 hi3085b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3085 : meanBracketCheck (199757/200000) lo3085 hi3085=true := by decide +kernel
def bracket3085 : MeanBracket := meanBracketOfMoments (199757/200000) lo3085 hi3085 accepted3085
def lo3086b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨12,by decide⟩
def lo3086b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨13,by decide⟩
def lo3086 : CheckedMoment :=
  CheckedMoment.ofBessel lo3086b1 lo3086b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3086b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨17,by decide⟩
def hi3086b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨18,by decide⟩
def hi3086 : CheckedMoment :=
  CheckedMoment.ofBessel hi3086b1 hi3086b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3086 : meanBracketCheck (99879/100000) lo3086 hi3086=true := by decide +kernel
def bracket3086 : MeanBracket := meanBracketOfMoments (99879/100000) lo3086 hi3086 accepted3086
def lo3087b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨22,by decide⟩
def lo3087b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨23,by decide⟩
def lo3087 : CheckedMoment :=
  CheckedMoment.ofBessel lo3087b1 lo3087b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3087b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨27,by decide⟩
def hi3087b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨28,by decide⟩
def hi3087 : CheckedMoment :=
  CheckedMoment.ofBessel hi3087b1 hi3087b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3087 : meanBracketCheck (199759/200000) lo3087 hi3087=true := by decide +kernel
def bracket3087 : MeanBracket := meanBracketOfMoments (199759/200000) lo3087 hi3087 accepted3087
#print axioms bracket3072
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0192
