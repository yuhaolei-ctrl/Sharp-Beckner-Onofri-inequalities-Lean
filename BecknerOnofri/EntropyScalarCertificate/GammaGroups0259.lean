module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0323
public import BecknerOnofri.EntropyScalarCertificate.Bessel0324
public import BecknerOnofri.EntropyScalarCertificate.Bessel0325
public import BecknerOnofri.EntropyScalarCertificate.Bessel0650
public import BecknerOnofri.EntropyScalarCertificate.Bessel0651
public import BecknerOnofri.EntropyScalarCertificate.Brackets0129
public import BecknerOnofri.EntropyScalarCertificate.Brackets0130
public import BecknerOnofri.EntropyScalarCertificate.Logs0259
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2072
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (6291168340686615431969084239534228294399/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6291168340686615431969084239534228294399/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (12612697260360652265523069989007729635571/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12612697260360652265523069989007729635571/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (25195033941733883129461238468076186224369/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25195033941733883129461238468076186224369/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2072 BracketBatch0129.bracket2073 (25195033941733883129461238468076186224369/4000000000000000000000000000000000000000) (1080279026390261266023335098793644148691/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2072 BracketBatch0129.bracket2073
  (25195033941733883129461238468076186224369/4000000000000000000000000000000000000000) (1080279026390261266023335098793644148691/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2072
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2073
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0323.rows BesselBatch0323.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (15765871575450815331903837486259662044463/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15765871575450815331903837486259662044463/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (63216042037742949300186142609761268214519/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (63216042037742949300186142609761268214519/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (126279528339546210627801492554799916392371/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (126279528339546210627801492554799916392371/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2073 BracketBatch0129.bracket2074 (126279528339546210627801492554799916392371/20000000000000000000000000000000000000000) (67613778516962605340506704998747454577/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2073 BracketBatch0129.bracket2074
  (126279528339546210627801492554799916392371/20000000000000000000000000000000000000000) (67613778516962605340506704998747454577/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2073
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2074
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (15804010509435737325046535652440317053629/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15804010509435737325046535652440317053629/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (63369356217408282701450669833727811991269/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (63369356217408282701450669833727811991269/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0650.rows BesselBatch0650.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (25317079651030246400327362488697816041157/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25317079651030246400327362488697816041157/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2074 BracketBatch0129.bracket2075 (25317079651030246400327362488697816041157/4000000000000000000000000000000000000000) (541683052852384030500374068121940298149/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2074 BracketBatch0129.bracket2075
  (25317079651030246400327362488697816041157/4000000000000000000000000000000000000000) (541683052852384030500374068121940298149/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2074
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2075
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (31684678108704141350725334916863905995633/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31684678108704141350725334916863905995633/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (12704686899855074198838801257121226808611/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12704686899855074198838801257121226808611/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (126892790716683653695644676119333946034321/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (126892790716683653695644676119333946034321/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2075 BracketBatch0129.bracket2076 (126892790716683653695644676119333946034321/20000000000000000000000000000000000000000) (542457998035196646551036875556275042949/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2075 BracketBatch0129.bracket2076
  (126892790716683653695644676119333946034321/20000000000000000000000000000000000000000) (542457998035196646551036875556275042949/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2075
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2076
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (15880858624818842748548501571401533510763/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15880858624818842748548501571401533510763/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (15919570649567128936944055961646592941869/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15919570649567128936944055961646592941869/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (3975053659298246460686569691631015806579/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3975053659298246460686569691631015806579/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2076 BracketBatch0129.bracket2077 (3975053659298246460686569691631015806579/625000000000000000000000000000000000000) (271617537227940094869351297951428806773/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2076 BracketBatch0129.bracket2077
  (3975053659298246460686569691631015806579/625000000000000000000000000000000000000) (271617537227940094869351297951428806773/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2076
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2077
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (63678282598268515747776223846586371767473/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (63678282598268515747776223846586371767473/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (31916953143232892589588862847048029708089/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31916953143232892589588862847048029708089/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (127512188884734300926953949540682431183651/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (127512188884734300926953949540682431183651/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2077 BracketBatch0129.bracket2078 (127512188884734300926953949540682431183651/20000000000000000000000000000000000000000) (1088028585937437014227481607513256981709/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2077 BracketBatch0129.bracket2078
  (127512188884734300926953949540682431183651/20000000000000000000000000000000000000000) (1088028585937437014227481607513256981709/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2077
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2078
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (2553356251458631407167109027763842376647/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2553356251458631407167109027763842376647/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (31995155696907599532277241292896096160557/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31995155696907599532277241292896096160557/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (127824217680280984243732208279888251737289/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (127824217680280984243732208279888251737289/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2078 BracketBatch0129.bracket2079 (127824217680280984243732208279888251737289/20000000000000000000000000000000000000000) (544795664511365170375742661198282813663/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2078 BracketBatch0129.bracket2079
  (127824217680280984243732208279888251737289/20000000000000000000000000000000000000000) (544795664511365170375742661198282813663/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2078
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2079
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0324.rows BesselBatch0324.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (63990311393815199064554482585792192321111/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (63990311393815199064554482585792192321111/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0325.rows BesselBatch0325.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1282950076177234212713358899500292634061/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1282950076177234212713358899500292634061/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0651.rows BesselBatch0651.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (128137815202676909700222427560806824024161/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (128137815202676909700222427560806824024161/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0259.rows ScalarLogs0259.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0129.bracket2079 BracketBatch0130.bracket2080 (128137815202676909700222427560806824024161/20000000000000000000000000000000000000000) (2182316800422724307540490552485121005593/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0129.bracket2079 BracketBatch0130.bracket2080
  (128137815202676909700222427560806824024161/20000000000000000000000000000000000000000) (2182316800422724307540490552485121005593/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2079
