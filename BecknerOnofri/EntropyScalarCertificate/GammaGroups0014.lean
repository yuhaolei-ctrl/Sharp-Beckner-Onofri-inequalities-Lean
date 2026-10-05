module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0017
public import BecknerOnofri.EntropyScalarCertificate.Bessel0018
public import BecknerOnofri.EntropyScalarCertificate.Bessel0497
public import BecknerOnofri.EntropyScalarCertificate.Bessel0498
public import BecknerOnofri.EntropyScalarCertificate.Brackets0007
public import BecknerOnofri.EntropyScalarCertificate.Logs0014
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0112
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (39573433064534602034582683792627998873/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39573433064534602034582683792627998873/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (158697509590254037040572220373215369481/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (158697509590254037040572220373215369481/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (316991241848392445178902955543727364973/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (316991241848392445178902955543727364973/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0112 BracketBatch0007.bracket0113 (316991241848392445178902955543727364973/4000000000000000000000000000000000000000) (29858319942459169389497474958902473/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0112 BracketBatch0007.bracket0113
  (316991241848392445178902955543727364973/4000000000000000000000000000000000000000) (29858319942459169389497474958902473/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0112
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0113
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (396743773975635092601430550933038423701/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (396743773975635092601430550933038423701/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (198876632800595544475485951422221863833/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (198876632800595544475485951422221863833/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (794497039576826181552402453777482151367/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (794497039576826181552402453777482151367/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0113 BracketBatch0007.bracket0114 (794497039576826181552402453777482151367/10000000000000000000000000000000000000000) (1885420275634082430113756651267437/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0113 BracketBatch0007.bracket0114
  (794497039576826181552402453777482151367/10000000000000000000000000000000000000000) (1885420275634082430113756651267437/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0113
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0114
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (795506531202382177901943805688887455329/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (795506531202382177901943805688887455329/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (797525611296838975959258310740809631683/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (797525611296838975959258310740809631683/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (398258035624805288465300529107424271753/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (398258035624805288465300529107424271753/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0114 BracketBatch0007.bracket0115 (398258035624805288465300529107424271753/5000000000000000000000000000000000000000) (6095496664531569294103799529233403/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0114 BracketBatch0007.bracket0115
  (398258035624805288465300529107424271753/5000000000000000000000000000000000000000) (6095496664531569294103799529233403/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0114
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0115
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (2492267535302621799872682221065030099/31250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2492267535302621799872682221065030099/31250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (799544788487517690834430900104750542099/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (799544788487517690834430900104750542099/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (1597070399784356666793689210845560173779/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1597070399784356666793689210845560173779/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0115 BracketBatch0007.bracket0116 (1597070399784356666793689210845560173779/20000000000000000000000000000000000000000) (30790608677643069430382711544497081/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0115 BracketBatch0007.bracket0116
  (1597070399784356666793689210845560173779/20000000000000000000000000000000000000000) (30790608677643069430382711544497081/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0115
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0116
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (49971549280469855677151931256546908881/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (49971549280469855677151931256546908881/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (200391015756840442295587326678666597211/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (200391015756840442295587326678666597211/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (80055442575743973000839010340970846547/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (80055442575743973000839010340970846547/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0116 BracketBatch0007.bracket0117 (80055442575743973000839010340970846547/1000000000000000000000000000000000000000) (31106112503814691597036335088236447/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0116 BracketBatch0007.bracket0117
  (80055442575743973000839010340970846547/1000000000000000000000000000000000000000) (31106112503814691597036335088236447/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0116
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0117
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (801564063027361769182349306714666388841/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (801564063027361769182349306714666388841/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (803583435169381173868669357728816100941/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (803583435169381173868669357728816100941/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (802573749098371471525509332221741244891/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (802573749098371471525509332221741244891/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0117 BracketBatch0007.bracket0118 (802573749098371471525509332221741244891/10000000000000000000000000000000000000000) (15712003430479850904290285980710087/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0117 BracketBatch0007.bracket0118
  (802573749098371471525509332221741244891/10000000000000000000000000000000000000000) (15712003430479850904290285980710087/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0117
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0118
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (401791717584690586934334678864408050469/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (401791717584690586934334678864408050469/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (805602905166652565095154009295917140583/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (805602905166652565095154009295917140583/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (1609186340336033738963823367024733241521/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1609186340336033738963823367024733241521/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0118 BracketBatch0007.bracket0119 (1609186340336033738963823367024733241521/20000000000000000000000000000000000000000) (31744303839944288222626044185144997/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0118 BracketBatch0007.bracket0119
  (1609186340336033738963823367024733241521/20000000000000000000000000000000000000000) (31744303839944288222626044185144997/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0118
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0119
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (40280145258332628254757700464795857029/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (40280145258332628254757700464795857029/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (403811236636159740817581269610278969767/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (403811236636159740817581269610278969767/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (806612689219486023365158274258237540057/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (806612689219486023365158274258237540057/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0014.rows ScalarLogs0014.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0007.bracket0119 BracketBatch0007.bracket0120 (806612689219486023365158274258237540057/10000000000000000000000000000000000000000) (8016753890679942129159296555414461/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0007.bracket0119 BracketBatch0007.bracket0120
  (806612689219486023365158274258237540057/10000000000000000000000000000000000000000) (8016753890679942129159296555414461/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0119
