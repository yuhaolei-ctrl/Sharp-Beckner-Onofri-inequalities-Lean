module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0006
public import BecknerOnofri.EntropyScalarCertificate.Bessel0007
public import BecknerOnofri.EntropyScalarCertificate.Bessel0492
public import BecknerOnofri.EntropyScalarCertificate.Brackets0002
public import BecknerOnofri.EntropyScalarCertificate.Brackets0003
public import BecknerOnofri.EntropyScalarCertificate.Logs0005
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0040
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (32317317526234389522343405854101124567/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (32317317526234389522343405854101124567/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (324179471491785995609366619961050353611/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (324179471491785995609366619961050353611/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (647352646754129890832800678502061599281/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (647352646754129890832800678502061599281/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0040 BracketBatch0002.bracket0041 (647352646754129890832800678502061599281/10000000000000000000000000000000000000000) (6550299736888918544621725085677097/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0040 BracketBatch0002.bracket0041
  (647352646754129890832800678502061599281/10000000000000000000000000000000000000000) (6550299736888918544621725085677097/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0040
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0041
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (648358942983571991218733239922100707219/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (648358942983571991218733239922100707219/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (650371613992854867347751334027392640721/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (650371613992854867347751334027392640721/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (64936527848821342928324228697474667397/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64936527848821342928324228697474667397/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0041 BracketBatch0002.bracket0042 (64936527848821342928324228697474667397/1000000000000000000000000000000000000000) (13269006694002153445585614942191871/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0041 BracketBatch0002.bracket0042
  (64936527848821342928324228697474667397/1000000000000000000000000000000000000000) (13269006694002153445585614942191871/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0041
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0042
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (325185806996427433673875667013696320359/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (325185806996427433673875667013696320359/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (652384363801052968872609323656342125511/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (652384363801052968872609323656342125511/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (1302755977793907836220360657683734766229/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1302755977793907836220360657683734766229/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0042 BracketBatch0002.bracket0043 (1302755977793907836220360657683734766229/20000000000000000000000000000000000000000) (6719492905202104949001471349446391/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0042 BracketBatch0002.bracket0043
  (1302755977793907836220360657683734766229/20000000000000000000000000000000000000000) (6719492905202104949001471349446391/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0042
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0043
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (163096090950263242218152330914085531377/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (163096090950263242218152330914085531377/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (654397192656736242501712156279241126997/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (654397192656736242501712156279241126997/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (261356311291557842274864295987116650501/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (261356311291557842274864295987116650501/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0043 BracketBatch0002.bracket0044 (261356311291557842274864295987116650501/4000000000000000000000000000000000000000) (13610546598259690961461931123762329/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0043 BracketBatch0002.bracket0044
  (261356311291557842274864295987116650501/4000000000000000000000000000000000000000) (13610546598259690961461931123762329/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0043
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0044
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (327198596328368121250856078139620563497/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (327198596328368121250856078139620563497/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (656410100808528205448066244085638010519/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (656410100808528205448066244085638010519/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (1310807293465264447949778400364879137513/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1310807293465264447949778400364879137513/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0044 BracketBatch0002.bracket0045 (1310807293465264447949778400364879137513/20000000000000000000000000000000000000000) (13783698863528214840168718161107009/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0044 BracketBatch0002.bracket0045
  (1310807293465264447949778400364879137513/20000000000000000000000000000000000000000) (13783698863528214840168718161107009/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0044
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0045
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (164102525202132051362016561021409502629/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (164102525202132051362016561021409502629/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (26336923540204244774065130259130260749/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26336923540204244774065130259130260749/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (1314833189313634324799694500563894529241/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1314833189313634324799694500563894529241/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0045 BracketBatch0002.bracket0046 (1314833189313634324799694500563894529241/20000000000000000000000000000000000000000) (3489613110714527045495456006879361/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0045 BracketBatch0002.bracket0046
  (1314833189313634324799694500563894529241/20000000000000000000000000000000000000000) (3489613110714527045495456006879361/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0045
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0046
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (329211544252553059675814128239128259361/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (329211544252553059675814128239128259361/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (660436155995201164289415452997036482029/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (660436155995201164289415452997036482029/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (1318859244500307283641043709475293000751/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1318859244500307283641043709475293000751/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0046 BracketBatch0002.bracket0047 (1318859244500307283641043709475293000751/20000000000000000000000000000000000000000) (1413481720359119619714144437472921/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0046 BracketBatch0002.bracket0047
  (1318859244500307283641043709475293000751/20000000000000000000000000000000000000000) (1413481720359119619714144437472921/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0046
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0047
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (330218077997600582144707726498518241013/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (330218077997600582144707726498518241013/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (662449303527598612873674007189494330483/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (662449303527598612873674007189494330483/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (1322885459522799777163089460186530812509/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1322885459522799777163089460186530812509/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0005.rows ScalarLogs0005.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0047 BracketBatch0003.bracket0048 (1322885459522799777163089460186530812509/20000000000000000000000000000000000000000) (14312803043767608147638000494576521/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0047 BracketBatch0003.bracket0048
  (1322885459522799777163089460186530812509/20000000000000000000000000000000000000000) (14312803043767608147638000494576521/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0047
