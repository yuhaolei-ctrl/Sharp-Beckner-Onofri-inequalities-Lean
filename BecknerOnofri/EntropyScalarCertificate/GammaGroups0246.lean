module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0307
public import BecknerOnofri.EntropyScalarCertificate.Bessel0308
public import BecknerOnofri.EntropyScalarCertificate.Bessel0642
public import BecknerOnofri.EntropyScalarCertificate.Bessel0643
public import BecknerOnofri.EntropyScalarCertificate.Brackets0123
public import BecknerOnofri.EntropyScalarCertificate.Logs0246
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1968
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (5853249682561593797335822822503530434321/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5853249682561593797335822822503530434321/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (47241685936534706366890205745620361724967/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (47241685936534706366890205745620361724967/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (18813536679405491349115357665129721039907/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18813536679405491349115357665129721039907/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1968 BracketBatch0123.bracket1969 (18813536679405491349115357665129721039907/4000000000000000000000000000000000000000) (177524949756631769837911807719548653063/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1968 BracketBatch0123.bracket1969
  (18813536679405491349115357665129721039907/4000000000000000000000000000000000000000) (177524949756631769837911807719548653063/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1968
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1969
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (11810421484133676591722551436405090431241/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11810421484133676591722551436405090431241/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (47665102626233126379864992778361355501587/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (47665102626233126379864992778361355501587/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (94906788562767832746755198523981717226551/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (94906788562767832746755198523981717226551/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1969 BracketBatch0123.bracket1970 (94906788562767832746755198523981717226551/20000000000000000000000000000000000000000) (1785975334436489320952536826354151647169/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1969 BracketBatch0123.bracket1970
  (94906788562767832746755198523981717226551/20000000000000000000000000000000000000000) (1785975334436489320952536826354151647169/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1969
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1970
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (2979068914139570398741562048647584718849/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2979068914139570398741562048647584718849/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (9619292794426621736245979478225972946153/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9619292794426621736245979478225972946153/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (95761566598366235061094890169491220232349/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (95761566598366235061094890169491220232349/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1970 BracketBatch0123.bracket1971 (95761566598366235061094890169491220232349/20000000000000000000000000000000000000000) (1796806654742519422350886057886770649003/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1970 BracketBatch0123.bracket1971
  (95761566598366235061094890169491220232349/20000000000000000000000000000000000000000) (1796806654742519422350886057886770649003/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1970
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1971
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0307.rows BesselBatch0307.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (24048231986066554340614948695564932365381/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (24048231986066554340614948695564932365381/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (48535994588773680438299170430337761721913/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (48535994588773680438299170430337761721913/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (3865298342436271564781162712858705058107/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3865298342436271564781162712858705058107/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1971 BracketBatch0123.bracket1972 (3865298342436271564781162712858705058107/800000000000000000000000000000000000000) (1807745155480676280325069550091461985197/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1971 BracketBatch0123.bracket1972
  (3865298342436271564781162712858705058107/800000000000000000000000000000000000000) (1807745155480676280325069550091461985197/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1971
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1972
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (4853599458877368043829917043033776172191/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4853599458877368043829917043033776172191/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (48983927651775930459484539185121224492909/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (48983927651775930459484539185121224492909/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (97519922240549610897783709615458986214819/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (97519922240549610897783709615458986214819/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1972 BracketBatch0123.bracket1973 (97519922240549610897783709615458986214819/20000000000000000000000000000000000000000) (1818792572126702215926439543907592689189/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1972 BracketBatch0123.bracket1973
  (97519922240549610897783709615458986214819/20000000000000000000000000000000000000000) (1818792572126702215926439543907592689189/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1972
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1973
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (24491963825887965229742269592560612246453/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (24491963825887965229742269592560612246453/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (49440505309372422592806446748413812111109/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (49440505309372422592806446748413812111109/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (19684886592229670610458197186707007320803/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19684886592229670610458197186707007320803/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1973 BracketBatch0123.bracket1974 (19684886592229670610458197186707007320803/4000000000000000000000000000000000000000) (914975339758627071185548314753672483229/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1973 BracketBatch0123.bracket1974
  (19684886592229670610458197186707007320803/4000000000000000000000000000000000000000) (914975339758627071185548314753672483229/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1973
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1974
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (24720252654686211296403223374206906055553/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (24720252654686211296403223374206906055553/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (12476494779475890921580977685127063347091/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12476494779475890921580977685127063347091/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (9934648442727598627913035748892206549947/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9934648442727598627913035748892206549947/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1974 BracketBatch0123.bracket1975 (9934648442727598627913035748892206549947/2000000000000000000000000000000000000000) (1841221292732866602785657349707049571661/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1974 BracketBatch0123.bracket1975
  (9934648442727598627913035748892206549947/2000000000000000000000000000000000000000) (1841221292732866602785657349707049571661/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1974
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1975
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (49905979117903563686323910740508253388361/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (49905979117903563686323910740508253388361/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0308.rows BesselBatch0308.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (25190305251463132965838452828494060304169/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (25190305251463132965838452828494060304169/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (100286589620829829618000816397496373996699/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (100286589620829829618000816397496373996699/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0246.rows ScalarLogs0246.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0123.bracket1975 BracketBatch0123.bracket1976 (100286589620829829618000816397496373996699/20000000000000000000000000000000000000000) (926303133989695288135217927985608947899/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0123.bracket1975 BracketBatch0123.bracket1976
  (100286589620829829618000816397496373996699/20000000000000000000000000000000000000000) (926303133989695288135217927985608947899/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1975
