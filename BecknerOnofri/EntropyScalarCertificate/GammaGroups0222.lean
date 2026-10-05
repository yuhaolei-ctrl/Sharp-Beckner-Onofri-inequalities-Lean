module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0277
public import BecknerOnofri.EntropyScalarCertificate.Bessel0278
public import BecknerOnofri.EntropyScalarCertificate.Bessel0627
public import BecknerOnofri.EntropyScalarCertificate.Bessel0628
public import BecknerOnofri.EntropyScalarCertificate.Brackets0111
public import BecknerOnofri.EntropyScalarCertificate.Logs0222
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1776
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (5214119815579903464846572361782470360309/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5214119815579903464846572361782470360309/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (10435402909508300462017770501519468519521/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10435402909508300462017770501519468519521/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (20863642540668107391710915225084409240139/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20863642540668107391710915225084409240139/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1776 BracketBatch0111.bracket1777 (20863642540668107391710915225084409240139/10000000000000000000000000000000000000000) (844760852352458328145513586685766397681/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1776 BracketBatch0111.bracket1777
  (20863642540668107391710915225084409240139/10000000000000000000000000000000000000000) (844760852352458328145513586685766397681/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1776
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1777
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (20870805819016600924035541003038937039039/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20870805819016600924035541003038937039039/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (20885154894028945430940318965498297505787/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20885154894028945430940318965498297505787/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (20877980356522773177487929984268617272413/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20877980356522773177487929984268617272413/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1777 BracketBatch0111.bracket1778 (20877980356522773177487929984268617272413/10000000000000000000000000000000000000000) (422738419216922366913773608382676480029/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1777 BracketBatch0111.bracket1778
  (20877980356522773177487929984268617272413/10000000000000000000000000000000000000000) (422738419216922366913773608382676480029/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1777
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1778
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (2610644361753618178867539870687287188223/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2610644361753618178867539870687287188223/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (5224881635322139518078740479804349332683/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5224881635322139518078740479804349332683/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (10446170358829375875813820221178923709129/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10446170358829375875813820221178923709129/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1778 BracketBatch0111.bracket1779 (10446170358829375875813820221178923709129/5000000000000000000000000000000000000000) (105774208866399862513611725633388443913/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1778 BracketBatch0111.bracket1779
  (10446170358829375875813820221178923709129/5000000000000000000000000000000000000000) (105774208866399862513611725633388443913/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1778
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1779
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (20899526541288558072314961919217397330729/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20899526541288558072314961919217397330729/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (20913920814891445681349879021020798020133/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20913920814891445681349879021020798020133/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (20906723678090001876832420470119097675431/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20906723678090001876832420470119097675431/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1779 BracketBatch0111.bracket1780 (20906723678090001876832420470119097675431/10000000000000000000000000000000000000000) (846911351246676917763549140168287907193/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1779 BracketBatch0111.bracket1780
  (20906723678090001876832420470119097675431/10000000000000000000000000000000000000000) (846911351246676917763549140168287907193/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1779
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1780
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (2091392081489144568134987902102079802013/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2091392081489144568134987902102079802013/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (20928337769098321391496483964363616664509/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20928337769098321391496483964363616664509/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (41842258583989767072846362985384414684639/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41842258583989767072846362985384414684639/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1780 BracketBatch0111.bracket1781 (41842258583989767072846362985384414684639/20000000000000000000000000000000000000000) (211907470196301688216371888698531989221/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1780 BracketBatch0111.bracket1781
  (41842258583989767072846362985384414684639/20000000000000000000000000000000000000000) (211907470196301688216371888698531989221/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1780
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1781
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (10464168884549160695748241982181808332253/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10464168884549160695748241982181808332253/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (20942777458335217570720461658443308994487/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20942777458335217570720461658443308994487/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (41871115227433538962216945622806925658993/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41871115227433538962216945622806925658993/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1781 BracketBatch0111.bracket1782 (41871115227433538962216945622806925658993/20000000000000000000000000000000000000000) (848349260954494897705849603311748855769/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1781 BracketBatch0111.bracket1782
  (41871115227433538962216945622806925658993/20000000000000000000000000000000000000000) (848349260954494897705849603311748855769/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1781
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1782
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (5235694364583804392680115414610827248621/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5235694364583804392680115414610827248621/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (5239309984298525386519628372119676627729/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5239309984298525386519628372119676627729/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (209500086977646595583994875734610077527/100000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (209500086977646595583994875734610077527/100000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1782 BracketBatch0111.bracket1783 (209500086977646595583994875734610077527/100000000000000000000000000000000000000) (849069493165033048275586567888648689529/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1782 BracketBatch0111.bracket1783
  (209500086977646595583994875734610077527/100000000000000000000000000000000000000) (849069493165033048275586567888648689529/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1782
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1783
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (20957239937194101546078513488478706510913/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20957239937194101546078513488478706510913/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0278.rows BesselBatch0278.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (2621465657554186766759136464937950701507/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2621465657554186766759136464937950701507/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (41928965197627595680151605207982312122969/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41928965197627595680151605207982312122969/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0222.rows ScalarLogs0222.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0111.bracket1783 BracketBatch0111.bracket1784 (41928965197627595680151605207982312122969/20000000000000000000000000000000000000000) (424895289415052404244942946655741942713/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0111.bracket1783 BracketBatch0111.bracket1784
  (41928965197627595680151605207982312122969/20000000000000000000000000000000000000000) (424895289415052404244942946655741942713/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1783
