module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0268
public import BecknerOnofri.EntropyScalarCertificate.Bessel0269
public import BecknerOnofri.EntropyScalarCertificate.Bessel0270
public import BecknerOnofri.EntropyScalarCertificate.Bessel0623
public import BecknerOnofri.EntropyScalarCertificate.Brackets0107
public import BecknerOnofri.EntropyScalarCertificate.Brackets0108
public import BecknerOnofri.EntropyScalarCertificate.Logs0215
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1720
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (4017707738897248927245860959945959631931/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4017707738897248927245860959945959631931/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (10050842750426163444497426853435177573367/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10050842750426163444497426853435177573367/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (40190224195338571525224158506600153306389/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40190224195338571525224158506600153306389/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1720 BracketBatch0107.bracket1721 (40190224195338571525224158506600153306389/20000000000000000000000000000000000000000) (161194894674498960804979531088433362893/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1720 BracketBatch0107.bracket1721
  (40190224195338571525224158506600153306389/20000000000000000000000000000000000000000) (161194894674498960804979531088433362893/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1720
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1721
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (20101685500852326888994853706870355146731/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20101685500852326888994853706870355146731/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (20114852049601419726673468083414502555013/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20114852049601419726673468083414502555013/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (2513533596903359163479270111892803606359/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2513533596903359163479270111892803606359/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1721 BracketBatch0107.bracket1722 (2513533596903359163479270111892803606359/1250000000000000000000000000000000000000) (806645215362941002200907553538192658153/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1721 BracketBatch0107.bracket1722
  (2513533596903359163479270111892803606359/1250000000000000000000000000000000000000) (806645215362941002200907553538192658153/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1721
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1722
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (2011485204960141972667346808341450255501/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2011485204960141972667346808341450255501/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (629001199574085078523532727529325563843/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (629001199574085078523532727529325563843/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (20121445217986071119713257682176460298993/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20121445217986071119713257682176460298993/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1722 BracketBatch0107.bracket1723 (20121445217986071119713257682176460298993/10000000000000000000000000000000000000000) (201829182369625016900509087833192651803/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1722 BracketBatch0107.bracket1723
  (20121445217986071119713257682176460298993/10000000000000000000000000000000000000000) (201829182369625016900509087833192651803/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1722
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1723
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (20128038386370722512753047280938418042973/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20128038386370722512753047280938418042973/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (5035311139232839627083660130281038863767/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5035311139232839627083660130281038863767/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (40269282943302081021087687802062573498041/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40269282943302081021087687802062573498041/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1723 BracketBatch0107.bracket1724 (40269282943302081021087687802062573498041/20000000000000000000000000000000000000000) (807989016975972015359682003323584133943/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1723 BracketBatch0107.bracket1724
  (40269282943302081021087687802062573498041/20000000000000000000000000000000000000000) (807989016975972015359682003323584133943/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1723
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1724
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (4028248911386271701666928104224831091013/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4028248911386271701666928104224831091013/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (4030894121437770273983711882170642086709/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4030894121437770273983711882170642086709/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (4029571516412020987825319993197736588861/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4029571516412020987825319993197736588861/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1724 BracketBatch0107.bracket1725 (4029571516412020987825319993197736588861/2000000000000000000000000000000000000000) (101082759889324221945264119601999227317/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1724 BracketBatch0107.bracket1725
  (4029571516412020987825319993197736588861/2000000000000000000000000000000000000000) (101082759889324221945264119601999227317/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1724
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1725
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (10077235303594425684959279705426605216771/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10077235303594425684959279705426605216771/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (10083858291591801850592710794123503834999/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10083858291591801850592710794123503834999/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (2016109359518622753555199049955010905177/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2016109359518622753555199049955010905177/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1725 BracketBatch0107.bracket1726 (2016109359518622753555199049955010905177/1000000000000000000000000000000000000000) (202333979289011150589351319242774941789/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1725 BracketBatch0107.bracket1726
  (2016109359518622753555199049955010905177/1000000000000000000000000000000000000000) (202333979289011150589351319242774941789/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1725
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1726
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (4033543316636720740237084317649401533999/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4033543316636720740237084317649401533999/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (2522622816386422208693446502289346032411/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2522622816386422208693446502289346032411/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (40348699114274981370732993606561775929283/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40348699114274981370732993606561775929283/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1726 BracketBatch0107.bracket1727 (40348699114274981370732993606561775929283/20000000000000000000000000000000000000000) (810010532364451501537243390498631658043/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1726 BracketBatch0107.bracket1727
  (40348699114274981370732993606561775929283/20000000000000000000000000000000000000000) (810010532364451501537243390498631658043/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1726
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1727
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0269.rows BesselBatch0269.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (4036196506218275533909514403662953651857/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4036196506218275533909514403662953651857/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (20194268497223777698313347231713179314687/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20194268497223777698313347231713179314687/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (10093812757078788841965229812506986893493/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10093812757078788841965229812506986893493/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0215.rows ScalarLogs0215.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1727 BracketBatch0108.bracket1728 (10093812757078788841965229812506986893493/5000000000000000000000000000000000000000) (810685926006394676718531291617600222491/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1727 BracketBatch0108.bracket1728
  (10093812757078788841965229812506986893493/5000000000000000000000000000000000000000) (810685926006394676718531291617600222491/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1727
