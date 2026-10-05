import BecknerOnofri.EntropyScalarCertificate.Bessel0442
import BecknerOnofri.EntropyScalarCertificate.Bessel0443
import BecknerOnofri.EntropyScalarCertificate.Bessel0710
import BecknerOnofri.EntropyScalarCertificate.Brackets0177
import BecknerOnofri.EntropyScalarCertificate.Logs0354
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2832
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1009319195226862202004955087851540909633269/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1009319195226862202004955087851540909633269/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (126419459963260483855181555672789867797849/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (126419459963260483855181555672789867797849/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (2020674874932946072846407533233859852016061/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2020674874932946072846407533233859852016061/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2832 BracketBatch0177.bracket2833 (2020674874932946072846407533233859852016061/20000000000000000000000000000000000000000) (612776824013681491897818086782426423633/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2832 BracketBatch0177.bracket2833
  (2020674874932946072846407533233859852016061/20000000000000000000000000000000000000000) (612776824013681491897818086782426423633/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2832
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2833
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1011355679706083870841452445382318942382789/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1011355679706083870841452445382318942382789/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1013400409100412821874679095070929566787909/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1013400409100412821874679095070929566787909/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (1012378044403248346358065770226624254585349/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1012378044403248346358065770226624254585349/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2833 BracketBatch0177.bracket2834 (1012378044403248346358065770226624254585349/10000000000000000000000000000000000000000) (6130870959439860366070783378303239546119/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2833 BracketBatch0177.bracket2834
  (1012378044403248346358065770226624254585349/10000000000000000000000000000000000000000) (6130870959439860366070783378303239546119/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2833
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2834
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (506700204550206410937339547535464783393953/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (506700204550206410937339547535464783393953/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (203090686716348955922856797778547432983693/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (203090686716348955922856797778547432983693/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (2028853842682157601488963083963666731706371/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2028853842682157601488963083963666731706371/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2834 BracketBatch0177.bracket2835 (2028853842682157601488963083963666731706371/20000000000000000000000000000000000000000) (1533495006606460388328083045147066910159/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2834 BracketBatch0177.bracket2835
  (2028853842682157601488963083963666731706371/20000000000000000000000000000000000000000) (1533495006606460388328083045147066910159/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2834
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2835
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (507726716790872389807141994446368582459231/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (507726716790872389807141994446368582459231/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1017514803729877059938592535043614994465941/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1017514803729877059938592535043614994465941/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (2032968237311621839552876523936352159384403/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2032968237311621839552876523936352159384403/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2835 BracketBatch0177.bracket2836 (2032968237311621839552876523936352159384403/20000000000000000000000000000000000000000) (3068547732904314882084808227448908330781/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2835 BracketBatch0177.bracket2836
  (2032968237311621839552876523936352159384403/20000000000000000000000000000000000000000) (3068547732904314882084808227448908330781/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2835
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2836
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (508757401864938529969296267521807497232969/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (508757401864938529969296267521807497232969/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (509792285268331177060374937224188714585577/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (509792285268331177060374937224188714585577/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (509274843566634853514835602372998105909273/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (509274843566634853514835602372998105909273/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2836 BracketBatch0177.bracket2837 (509274843566634853514835602372998105909273/5000000000000000000000000000000000000000) (767527162805214987802568867068762558517/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2836 BracketBatch0177.bracket2837
  (509274843566634853514835602372998105909273/5000000000000000000000000000000000000000) (767527162805214987802568867068762558517/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2836
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2837
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1019584570536662354120749874448377429171151/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1019584570536662354120749874448377429171151/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (8173302283281707004131270172303453714247/80000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8173302283281707004131270172303453714247/80000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (1020623677973437864818579322993154571726013/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1020623677973437864818579322993154571726013/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2837 BracketBatch0177.bracket2838 (1020623677973437864818579322993154571726013/10000000000000000000000000000000000000000) (153583639032980851134331911794164381743/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2837 BracketBatch0177.bracket2838
  (1020623677973437864818579322993154571726013/10000000000000000000000000000000000000000) (153583639032980851134331911794164381743/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2837
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2838
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (127707848176276671939551096442241464285109/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (127707848176276671939551096442241464285109/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1023749500179159097008321653650020328795491/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1023749500179159097008321653650020328795491/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (2045412285589372472524730425187952043076363/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2045412285589372472524730425187952043076363/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2838 BracketBatch0177.bracket2839 (2045412285589372472524730425187952043076363/20000000000000000000000000000000000000000) (3073240133788466677066866227138245854029/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2838 BracketBatch0177.bracket2839
  (2045412285589372472524730425187952043076363/20000000000000000000000000000000000000000) (3073240133788466677066866227138245854029/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2838
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2839
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (31992171880598721781510051676563135274859/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31992171880598721781510051676563135274859/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0443.rows BesselBatch0443.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (512922383548476659619592916985809950340779/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (512922383548476659619592916985809950340779/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (1024797133638056208123753743810820114738523/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1024797133638056208123753743810820114738523/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0354.rows ScalarLogs0354.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0177.bracket2839 BracketBatch0177.bracket2840 (1024797133638056208123753743810820114738523/10000000000000000000000000000000000000000) (6149621446493238413089288655906530518883/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0177.bracket2839 BracketBatch0177.bracket2840
  (1024797133638056208123753743810820114738523/10000000000000000000000000000000000000000) (6149621446493238413089288655906530518883/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2839
