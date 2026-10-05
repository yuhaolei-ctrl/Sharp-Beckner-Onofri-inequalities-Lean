module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0033
public import BecknerOnofri.EntropyScalarCertificate.Bessel0034
public import BecknerOnofri.EntropyScalarCertificate.Bessel0035
public import BecknerOnofri.EntropyScalarCertificate.Bessel0505
public import BecknerOnofri.EntropyScalarCertificate.Bessel0506
public import BecknerOnofri.EntropyScalarCertificate.Brackets0013
public import BecknerOnofri.EntropyScalarCertificate.Brackets0014
public import BecknerOnofri.EntropyScalarCertificate.Logs0027
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0216
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1001996571771990479909492985648699087663/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1001996571771990479909492985648699087663/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1004026870792924927885607942297788037379/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1004026870792924927885607942297788037379/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1003011721282457703897550463973243562521/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1003011721282457703897550463973243562521/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0216 BracketBatch0013.bracket0217 (1003011721282457703897550463973243562521/10000000000000000000000000000000000000000) (38435513504530689884414395092424879/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0216 BracketBatch0013.bracket0217
  (1003011721282457703897550463973243562521/10000000000000000000000000000000000000000) (38435513504530689884414395092424879/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0216
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0217
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (3921979964034862999553156024600734521/39062500000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3921979964034862999553156024600734521/39062500000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (503028646542266064290222267321647014629/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (503028646542266064290222267321647014629/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (1005042081938728528233026238470541033317/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1005042081938728528233026238470541033317/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0217 BracketBatch0013.bracket0218 (1005042081938728528233026238470541033317/10000000000000000000000000000000000000000) (77494239188375873299661883701329391/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0217 BracketBatch0013.bracket0218
  (1005042081938728528233026238470541033317/10000000000000000000000000000000000000000) (77494239188375873299661883701329391/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0217
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0218
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (201211458616906425716088906928658805851/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (201211458616906425716088906928658805851/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1008087838907493452525845747242372170023/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1008087838907493452525845747242372170023/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (1007072565996012790553145140942833099639/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1007072565996012790553145140942833099639/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0218 BracketBatch0013.bracket0219 (1007072565996012790553145140942833099639/10000000000000000000000000000000000000000) (78121221112295067164735526661691219/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0218 BracketBatch0013.bracket0219
  (1007072565996012790553145140942833099639/10000000000000000000000000000000000000000) (78121221112295067164735526661691219/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0218
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0219
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (50404391945374672626292287362118608501/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (50404391945374672626292287362118608501/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (505059254261287942377516354867039032319/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (505059254261287942377516354867039032319/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (1009103173715034668640439228488225117329/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1009103173715034668640439228488225117329/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0219 BracketBatch0013.bracket0220 (1009103173715034668640439228488225117329/10000000000000000000000000000000000000000) (78751988043993891826996745371146163/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0219 BracketBatch0013.bracket0220
  (1009103173715034668640439228488225117329/10000000000000000000000000000000000000000) (78751988043993891826996745371146163/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0219
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0220
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (202023701704515176951006541946815612927/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (202023701704515176951006541946815612927/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1012149302190632218863554897717808390317/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1012149302190632218863554897717808390317/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (252783476339151012952323450931485806869/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (252783476339151012952323450931485806869/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0220 BracketBatch0013.bracket0221 (252783476339151012952323450931485806869/2500000000000000000000000000000000000000) (79386555278414676318299876312876791/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0220 BracketBatch0013.bracket0221
  (252783476339151012952323450931485806869/2500000000000000000000000000000000000000) (79386555278414676318299876312876791/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0220
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0221
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (506074651095316109431777448858904195157/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (506074651095316109431777448858904195157/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (253545055043150312803684553494889220867/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (253545055043150312803684553494889220867/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (1013164761181616735039146555848682636891/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1013164761181616735039146555848682636891/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0221 BracketBatch0013.bracket0222 (1013164761181616735039146555848682636891/10000000000000000000000000000000000000000) (8002493814227474439503997329557209/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0221 BracketBatch0013.bracket0222
  (1013164761181616735039146555848682636891/10000000000000000000000000000000000000000) (8002493814227474439503997329557209/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0221
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0222
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (202836044034520250242947642795911376693/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (202836044034520250242947642795911376693/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1016211262729507975289988665266994512293/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1016211262729507975289988665266994512293/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (1015195741451054613252363439623275697879/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1015195741451054613252363439623275697879/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0222 BracketBatch0013.bracket0223 (1015195741451054613252363439623275697879/10000000000000000000000000000000000000000) (80667151994074027519746401539635529/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0222 BracketBatch0013.bracket0223
  (1015195741451054613252363439623275697879/10000000000000000000000000000000000000000) (80667151994074027519746401539635529/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0222
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0223
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0034.rows BesselBatch0034.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (101621126272950797528998866526699451229/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (101621126272950797528998866526699451229/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1018242430122463776184309797613173743137/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1018242430122463776184309797613173743137/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (2034453692851971751474298462880168255427/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2034453692851971751474298462880168255427/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0027.rows ScalarLogs0027.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0223 BracketBatch0014.bracket0224 (2034453692851971751474298462880168255427/20000000000000000000000000000000000000000) (81313212224102694679077298466933019/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0223 BracketBatch0014.bracket0224
  (2034453692851971751474298462880168255427/20000000000000000000000000000000000000000) (81313212224102694679077298466933019/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0223
