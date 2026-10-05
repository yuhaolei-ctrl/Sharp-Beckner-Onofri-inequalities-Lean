import BecknerOnofri.EntropyScalarCertificate.Bessel0447
import BecknerOnofri.EntropyScalarCertificate.Bessel0448
import BecknerOnofri.EntropyScalarCertificate.Bessel0712
import BecknerOnofri.EntropyScalarCertificate.Bessel0713
import BecknerOnofri.EntropyScalarCertificate.Brackets0179
import BecknerOnofri.EntropyScalarCertificate.Logs0358
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2864
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (134855072793205003349091411942685068384087/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (134855072793205003349091411942685068384087/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (270291993218870911304207549916940743372859/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (270291993218870911304207549916940743372859/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (540002138805280918002390373802310880141033/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (540002138805280918002390373802310880141033/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2864 BracketBatch0179.bracket2865 (540002138805280918002390373802310880141033/5000000000000000000000000000000000000000) (6230331520149829344667537615126542334639/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2864 BracketBatch0179.bracket2865
  (540002138805280918002390373802310880141033/5000000000000000000000000000000000000000) (6230331520149829344667537615126542334639/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2864
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2865
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1081167972875483645216830199667762973491433/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1081167972875483645216830199667762973491433/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1083505438730307608871592276145286127073979/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1083505438730307608871592276145286127073979/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (541168352901447813522105618953262275141353/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (541168352901447813522105618953262275141353/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2865 BracketBatch0179.bracket2866 (541168352901447813522105618953262275141353/5000000000000000000000000000000000000000) (1558412588439447226815272457043861581377/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2865 BracketBatch0179.bracket2866
  (541168352901447813522105618953262275141353/5000000000000000000000000000000000000000) (1558412588439447226815272457043861581377/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2865
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2866
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (135438179841288451108949034518160765884247/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (135438179841288451108949034518160765884247/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1085853045476216501574986656111672726832387/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1085853045476216501574986656111672726832387/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (2169358484206524110446578932256958853906363/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2169358484206524110446578932256958853906363/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2866 BracketBatch0179.bracket2867 (2169358484206524110446578932256958853906363/20000000000000000000000000000000000000000) (3118488200219489410428163592386278036319/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2866 BracketBatch0179.bracket2867
  (2169358484206524110446578932256958853906363/20000000000000000000000000000000000000000) (3118488200219489410428163592386278036319/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2866
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2867
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (4241613458891470709277291625436221589189/39062500000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4241613458891470709277291625436221589189/39062500000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (272052714812363736781026967641219895548241/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (272052714812363736781026967641219895548241/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (543515976181417862174773631669138077256337/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (543515976181417862174773631669138077256337/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2867 BracketBatch0179.bracket2868 (543515976181417862174773631669138077256337/5000000000000000000000000000000000000000) (1560077422479281875490472495962214997087/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2867 BracketBatch0179.bracket2868
  (543515976181417862174773631669138077256337/5000000000000000000000000000000000000000) (1560077422479281875490472495962214997087/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2867
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2868
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1088210859249454947124107870564879582192961/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1088210859249454947124107870564879582192961/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (545289473381309142555963345612096277210739/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (545289473381309142555963345612096277210739/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (2178789806012073232236034561789072136614439/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2178789806012073232236034561789072136614439/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2868 BracketBatch0179.bracket2869 (2178789806012073232236034561789072136614439/20000000000000000000000000000000000000000) (780456281511527506973213603491443669501/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2868 BracketBatch0179.bracket2869
  (2178789806012073232236034561789072136614439/20000000000000000000000000000000000000000) (780456281511527506973213603491443669501/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2868
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2869
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (43623157870504731404477067648967702176859/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (43623157870504731404477067648967702176859/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1092957375310944609309325919790079553290217/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1092957375310944609309325919790079553290217/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (545884080518390723605313152753568026927923/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (545884080518390723605313152753568026927923/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2869 BracketBatch0179.bracket2870 (545884080518390723605313152753568026927923/5000000000000000000000000000000000000000) (780874764630225905370582351531463493033/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2869 BracketBatch0179.bracket2870
  (545884080518390723605313152753568026927923/5000000000000000000000000000000000000000) (780874764630225905370582351531463493033/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2869
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2870
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (546478687655472304654662959895039776645107/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (546478687655472304654662959895039776645107/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1095346212778689414866156343630137355841367/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1095346212778689414866156343630137355841367/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (2188303588089634024175482263420216909131581/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2188303588089634024175482263420216909131581/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2870 BracketBatch0179.bracket2871 (2188303588089634024175482263420216909131581/20000000000000000000000000000000000000000) (125007066300446506415079340195058049949/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2870 BracketBatch0179.bracket2871
  (2188303588089634024175482263420216909131581/20000000000000000000000000000000000000000) (125007066300446506415079340195058049949/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2870
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2871
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (273836553194672353716539085907534338960341/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (273836553194672353716539085907534338960341/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (219549105529116824489829738755699047542231/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (219549105529116824489829738755699047542231/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (2193091740424273537315305037408632593552519/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2193091740424273537315305037408632593552519/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0358.rows ScalarLogs0358.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2871 BracketBatch0179.bracket2872 (2193091740424273537315305037408632593552519/20000000000000000000000000000000000000000) (6253715876470426842479549318971634212037/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2871 BracketBatch0179.bracket2872
  (2193091740424273537315305037408632593552519/20000000000000000000000000000000000000000) (6253715876470426842479549318971634212037/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2871
