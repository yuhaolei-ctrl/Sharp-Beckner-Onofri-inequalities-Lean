import BecknerOnofri.EntropyScalarCertificate.Bessel0196
import BecknerOnofri.EntropyScalarCertificate.Bessel0197
import BecknerOnofri.EntropyScalarCertificate.Bessel0587
import BecknerOnofri.EntropyScalarCertificate.Brackets0078
import BecknerOnofri.EntropyScalarCertificate.Brackets0079
import BecknerOnofri.EntropyScalarCertificate.Logs0157
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1256
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (11369584588723698084610598958146996403739/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11369584588723698084610598958146996403739/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (5703965070719595309119388839203700461697/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5703965070719595309119388839203700461697/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (22777514730162888702849376636554397327133/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22777514730162888702849376636554397327133/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1256 BracketBatch0078.bracket1257 (22777514730162888702849376636554397327133/20000000000000000000000000000000000000000) (318288705868322130894198637208122226561/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1256 BracketBatch0078.bracket1257
  (22777514730162888702849376636554397327133/20000000000000000000000000000000000000000) (318288705868322130894198637208122226561/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1256
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1257
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (11407930141439190618238777678407400923391/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11407930141439190618238777678407400923391/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (11446519591319989033037047224477709976259/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11446519591319989033037047224477709976259/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (457088994655183593025516498057702217993/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (457088994655183593025516498057702217993/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1257 BracketBatch0078.bracket1258 (457088994655183593025516498057702217993/400000000000000000000000000000000000000) (320479809333974473708791937471556830949/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1257 BracketBatch0078.bracket1258
  (457088994655183593025516498057702217993/400000000000000000000000000000000000000) (320479809333974473708791937471556830949/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1257
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1258
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (178851868614374828641203862882464218379/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (178851868614374828641203862882464218379/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2871338975763324385118517520345991731013/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2871338975763324385118517520345991731013/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (5732968873593321643377779326465419225077/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5732968873593321643377779326465419225077/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1258 BracketBatch0078.bracket1259 (5732968873593321643377779326465419225077/5000000000000000000000000000000000000000) (2520987072604988033775294283889592643/78125000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1258 BracketBatch0078.bracket1259
  (5732968873593321643377779326465419225077/5000000000000000000000000000000000000000) (2520987072604988033775294283889592643/78125000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1258
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1259
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (11485355903053297540474070081383966924049/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11485355903053297540474070081383966924049/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (576222104529618936475583389582918523137/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (576222104529618936475583389582918523137/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (23009797993645676269985737873042337386789/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23009797993645676269985737873042337386789/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1259 BracketBatch0078.bracket1260 (23009797993645676269985737873042337386789/20000000000000000000000000000000000000000) (324908457541802084103459410106248235773/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1259 BracketBatch0078.bracket1260
  (23009797993645676269985737873042337386789/20000000000000000000000000000000000000000) (324908457541802084103459410106248235773/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1259
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1260
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0196.rows BesselBatch0196.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (11524442090592378729511667791658370462737/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11524442090592378729511667791658370462737/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (11563781218180095521363298326108300057627/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11563781218180095521363298326108300057627/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (5772055827193118562718741529441667630091/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5772055827193118562718741529441667630091/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1260 BracketBatch0078.bracket1261 (5772055827193118562718741529441667630091/5000000000000000000000000000000000000000) (327146291901776294822092471577725752391/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1260 BracketBatch0078.bracket1261
  (5772055827193118562718741529441667630091/5000000000000000000000000000000000000000) (327146291901776294822092471577725752391/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1260
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1261
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1445472652272511940170412290763537507203/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1445472652272511940170412290763537507203/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1160337640139758797048702911609814159023/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1160337640139758797048702911609814159023/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (11583578809788841745925163721103220823927/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11583578809788841745925163721103220823927/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1261 BracketBatch0078.bracket1262 (11583578809788841745925163721103220823927/10000000000000000000000000000000000000000) (329399996261184449738439127918418356549/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1261 BracketBatch0078.bracket1262
  (11583578809788841745925163721103220823927/10000000000000000000000000000000000000000) (329399996261184449738439127918418356549/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1261
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1262
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (11603376401397587970487029116098141590227/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11603376401397587970487029116098141590227/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (5821615404119394522417315295228253453861/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5821615404119394522417315295228253453861/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (23246607209636377015321659706554648497949/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23246607209636377015321659706554648497949/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1262 BracketBatch0078.bracket1263 (23246607209636377015321659706554648497949/20000000000000000000000000000000000000000) (331669720611241647768931826636591943129/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1262 BracketBatch0078.bracket1263
  (23246607209636377015321659706554648497949/20000000000000000000000000000000000000000) (331669720611241647768931826636591943129/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1262
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1263
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (11643230808238789044834630590456506907719/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11643230808238789044834630590456506907719/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0197.rows BesselBatch0197.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (5841673830105752734906350713103285485513/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5841673830105752734906350713103285485513/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0587.rows BesselBatch0587.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (4665315693690058902929466403332615575749/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4665315693690058902929466403332615575749/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0157.rows ScalarLogs0157.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0078.bracket1263 BracketBatch0079.bracket1264 (4665315693690058902929466403332615575749/4000000000000000000000000000000000000000) (166977808542820842086919098763012379819/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0078.bracket1263 BracketBatch0079.bracket1264
  (4665315693690058902929466403332615575749/4000000000000000000000000000000000000000) (166977808542820842086919098763012379819/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1263
