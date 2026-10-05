import BecknerOnofri.EntropyScalarCertificate.Bessel0213
import BecknerOnofri.EntropyScalarCertificate.Bessel0214
import BecknerOnofri.EntropyScalarCertificate.Bessel0215
import BecknerOnofri.EntropyScalarCertificate.Bessel0595
import BecknerOnofri.EntropyScalarCertificate.Bessel0596
import BecknerOnofri.EntropyScalarCertificate.Brackets0085
import BecknerOnofri.EntropyScalarCertificate.Brackets0086
import BecknerOnofri.EntropyScalarCertificate.Logs0171
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1368
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (16098416806468216108032887686149620501481/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16098416806468216108032887686149620501481/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (3227624464868851460427689742732974497761/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3227624464868851460427689742732974497761/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (16118269565406236705085668199907246495143/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16118269565406236705085668199907246495143/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1368 BracketBatch0085.bracket1369 (16118269565406236705085668199907246495143/10000000000000000000000000000000000000000) (295272868841485599688005701330247311867/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1368 BracketBatch0085.bracket1369
  (16118269565406236705085668199907246495143/10000000000000000000000000000000000000000) (295272868841485599688005701330247311867/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1368
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1369
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (8069061162172128651069224356832436244401/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8069061162172128651069224356832436244401/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1617804940712035575733098836132276011907/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1617804940712035575733098836132276011907/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (252470091652067289527104977148340879749/156250000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (252470091652067289527104977148340879749/156250000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1369 BracketBatch0085.bracket1370 (252470091652067289527104977148340879749/156250000000000000000000000000000000000) (74095416900937024389268862468473898699/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1369 BracketBatch0085.bracket1370
  (252470091652067289527104977148340879749/156250000000000000000000000000000000000) (74095416900937024389268862468473898699/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1369
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1370
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (16178049407120355757330988361322760119067/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16178049407120355757330988361322760119067/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (50681875353467929575283280987563210087/31250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (50681875353467929575283280987563210087/31250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (32396249520230093221421638277342987346907/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (32396249520230093221421638277342987346907/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1370 BracketBatch0085.bracket1371 (32396249520230093221421638277342987346907/20000000000000000000000000000000000000000) (148747886744362570929037100014603811197/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1370 BracketBatch0085.bracket1371
  (32396249520230093221421638277342987346907/20000000000000000000000000000000000000000) (148747886744362570929037100014603811197/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1370
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1371
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (16218200113109737464090649916020227227837/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16218200113109737464090649916020227227837/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (16258576525453658216553866452955863808127/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16258576525453658216553866452955863808127/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (8119194159640848920161129092244022758991/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8119194159640848920161129092244022758991/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1371 BracketBatch0085.bracket1372 (8119194159640848920161129092244022758991/5000000000000000000000000000000000000000) (597230448522781710001436749847258813169/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1371 BracketBatch0085.bracket1372
  (8119194159640848920161129092244022758991/5000000000000000000000000000000000000000) (597230448522781710001436749847258813169/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1371
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1372
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (4064644131363414554138466613238965952031/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4064644131363414554138466613238965952031/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (8149590376240125316033748205006573786187/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8149590376240125316033748205006573786187/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (16278878638966954424310681431484505690249/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16278878638966954424310681431484505690249/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1372 BracketBatch0085.bracket1373 (16278878638966954424310681431484505690249/10000000000000000000000000000000000000000) (599480116073241220000871301582276027467/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1372 BracketBatch0085.bracket1373
  (16278878638966954424310681431484505690249/10000000000000000000000000000000000000000) (599480116073241220000871301582276027467/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1372
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1373
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (16299180752480250632067496410013147572371/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16299180752480250632067496410013147572371/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (8170007464034681195133201740663397554127/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8170007464034681195133201740663397554127/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (52222713088879380835734239826143908289/32000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (52222713088879380835734239826143908289/32000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1373 BracketBatch0085.bracket1374 (52222713088879380835734239826143908289/32000000000000000000000000000000000000) (601740626565367963190244518367859151817/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1373 BracketBatch0085.bracket1374
  (52222713088879380835734239826143908289/32000000000000000000000000000000000000) (601740626565367963190244518367859151817/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1373
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1374
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (16340014928069362390266403481326795108251/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16340014928069362390266403481326795108251/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (819054060601175024267980239663250336571/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (819054060601175024267980239663250336571/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (32721096140092862875626008274591801839671/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (32721096140092862875626008274591801839671/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1374 BracketBatch0085.bracket1375 (32721096140092862875626008274591801839671/20000000000000000000000000000000000000000) (302006028824770491597705988381106850763/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1374 BracketBatch0085.bracket1375
  (32721096140092862875626008274591801839671/20000000000000000000000000000000000000000) (302006028824770491597705988381106850763/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1374
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1375
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0214.rows BesselBatch0214.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (16381081212023500485359604793265006731417/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16381081212023500485359604793265006731417/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0215.rows BesselBatch0215.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (16422381790444998852602272649795773993731/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16422381790444998852602272649795773993731/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0596.rows BesselBatch0596.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (8200865750617124834490469360765195181287/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8200865750617124834490469360765195181287/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0171.rows ScalarLogs0171.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1375 BracketBatch0086.bracket1376 (8200865750617124834490469360765195181287/5000000000000000000000000000000000000000) (303147243848548422006077450538858347821/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1375 BracketBatch0086.bracket1376
  (8200865750617124834490469360765195181287/5000000000000000000000000000000000000000) (303147243848548422006077450538858347821/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1375
