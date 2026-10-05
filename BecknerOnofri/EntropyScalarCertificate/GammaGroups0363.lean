import BecknerOnofri.EntropyScalarCertificate.Bessel0453
import BecknerOnofri.EntropyScalarCertificate.Bessel0454
import BecknerOnofri.EntropyScalarCertificate.Bessel0455
import BecknerOnofri.EntropyScalarCertificate.Bessel0715
import BecknerOnofri.EntropyScalarCertificate.Bessel0716
import BecknerOnofri.EntropyScalarCertificate.Brackets0181
import BecknerOnofri.EntropyScalarCertificate.Brackets0182
import BecknerOnofri.EntropyScalarCertificate.Logs0363
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2904
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (118049927925337210353265199868885162095589/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (118049927925337210353265199868885162095589/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (147910885460722164013197197515820493112727/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (147910885460722164013197197515820493112727/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1181893181469574707819114789407707782928853/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1181893181469574707819114789407707782928853/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2904 BracketBatch0181.bracket2905 (1181893181469574707819114789407707782928853/10000000000000000000000000000000000000000) (6369020673785988673922498476171930202461/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2904 BracketBatch0181.bracket2905
  (1181893181469574707819114789407707782928853/10000000000000000000000000000000000000000) (6369020673785988673922498476171930202461/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2904
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2905
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0453.rows BesselBatch0453.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (1183287083685777312105577580126563944901813/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1183287083685777312105577580126563944901813/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1186088100506611359023797113281662387604303/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1186088100506611359023797113281662387604303/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (592343796048097167782343673352056583126529/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (592343796048097167782343673352056583126529/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2905 BracketBatch0181.bracket2906 (592343796048097167782343673352056583126529/5000000000000000000000000000000000000000) (6372653029362858323696818848572008618559/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2905 BracketBatch0181.bracket2906
  (592343796048097167782343673352056583126529/5000000000000000000000000000000000000000) (6372653029362858323696818848572008618559/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2905
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2906
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (11860881005066113590237971132816623876043/100000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11860881005066113590237971132816623876043/100000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (74306401491619301909735411329531313129171/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (74306401491619301909735411329531313129171/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0715.rows BesselBatch0715.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (593747631093130047394890923638540849417759/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (593747631093130047394890923638540849417759/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2906 BracketBatch0181.bracket2907 (593747631093130047394890923638540849417759/5000000000000000000000000000000000000000) (6376293937676580836719955022397361546567/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2906 BracketBatch0181.bracket2907
  (593747631093130047394890923638540849417759/5000000000000000000000000000000000000000) (6376293937676580836719955022397361546567/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2906
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2907
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (1188902423865908830555766581272501010066733/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1188902423865908830555766581272501010066733/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (29793253720259282729005752570779867876917/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (29793253720259282729005752570779867876917/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (2380632572676280139715996684103695725143413/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2380632572676280139715996684103695725143413/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2907 BracketBatch0181.bracket2908 (2380632572676280139715996684103695725143413/20000000000000000000000000000000000000000) (6379943436626250530554667980426748059351/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2907 BracketBatch0181.bracket2908
  (2380632572676280139715996684103695725143413/20000000000000000000000000000000000000000) (6379943436626250530554667980426748059351/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2907
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2908
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1191730148810371309160230102831194715076677/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1191730148810371309160230102831194715076677/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1194571371294067456972960987736255358792919/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1194571371294067456972960987736255358792919/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (596575380026109691533297772641862518467399/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (596575380026109691533297772641862518467399/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2908 BracketBatch0181.bracket2909 (596575380026109691533297772641862518467399/5000000000000000000000000000000000000000) (6383601564348697347478993952151190680687/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2908 BracketBatch0181.bracket2909
  (596575380026109691533297772641862518467399/5000000000000000000000000000000000000000) (6383601564348697347478993952151190680687/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2908
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2909
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (298642842823516864243240246934063839698229/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (298642842823516864243240246934063839698229/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1197426188189286689008623480380129113877491/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1197426188189286689008623480380129113877491/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (2391997559483354145981584468116384472670407/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2391997559483354145981584468116384472670407/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2909 BracketBatch0181.bracket2910 (2391997559483354145981584468116384472670407/20000000000000000000000000000000000000000) (159681708980507278176103339390137022861/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2909 BracketBatch0181.bracket2910
  (2391997559483354145981584468116384472670407/20000000000000000000000000000000000000000) (159681708980507278176103339390137022861/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2909
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2910
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (74839136761830418063038967523758069617343/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (74839136761830418063038967523758069617343/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1200294697297549014322373524365169278769599/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1200294697297549014322373524365169278769599/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (2397720885486835703330997004745298392647087/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2397720885486835703330997004745298392647087/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2910 BracketBatch0181.bracket2911 (2397720885486835703330997004745298392647087/20000000000000000000000000000000000000000) (319547192992937989304003991827623366307/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2910 BracketBatch0181.bracket2911
  (2397720885486835703330997004745298392647087/20000000000000000000000000000000000000000) (319547192992937989304003991827623366307/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2910
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2911
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0454.rows BesselBatch0454.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (300073674324387253580593381091292319692399/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (300073674324387253580593381091292319692399/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0455.rows BesselBatch0455.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1203176997360773672957444156654146973043653/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1203176997360773672957444156654146973043653/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0716.rows BesselBatch0716.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (2403471694658322687279817681019316251813249/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2403471694658322687279817681019316251813249/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0363.rows ScalarLogs0363.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0181.bracket2911 BracketBatch0182.bracket2912 (2403471694658322687279817681019316251813249/20000000000000000000000000000000000000000) (6394628105125021460861969824200081888819/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0181.bracket2911 BracketBatch0182.bracket2912
  (2403471694658322687279817681019316251813249/20000000000000000000000000000000000000000) (6394628105125021460861969824200081888819/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2911
