import BecknerOnofri.EntropyScalarCertificate.Bessel0290
import BecknerOnofri.EntropyScalarCertificate.Bessel0291
import BecknerOnofri.EntropyScalarCertificate.Bessel0633
import BecknerOnofri.EntropyScalarCertificate.Bessel0634
import BecknerOnofri.EntropyScalarCertificate.Brackets0116
import BecknerOnofri.EntropyScalarCertificate.Logs0232
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1856
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (12046588079423191975340902125466462614401/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12046588079423191975340902125466462614401/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (24192894622058544414538089960781411692373/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (24192894622058544414538089960781411692373/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (1931442831236197134608795768468573476847/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1931442831236197134608795768468573476847/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1856 BracketBatch0116.bracket1857 (1931442831236197134608795768468573476847/800000000000000000000000000000000000000) (199242555343766219594212787905725376813/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1856 BracketBatch0116.bracket1857
  (1931442831236197134608795768468573476847/800000000000000000000000000000000000000) (199242555343766219594212787905725376813/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1856
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1857
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (2419289462205854441453808996078141169237/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2419289462205854441453808996078141169237/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (12146771407153056389187413652129469522397/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12146771407153056389187413652129469522397/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (12121609359091164298228229316260087684291/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12121609359091164298228229316260087684291/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1857 BracketBatch0116.bracket1858 (12121609359091164298228229316260087684291/5000000000000000000000000000000000000000) (3127310775789479999572104741788765541/31250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1857 BracketBatch0116.bracket1858
  (12121609359091164298228229316260087684291/5000000000000000000000000000000000000000) (3127310775789479999572104741788765541/31250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1857
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1858
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (24293542814306112778374827304258939044791/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (24293542814306112778374827304258939044791/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (24395133626350276500489414890381084736041/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (24395133626350276500489414890381084736041/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (1521521138770512164964507568582500743151/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1521521138770512164964507568582500743151/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1858 BracketBatch0116.bracket1859 (1521521138770512164964507568582500743151/625000000000000000000000000000000000000) (502647755925047916047469527827876906461/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1858 BracketBatch0116.bracket1859
  (1521521138770512164964507568582500743151/625000000000000000000000000000000000000) (502647755925047916047469527827876906461/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1858
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1859
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (12197566813175138250244707445190542368019/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12197566813175138250244707445190542368019/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (6124420045105080191199798089644949510597/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6124420045105080191199798089644949510597/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (24446406903385298632644303624480441389213/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (24446406903385298632644303624480441389213/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1859 BracketBatch0116.bracket1860 (24446406903385298632644303624480441389213/10000000000000000000000000000000000000000) (1009881229478609305597392562404507774507/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1859 BracketBatch0116.bracket1860
  (24446406903385298632644303624480441389213/10000000000000000000000000000000000000000) (1009881229478609305597392562404507774507/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1859
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1860
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (4899536036084064152959838471715959608477/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4899536036084064152959838471715959608477/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (24601195835477160248328710136678778834847/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (24601195835477160248328710136678778834847/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (3068679750993592563320493905953661054827/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3068679750993592563320493905953661054827/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1860 BracketBatch0116.bracket1861 (3068679750993592563320493905953661054827/1250000000000000000000000000000000000000) (1014496866066087310788120438189062974251/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1860 BracketBatch0116.bracket1861
  (3068679750993592563320493905953661054827/1250000000000000000000000000000000000000) (1014496866066087310788120438189062974251/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1860
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1861
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (6150298958869290062082177534169694708711/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6150298958869290062082177534169694708711/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (24705694192625362069603333861903247714747/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (24705694192625362069603333861903247714747/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (49306890028102522317932043998582026549591/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (49306890028102522317932043998582026549591/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1861 BracketBatch0116.bracket1862 (49306890028102522317932043998582026549591/20000000000000000000000000000000000000000) (127392836193967806492639869395108192219/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1861 BracketBatch0116.bracket1862
  (49306890028102522317932043998582026549591/20000000000000000000000000000000000000000) (127392836193967806492639869395108192219/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1861
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1862
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (3088211774078170258700416732737905964343/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3088211774078170258700416732737905964343/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (24811189100678610132224454492742038400759/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (24811189100678610132224454492742038400759/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (49516883293303972201827788354645286115503/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (49516883293303972201827788354645286115503/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1862 BracketBatch0116.bracket1863 (49516883293303972201827788354645286115503/20000000000000000000000000000000000000000) (1023818970938279470896440901219652805827/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1862 BracketBatch0116.bracket1863
  (49516883293303972201827788354645286115503/20000000000000000000000000000000000000000) (1023818970938279470896440901219652805827/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1862
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1863
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (6202797275169652533056113623185509600189/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6202797275169652533056113623185509600189/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (3114711832735468294662514100878209465241/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3114711832735468294662514100878209465241/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (12432220940640589122381141824941928530671/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12432220940640589122381141824941928530671/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0232.rows ScalarLogs0232.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1863 BracketBatch0116.bracket1864 (12432220940640589122381141824941928530671/5000000000000000000000000000000000000000) (128565748043193566562101501013864331679/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1863 BracketBatch0116.bracket1864
  (12432220940640589122381141824941928530671/5000000000000000000000000000000000000000) (128565748043193566562101501013864331679/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1863
