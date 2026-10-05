import BecknerOnofri.EntropyScalarCertificate.Bessel0096
import BecknerOnofri.EntropyScalarCertificate.Bessel0097
import BecknerOnofri.EntropyScalarCertificate.Bessel0537
import BecknerOnofri.EntropyScalarCertificate.Brackets0038
import BecknerOnofri.EntropyScalarCertificate.Brackets0039
import BecknerOnofri.EntropyScalarCertificate.Logs0077
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0616
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1826819979019669110914842244796317634911/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1826819979019669110914842244796317634911/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (914460756558605161701255584094055446217/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (914460756558605161701255584094055446217/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (731148298427375886863470682596885705469/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (731148298427375886863470682596885705469/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0616 BracketBatch0038.bracket0617 (731148298427375886863470682596885705469/4000000000000000000000000000000000000000) (205666873665174709374263711707227313/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0616 BracketBatch0038.bracket0617
  (731148298427375886863470682596885705469/4000000000000000000000000000000000000000) (205666873665174709374263711707227313/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0616
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0617
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1828921513117210323402511168188110892431/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1828921513117210323402511168188110892431/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (57219477619655048248661331305650095513/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (57219477619655048248661331305650095513/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (3659944796946171867359673769968913948847/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3659944796946171867359673769968913948847/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0617 BracketBatch0038.bracket0618 (3659944796946171867359673769968913948847/20000000000000000000000000000000000000000) (826362274359088695931110029013895021/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0617 BracketBatch0038.bracket0618
  (3659944796946171867359673769968913948847/20000000000000000000000000000000000000000) (826362274359088695931110029013895021/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0617
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0618
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1831023283828961543957162601780803056413/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1831023283828961543957162601780803056413/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (916562645733643204742997313718861708169/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (916562645733643204742997313718861708169/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (3664148575296247953443157229218526472751/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3664148575296247953443157229218526472751/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0618 BracketBatch0038.bracket0619 (3664148575296247953443157229218526472751/20000000000000000000000000000000000000000) (830069562699749372650465201548988287/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0618 BracketBatch0038.bracket0619
  (3664148575296247953443157229218526472751/20000000000000000000000000000000000000000) (830069562699749372650465201548988287/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0618
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0619
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (366625058293457281897198925487544683267/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (366625058293457281897198925487544683267/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1835227536344727700601203626663213501741/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1835227536344727700601203626663213501741/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (917088206953003527521799563525234229519/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (917088206953003527521799563525234229519/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0619 BracketBatch0038.bracket0620 (917088206953003527521799563525234229519/5000000000000000000000000000000000000000) (833789388448566658159541398332671233/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0619 BracketBatch0038.bracket0620
  (917088206953003527521799563525234229519/5000000000000000000000000000000000000000) (833789388448566658159541398332671233/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0619
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0620
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (917613768172363850300601813331606750869/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (917613768172363850300601813331606750869/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (1837330018774007628278983252541872760883/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1837330018774007628278983252541872760883/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (3672557555118735328880186879205086262621/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3672557555118735328880186879205086262621/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0620 BracketBatch0038.bracket0621 (3672557555118735328880186879205086262621/20000000000000000000000000000000000000000) (418760890203855924658663894522496401/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0620 BracketBatch0038.bracket0621
  (3672557555118735328880186879205086262621/20000000000000000000000000000000000000000) (418760890203855924658663894522496401/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0620
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0621
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (22966625234675095353487290656773409511/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (22966625234675095353487290656773409511/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1839432739068028120857783788738230421113/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1839432739068028120857783788738230421113/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (3676762757842035749136767041280103181993/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3676762757842035749136767041280103181993/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0621 BracketBatch0038.bracket0622 (3676762757842035749136767041280103181993/20000000000000000000000000000000000000000) (6730134139325257761665483146138469/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0621 BracketBatch0038.bracket0622
  (3676762757842035749136767041280103181993/20000000000000000000000000000000000000000) (6730134139325257761665483146138469/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0621
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0622
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (183943273906802812085778378873823042111/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (183943273906802812085778378873823042111/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1841535697539871111376498480790335700101/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1841535697539871111376498480790335700101/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (3680968436607899232234282269528566121211/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3680968436607899232234282269528566121211/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0622 BracketBatch0038.bracket0623 (3680968436607899232234282269528566121211/20000000000000000000000000000000000000000) (845024378347191516527404800886045809/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0622 BracketBatch0038.bracket0623
  (3680968436607899232234282269528566121211/20000000000000000000000000000000000000000) (845024378347191516527404800886045809/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0622
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0623
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (920767848769935555688249240395167850049/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (920767848769935555688249240395167850049/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1843638894502798825253244631439264610749/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1843638894502798825253244631439264610749/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (3685174592042669936629743112229600310847/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3685174592042669936629743112229600310847/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0077.rows ScalarLogs0077.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0623 BracketBatch0039.bracket0624 (3685174592042669936629743112229600310847/20000000000000000000000000000000000000000) (33951785684537418940244023749713113/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0623 BracketBatch0039.bracket0624
  (3685174592042669936629743112229600310847/20000000000000000000000000000000000000000) (33951785684537418940244023749713113/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0623
