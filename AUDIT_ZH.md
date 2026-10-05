# paper 2 与现有 Lean 代码的差异审查

本次以 `paper 2/sharp_beckner_onofri_flat_torus.tex` 为准，以用户指定的
2026-09-27 Lean 压缩包为证明基线。51 个正式结果的标签全部保留，去除空白差异后
28 条陈述文本有变化。逐条原文、新文、标签、位置、目标与审查理由见
`audit/paper2_statement_map.json`。本次是同一实施助手的源码审查，不是独立审稿人认证。

## d≤10 采用什么形式化方式

低维与高维同样采用 Challenge → Solution → Comparator。

1. `Challenge.lean` 的 `low_density_endpoint`、`low_potential_endpoint`、等号分类、
   圆周 Poisson 家族及尖锐系数目标给出待证类型。
2. `Solution.lean` 调用 `BecknerOnofri/LowDimensionRaw.lean`、
   `LowDimensionConsequences.lean` 等文件的证明。
3. 这些文件把当前真实的 Haar 概率密度、临界 Sobolev 域和 Fourier 能量与
   `Legacy/BecknerOnofri/LowDimensionComplete.lean` 中的旧命名空间连接。
4. `Legacy` 内有形式证明；例如 `Legacy/D10/FiniteScalarSemantics.lean` 的有限检查
   使用 `decide +kernel`。检查器的数学含义、尾部控制和端点闭合也是 Lean 证明。
5. Comparator 检查类型和相关定义一致、传递公理白名单，并重放官方内核。

因此它不是把旧论文、Python 运行结果或某个“已证明”布尔字段作为外部公理。
低维 proof-route 与手稿逐行一致也不是必要条件；替代证明的对应范围需要单独说明。

## 已新增的适配代码

原 257 目标及其辅助证明保持不变。新文件 `Paper2Definitions.lean`、
`Paper2Proofs.lean`、`Paper2Challenge.lean`、`Paper2Solution.lean` 提供独立适配层，
机器检查的实际结果以 `verification/STATUS.json` 为准。

| 变化 | 处理 |
|---|---|
| Q 记号改成负阶 Sobolev 半范数 | 定义扩展非负能量，并证明与显式 Fourier 级数及 `(2π)^d` 缩放相等 |
| 低维密度端点扩大至所有概率密度 | 注册已有扩展熵证明的新版封装；等号仍要求有限熵 |
| 高维密度端点扩大至所有概率密度 | 按有限熵/无限熵分情况补充扩展实数端点 |
| 分数算子出现 `(2π)^2` | 证明原角坐标 Hilbert 空间上的谱幂缩放；**尚不能替代实际空间转换** |
| 论文标签、文字和已有映射漂移 | 保存 51 条新旧陈述和完整目标映射；补齐第一 Fourier 壳障碍的映射 |

新配置共 262 个目标，其中 257 个来自旧证书、5 个是新增适配目标。
目标数量不是论文覆盖率。

## 必须继续补齐的部分

**最重要的是引理 `lem:fractional`（原编号 2.9）的真实空间转换。**
旧 `MixedFractionalStatementDefinitions.lean` 的空间是活动坐标 `(0,π)`、
非活动坐标 `(0,2π]`，谱乘子为 `|k|^(2s)`。新版是 `(0,1/2)`、单位周期，
势带 `(2π)^2`，乘子为 `(2π|k|)^(2s)`。

令 `c=2π`，从角空间到物理空间的酉映射应为
`(Vf)(x)=c^(d/2) f(cx)`，因 `dθ=c^d dx`。需要在 Lean 中依次证明：

- 实际受限 Lebesgue 乘积测度的换元和 L² 酉映射；保留全部周期奇偶扇区。
- 光滑核、Dirichlet 边界和周期条件的双向对应。
- 闭形式和算子图 `B_x=c² V B_θ V⁻¹`。
- 分数幂的域及作用 `B_x^s=c^(2s) V B_θ^s V⁻¹`。
- 原始任意闭立方体光滑 U、非零多重指标和所有 s>0 的物理坐标交换式。
- 单独注册新的 physical intertwining Challenge 目标并给出 Solution。

目前新增的 `physicalSpectralPowerGraph_scaling` 只覆盖谱乘子的代数步骤。
不能把旧 angular theorem 重命名后称作上述完整物理坐标定理。

还有三个继承的覆盖边界：

| 原稿位置 | 现状 / 下一步 |
|---|---|
| `lem:section4-periodization-entropy-identity`，原 4.2 | 原周期化级数各阶导数的局部一致收敛尚无独立形式证明；现有 Fourier 衰减证明的是同一密度光滑。若要求整条引理字面覆盖，需补一致收敛目标。 |
| `rem:spectral-energy-restriction`，原注记 5.6 | 反例未单独形式化；它不在按 thm/lemma/prop/cor 枚举的 51 条内。 |
| Friedrichs 截断证明中的显式速率 | 现有证明用支配收敛给出所需形式范数收敛；显示的 O(δ^(2m−1)) 速率未单独导出。 |

这些缺口不等于旧端点 Lean 定理无证明，但意味着不能把旧证书称作新版逐句、逐算子实现的完整形式化。

## 哪些不需要重写

圆周重排已经在 UnitAddCircle 上定义；Euler 余弦表示与 Steiner 选择已经使用
`cos(2πx)`、`[0,1/2]` 和物理 β 参数。低维 `low_scalar_gap` 已经写成
`2*d/spectralThreshold d`。十一维数值常数和高维有限状态常数在这次文字改动中
未变；没有理由重新生成这些证书。能量归一化应通过统一桥接引理解释。

最终仍需分别完成：机器验证、新旧数学对象对应、独立外部语义审查。
任何一项通过都不能自动替代其他两项。
