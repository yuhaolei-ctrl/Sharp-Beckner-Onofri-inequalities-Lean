# paper 2 与现有 Lean 代码的差异审查

本次以 `paper 2/sharp_beckner_onofri_flat_torus.tex` 为准，以用户指定的
2026-09-27 Lean 压缩包为证明基线。51 个正式结果的标签全部保留，去除空白差异后
28 条陈述文本有变化。逐条原文、新文、标签、位置、目标与审查理由见
`audit/paper2_statement_map.json`。本次是同一实施助手的源码审查，不是独立审稿人认证。

28 条文字变化分为：13 条能量归一化记号，5 条说明或排版，3 条已使用单位周期的对象，
2 条密度端点定义域扩大，2 条 Haar 测度记号，以及物理坐标传输、已使用的物理参数、
参数恒等式各 1 条。除这些变化外，还补齐了文字未变的引理 4.2 的导数级数收敛缺口。

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
| 分数算子出现 `(2π)^2` | 补齐实际物理测度、L² 酉变换、光滑核、闭形式、算子图、谱幂域和任意 U 的交换公式 |
| 论文标签、文字和已有映射漂移 | 保存 51 条新旧陈述和完整目标映射；补齐第一 Fourier 壳障碍的映射 |

新配置共 269 个目标，其中 257 个来自旧证书、12 个是新增适配目标。
目标数量不是论文覆盖率。

## 本轮补齐的正式陈述

**引理 2.9（`lem:fractional`）**：`Paper2PhysicalMeasure.lean` 定义实际物理测度，
活动坐标为 `(0,1/2)`，非活动坐标为 `(0,1]` 的周期表示，并证明 Jacobian。
`Paper2PhysicalLp.lean` 给出原始拉回连续线性等价、内积缩放和酉映射
`Vf(x)=sqrt((2π)^d) f(2πx)`。`Paper2PhysicalCore.lean` 双向传递光滑核、
周期条件、边界支撑和导数，证明势项平方就是论文中的系数。
`Paper2PhysicalForm.lean` 传递闭包及双线性型；`Paper2PhysicalOperator.lean`
证明实际 Friedrichs 算子图的共轭关系、物理谱幂的一阶识别及全部实数幂的域对应。
`Paper2PhysicalFractional.lean` 最终证明任意闭立方体光滑 U、任意非零多重指标、
所有 s>0 的交换公式，包含 `(2π|k|)^(2s)` Fourier 乘子。

**引理 4.2（`lem:section4-periodization-entropy-identity`）**：
`Paper2Periodization.lean` 对原始有理 Euclidean 密度的任意有限序列坐标导数，
构造“原密度 × 有界表达式”的形式证明。平移后使用已有格点可求和控制，
得到每个紧集上的统一可求和上界，最后由 M-test 得到导数级数局部一致收敛。
坐标导数定义为全 Euclidean 空间中普通的坐标线导数；平移可交换性也有证明。
已有概率质量、严格正性、光滑性和条件熵恒等式目标继续使用。

这些新目标在 `Paper2Challenge.lean` 与 `Paper2Proofs.lean` 中具有相同类型，
合并配置登记 269 个目标。编译、公理扫描和外部重放的实际进度分别记录；
完成源码证明不等于外部检查已完成。

## 51 条正式结果以外的范围

注记 5.6 的任意密度反例尚未单独注册；它不在 51 个 thm/lemma/prop/cor 环境内。
Friedrichs 证明中显示的 O(δ^(2m−1)) 速率也未单独注册；形式化证明使用已经
证明的形式范数收敛完成闭包结论。上述差异是证明路线和覆盖边界，不能表述为
逐句覆盖整个手稿。独立外部语义审稿人认证仍未取得。

## 哪些不需要重写

圆周重排已经在 UnitAddCircle 上定义；Euler 余弦表示与 Steiner 选择已经使用
`cos(2πx)`、`[0,1/2]` 和物理 β 参数。低维 `low_scalar_gap` 已经写成
`2*d/spectralThreshold d`。十一维数值常数和高维有限状态常数在这次文字改动中
未变；没有理由重新生成这些证书。能量归一化应通过统一桥接引理解释。

最终状态须分别记录：机器验证、新旧数学对象对应、独立外部语义审查。
任何一项通过都不能自动替代其他两项。
