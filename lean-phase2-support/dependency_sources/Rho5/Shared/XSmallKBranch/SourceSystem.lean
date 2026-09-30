import Rho5.Shared.XSmallKBranch.RootBox

/-
D136 续（第五叶）— 实际矩阵的**来源系统**（波输入）：106 行 + 根盒 + 提升 + 35 条外包
=====================================================================================

把前面各叶已付事实打包成**单一可消费对象** `SourceSystem M`，供 M01 的覆盖层/后续检查器消费：

* `rows`：106 条源行的 LP 语义（104 冻结 + 96/98 两条矩阵行）；
* `boxIn`：§3.4 的 22 维根盒（**结论**，非假设）；
* `lift`：35 个共享乘积变量确实是真实乘积；
* `envelopes`：35 个乘积关于根盒端点满足原文 (5.1) 的四条 McCormick 外包。

显式前提：`SatFrame`、`NormalizedSigns`、`PosSigns`、`0 ≤ u₀`、`HighValue`、`k ≤ 2`
（`PhysicalBounds` 与 `Rho4Input` 已在前几叶内部支付）。

**本叶不做**：不重写 D135 检查器、不重算其样本、不用有理逼近替代全实数证明；
`terminal_empty` 的有理域版本不能当作实际 ℝ 来源为空——真实实数无解接口待
D135 `CERTIFICATE_RULES_REAL_SOUNDNESS_READY` 发布后再消费。
-/

noncomputable section
namespace Rho5.Shared.XSmallKBranch

open Rho5
open Rho5.Shared.V43MatrixRoundTrip

/-- 35 个共享乘积的四条外包（逐对列出，端点取根盒）。 -/
theorem envelopes_all_chartState (M : Matrix5) (hbox : BoxIn (chartState M)) :
    McCormick (chartState M 15) (chartState M 21) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ) ((boxLo 21 : ℚ) : ℝ) ((boxHi 21 : ℚ) : ℝ) ∧
    McCormick (chartState M 15) (chartState M 20) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ) ((boxLo 20 : ℚ) : ℝ) ((boxHi 20 : ℚ) : ℝ) ∧
    McCormick (chartState M 15) (chartState M 19) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ) ((boxLo 19 : ℚ) : ℝ) ((boxHi 19 : ℚ) : ℝ) ∧
    McCormick (chartState M 14) (chartState M 21) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ) ((boxLo 21 : ℚ) : ℝ) ((boxHi 21 : ℚ) : ℝ) ∧
    McCormick (chartState M 14) (chartState M 20) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ) ((boxLo 20 : ℚ) : ℝ) ((boxHi 20 : ℚ) : ℝ) ∧
    McCormick (chartState M 14) (chartState M 19) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ) ((boxLo 19 : ℚ) : ℝ) ((boxHi 19 : ℚ) : ℝ) ∧
    McCormick (chartState M 13) (chartState M 21) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ) ((boxLo 21 : ℚ) : ℝ) ((boxHi 21 : ℚ) : ℝ) ∧
    McCormick (chartState M 13) (chartState M 20) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ) ((boxLo 20 : ℚ) : ℝ) ((boxHi 20 : ℚ) : ℝ) ∧
    McCormick (chartState M 13) (chartState M 19) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ) ((boxLo 19 : ℚ) : ℝ) ((boxHi 19 : ℚ) : ℝ) ∧
    McCormick (chartState M 12) (chartState M 18) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ) ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) ∧
    McCormick (chartState M 12) (chartState M 17) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ) ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) ∧
    McCormick (chartState M 12) (chartState M 16) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ) ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) ∧
    McCormick (chartState M 11) (chartState M 18) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ) ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) ∧
    McCormick (chartState M 11) (chartState M 17) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ) ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) ∧
    McCormick (chartState M 11) (chartState M 16) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ) ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) ∧
    McCormick (chartState M 10) (chartState M 18) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ) ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) ∧
    McCormick (chartState M 10) (chartState M 17) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ) ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) ∧
    McCormick (chartState M 10) (chartState M 16) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ) ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) ∧
    McCormick (chartState M 9) (chartState M 18) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ) ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) ∧
    McCormick (chartState M 9) (chartState M 17) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ) ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) ∧
    McCormick (chartState M 9) (chartState M 16) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ) ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) ∧
    McCormick (chartState M 8) (chartState M 12) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ) ∧
    McCormick (chartState M 8) (chartState M 11) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ) ∧
    McCormick (chartState M 8) (chartState M 10) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ) ∧
    McCormick (chartState M 8) (chartState M 9) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ) ∧
    McCormick (chartState M 7) (chartState M 15) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ) ∧
    McCormick (chartState M 7) (chartState M 14) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ) ∧
    McCormick (chartState M 7) (chartState M 13) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ) ∧
    McCormick (chartState M 4) (chartState M 6) ((boxLo 4 : ℚ) : ℝ) ((boxHi 4 : ℚ) : ℝ) ((boxLo 6 : ℚ) : ℝ) ((boxHi 6 : ℚ) : ℝ) ∧
    McCormick (chartState M 4) (chartState M 5) ((boxLo 4 : ℚ) : ℝ) ((boxHi 4 : ℚ) : ℝ) ((boxLo 5 : ℚ) : ℝ) ((boxHi 5 : ℚ) : ℝ) ∧
    McCormick (chartState M 3) (chartState M 6) ((boxLo 3 : ℚ) : ℝ) ((boxHi 3 : ℚ) : ℝ) ((boxLo 6 : ℚ) : ℝ) ((boxHi 6 : ℚ) : ℝ) ∧
    McCormick (chartState M 3) (chartState M 5) ((boxLo 3 : ℚ) : ℝ) ((boxHi 3 : ℚ) : ℝ) ((boxLo 5 : ℚ) : ℝ) ((boxHi 5 : ℚ) : ℝ) ∧
    McCormick (chartState M 0) (chartState M 7) ((boxLo 0 : ℚ) : ℝ) ((boxHi 0 : ℚ) : ℝ) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ) ∧
    McCormick (chartState M 0) (chartState M 6) ((boxLo 0 : ℚ) : ℝ) ((boxHi 0 : ℚ) : ℝ) ((boxLo 6 : ℚ) : ℝ) ((boxHi 6 : ℚ) : ℝ) ∧
    McCormick (chartState M 0) (chartState M 5) ((boxLo 0 : ℚ) : ℝ) ((boxHi 0 : ℚ) : ℝ) ((boxLo 5 : ℚ) : ℝ) ((boxHi 5 : ℚ) : ℝ) := by
  exact ⟨envelope_0 (chartState M) (chartState_isLift M) hbox,
    envelope_1 (chartState M) (chartState_isLift M) hbox,
    envelope_2 (chartState M) (chartState_isLift M) hbox,
    envelope_3 (chartState M) (chartState_isLift M) hbox,
    envelope_4 (chartState M) (chartState_isLift M) hbox,
    envelope_5 (chartState M) (chartState_isLift M) hbox,
    envelope_6 (chartState M) (chartState_isLift M) hbox,
    envelope_7 (chartState M) (chartState_isLift M) hbox,
    envelope_8 (chartState M) (chartState_isLift M) hbox,
    envelope_9 (chartState M) (chartState_isLift M) hbox,
    envelope_10 (chartState M) (chartState_isLift M) hbox,
    envelope_11 (chartState M) (chartState_isLift M) hbox,
    envelope_12 (chartState M) (chartState_isLift M) hbox,
    envelope_13 (chartState M) (chartState_isLift M) hbox,
    envelope_14 (chartState M) (chartState_isLift M) hbox,
    envelope_15 (chartState M) (chartState_isLift M) hbox,
    envelope_16 (chartState M) (chartState_isLift M) hbox,
    envelope_17 (chartState M) (chartState_isLift M) hbox,
    envelope_18 (chartState M) (chartState_isLift M) hbox,
    envelope_19 (chartState M) (chartState_isLift M) hbox,
    envelope_20 (chartState M) (chartState_isLift M) hbox,
    envelope_21 (chartState M) (chartState_isLift M) hbox,
    envelope_22 (chartState M) (chartState_isLift M) hbox,
    envelope_23 (chartState M) (chartState_isLift M) hbox,
    envelope_24 (chartState M) (chartState_isLift M) hbox,
    envelope_25 (chartState M) (chartState_isLift M) hbox,
    envelope_26 (chartState M) (chartState_isLift M) hbox,
    envelope_27 (chartState M) (chartState_isLift M) hbox,
    envelope_28 (chartState M) (chartState_isLift M) hbox,
    envelope_29 (chartState M) (chartState_isLift M) hbox,
    envelope_30 (chartState M) (chartState_isLift M) hbox,
    envelope_31 (chartState M) (chartState_isLift M) hbox,
    envelope_32 (chartState M) (chartState_isLift M) hbox,
    envelope_33 (chartState M) (chartState_isLift M) hbox,
    envelope_34 (chartState M) (chartState_isLift M) hbox⟩

/-- **实际矩阵的来源系统**（波输入）：106 行 + 根盒 + 提升 + 35 条外包。 -/
structure SourceSystem (M : Matrix5) : Prop where
  rows : ∀ i, i ∈ paidIdx ∨ i = 96 ∨ i = 98 → RowProp i (chartState M)
  boxIn : BoxIn (chartState M)
  lift : IsLift (chartState M)
  envelopes :
    McCormick (chartState M 15) (chartState M 21) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ) ((boxLo 21 : ℚ) : ℝ) ((boxHi 21 : ℚ) : ℝ) ∧
    McCormick (chartState M 15) (chartState M 20) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ) ((boxLo 20 : ℚ) : ℝ) ((boxHi 20 : ℚ) : ℝ) ∧
    McCormick (chartState M 15) (chartState M 19) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ) ((boxLo 19 : ℚ) : ℝ) ((boxHi 19 : ℚ) : ℝ) ∧
    McCormick (chartState M 14) (chartState M 21) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ) ((boxLo 21 : ℚ) : ℝ) ((boxHi 21 : ℚ) : ℝ) ∧
    McCormick (chartState M 14) (chartState M 20) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ) ((boxLo 20 : ℚ) : ℝ) ((boxHi 20 : ℚ) : ℝ) ∧
    McCormick (chartState M 14) (chartState M 19) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ) ((boxLo 19 : ℚ) : ℝ) ((boxHi 19 : ℚ) : ℝ) ∧
    McCormick (chartState M 13) (chartState M 21) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ) ((boxLo 21 : ℚ) : ℝ) ((boxHi 21 : ℚ) : ℝ) ∧
    McCormick (chartState M 13) (chartState M 20) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ) ((boxLo 20 : ℚ) : ℝ) ((boxHi 20 : ℚ) : ℝ) ∧
    McCormick (chartState M 13) (chartState M 19) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ) ((boxLo 19 : ℚ) : ℝ) ((boxHi 19 : ℚ) : ℝ) ∧
    McCormick (chartState M 12) (chartState M 18) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ) ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) ∧
    McCormick (chartState M 12) (chartState M 17) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ) ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) ∧
    McCormick (chartState M 12) (chartState M 16) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ) ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) ∧
    McCormick (chartState M 11) (chartState M 18) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ) ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) ∧
    McCormick (chartState M 11) (chartState M 17) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ) ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) ∧
    McCormick (chartState M 11) (chartState M 16) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ) ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) ∧
    McCormick (chartState M 10) (chartState M 18) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ) ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) ∧
    McCormick (chartState M 10) (chartState M 17) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ) ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) ∧
    McCormick (chartState M 10) (chartState M 16) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ) ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) ∧
    McCormick (chartState M 9) (chartState M 18) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ) ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) ∧
    McCormick (chartState M 9) (chartState M 17) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ) ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) ∧
    McCormick (chartState M 9) (chartState M 16) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ) ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) ∧
    McCormick (chartState M 8) (chartState M 12) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ) ∧
    McCormick (chartState M 8) (chartState M 11) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ) ∧
    McCormick (chartState M 8) (chartState M 10) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ) ∧
    McCormick (chartState M 8) (chartState M 9) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ) ∧
    McCormick (chartState M 7) (chartState M 15) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ) ∧
    McCormick (chartState M 7) (chartState M 14) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ) ∧
    McCormick (chartState M 7) (chartState M 13) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ) ∧
    McCormick (chartState M 4) (chartState M 6) ((boxLo 4 : ℚ) : ℝ) ((boxHi 4 : ℚ) : ℝ) ((boxLo 6 : ℚ) : ℝ) ((boxHi 6 : ℚ) : ℝ) ∧
    McCormick (chartState M 4) (chartState M 5) ((boxLo 4 : ℚ) : ℝ) ((boxHi 4 : ℚ) : ℝ) ((boxLo 5 : ℚ) : ℝ) ((boxHi 5 : ℚ) : ℝ) ∧
    McCormick (chartState M 3) (chartState M 6) ((boxLo 3 : ℚ) : ℝ) ((boxHi 3 : ℚ) : ℝ) ((boxLo 6 : ℚ) : ℝ) ((boxHi 6 : ℚ) : ℝ) ∧
    McCormick (chartState M 3) (chartState M 5) ((boxLo 3 : ℚ) : ℝ) ((boxHi 3 : ℚ) : ℝ) ((boxLo 5 : ℚ) : ℝ) ((boxHi 5 : ℚ) : ℝ) ∧
    McCormick (chartState M 0) (chartState M 7) ((boxLo 0 : ℚ) : ℝ) ((boxHi 0 : ℚ) : ℝ) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ) ∧
    McCormick (chartState M 0) (chartState M 6) ((boxLo 0 : ℚ) : ℝ) ((boxHi 0 : ℚ) : ℝ) ((boxLo 6 : ℚ) : ℝ) ((boxHi 6 : ℚ) : ℝ) ∧
    McCormick (chartState M 0) (chartState M 5) ((boxLo 0 : ℚ) : ℝ) ((boxHi 0 : ℚ) : ℝ) ((boxLo 5 : ℚ) : ℝ) ((boxHi 5 : ℚ) : ℝ)

/-- 由显式前提构造来源系统（`PhysicalBounds` 与 `Rho4Input` 内部支付，`BoxIn` 由根盒叶导出）。 -/
theorem sourceSystem_of_satFrame (M : Matrix5) (h : SatFrame M)
    (hs : NormalizedSigns (chartState M)) (hpos : PosSigns (chartState M))
    (hu0 : 0 ≤ uu (chartState M) 0) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : SourceSystem M where
  rows := all_rows_sound_of_satFrame_noRho4 M h hs hF hk2
  boxIn := rootBox_chartState_noRho4 h (physicalBounds_chartState M h) hs hpos hu0 hF hk2
  lift := chartState_isLift M
  envelopes := envelopes_all_chartState M (rootBox_chartState_noRho4 h (physicalBounds_chartState M h) hs hpos hu0 hF hk2)

end Rho5.Shared.XSmallKBranch
