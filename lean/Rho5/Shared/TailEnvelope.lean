/-
D46 — 任意（未平衡）二阶真实尾块的精确增长上包络
=================================================

本卡只提供**二阶尾块的精确标量包络与等号资格**，作为将来 B24 分类证明的接口。
固定 `r > 0`、`T = [[r, s], [t, d]]`，`δ = d - t * s / r`，`E = r + |s * t| / r`：

1. **标量精确结论**（目标 1）：只用 `r > 0` 与 `|d| ≤ r` 得 `|δ| ≤ E`；并给出三条
   等号分类 —— `s*t > 0` 时 `|δ| = E ↔ d = -r`，`s*t < 0` 时 `|δ| = E ↔ d = r`，
   `s*t = 0` 时 `|δ| = E ↔ |d| = r`。正负分类留在**假设**里，不藏进定义；不做数值搜索。
2. **接真实 D10 `pivotSchur`**（目标 2）：`2 × 2` 的 `(0,0)` 消元唯一条目正是 `δ`
   （`delta_eq_pivotSchur_zero_zero`）；再用冻结的 D13 语义给出真实
   `LegalTrace T [|T 0 0|, |δ|]`。最后一枚主元为零时走 `zeroStop = [0]` 分支
   （`legalTrace_one_zeroStop`），**不假设最后主元非零**；同时给出显式 `step` 分支、
   `T 0 0 > 0` 的写法与 D40 首位置口径（`LeadingLegalTrace`）。
3. **该实际路径的峰值**（目标 3）：`tracePeak [r, |δ|] = max r |δ| ≤ E`；用 CP 的
   `|s|, |t| ≤ r` 给短推论 `E ≤ 2 * r`；最后给 `d = -r`、`s*t ≥ 0` 时最后主元绝对值
   `= r + s*t/r` 的薄适配（与既有 B24 的 F 形式吻合），不用更强的 `s ≥ 0, t ≥ 0` 缩域。

**未声明（本卡不支付，留给全局可行性责任方）**：不证明把任意五阶矩阵的 `d` 换成 `±r`
后仍保持此前各阶段的 CP/原盒合法；不声称平衡尾块无损、B24 全覆盖、全局 alpha 上界或
最终 `rho5` 值。目标 3 的 `d = -r` 薄适配只是**同一尾块内**的等号重写，不构成“平衡变形
总合法”的前提，也不声称该等号在真实路径上可达。

只读复用冻结输入：D08 `MatrixNormalization`、D10 `PivotReindex`、D13
`CompletePivotPath`、D17 `GrowthModel`、D40 `LeadingTrace`（D12/D20 经它们的 import 只读
引入）。无 `sorry`、无 `admit`、无 `native_decide`、无项目公理。
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath
import Rho5.Shared.GrowthModel
import Rho5.Shared.LeadingTrace

namespace Rho5.TailEnvelope

/-! ## 0. 标量工具 -/

/-- **工具引理（三角不等式取等的符号条件）**：`|a + b| = |a| + |b|` 迫使 `a * b ≥ 0`。
证明用平方：两边平方消去 `a², b²` 得 `a * b = |a| * |b| ≥ 0`。这是目标 1 三条等号分类
共用的唯一取等判据，不引用任何“平衡”前提。 -/
theorem nonneg_mul_of_abs_add_eq {a b : ℝ} (h : |a + b| = |a| + |b|) : 0 ≤ a * b := by
  have h2 : (a + b) ^ 2 = (|a| + |b|) ^ 2 := by rw [← sq_abs (a + b), h]
  have h3 : a * b = |a| * |b| := by nlinarith [h2, sq_abs a, sq_abs b]
  have h4 : 0 ≤ |a| * |b| := mul_nonneg (abs_nonneg a) (abs_nonneg b)
  linarith

/-- 目标 1 的两步三角链取等时的中间结论：`|d| = r` 且 `d` 与 `-(t*s/r)` 同号
（写成 `0 ≤ (-(t*s/r)) * d` 以便直接用 `nonneg/nonpos_of_mul_nonneg_right`）。 -/
private theorem eq_envelope_imp {r s t d : ℝ} (hr : 0 < r) (hd : |d| ≤ r)
    (h : |d - t * s / r| = r + |s * t| / r) :
    |d| = r ∧ 0 ≤ (-(t * s / r)) * d := by
  have htri : |d - t * s / r| ≤ |d| + |t * s / r| := by
    have h1 := abs_add_le d (-(t * s / r))
    simpa [sub_eq_add_neg, abs_neg] using h1
  have hdiv : |t * s / r| = |s * t| / r := by
    rw [abs_div, abs_mul, abs_of_pos hr, abs_mul]
    ring
  have hle : |d| + |t * s / r| ≤ r + |s * t| / r := by
    rw [hdiv]; linarith
  have htri' : |d| + |t * s / r| ≤ |d - t * s / r| := by rw [h]; exact hle
  have heq : |d - t * s / r| = |d| + |t * s / r| := le_antisymm htri htri'
  have hdr : |d| = r := by
    have hsum : |d| + |t * s / r| = r + |s * t| / r := by rw [← heq]; exact h
    linarith
  have habs : |d + -(t * s / r)| = |d| + |-(t * s / r)| := by
    have h1 : d + -(t * s / r) = d - t * s / r := by ring
    rw [h1, abs_neg]
    exact heq
  exact ⟨hdr, by simpa [mul_comm] using nonneg_mul_of_abs_add_eq habs⟩

/-! ## 1. 目标 1：精确包络与三条等号分类 -/

/-- **目标 1（精确上包络）**：只用 `r > 0` 与 `|d| ≤ r`，
`|d - t*s/r| ≤ r + |s*t|/r`。不假设 `T` 的主元性质、不假设 `s`、`t` 的符号，
也不假设 `T` 的任何 CP 前提。 -/
theorem abs_delta_le_envelope {r s t d : ℝ} (hr : 0 < r) (hd : |d| ≤ r) :
    |d - t * s / r| ≤ r + |s * t| / r := by
  have htri : |d - t * s / r| ≤ |d| + |t * s / r| := by
    have h1 := abs_add_le d (-(t * s / r))
    simpa [sub_eq_add_neg, abs_neg] using h1
  have hdiv : |t * s / r| = |s * t| / r := by
    rw [abs_div, abs_mul, abs_of_pos hr, abs_mul]
    ring
  have h2 : |d| + |t * s / r| ≤ r + |s * t| / r := by
    rw [hdiv]; linarith
  linarith

/-- **目标 1（等号分类，`s*t > 0`）**：此时 `t*s/r > 0`，取等迫使 `|d| = r` 且
`d ≤ 0`，故 `d = -r`；反之 `d = -r` 直接给出等号。正负前提显式留在假设里。 -/
theorem abs_delta_eq_envelope_iff_of_pos {r s t d : ℝ} (hr : 0 < r) (hd : |d| ≤ r)
    (hst : 0 < s * t) : |d - t * s / r| = r + |s * t| / r ↔ d = -r := by
  constructor
  · intro h
    obtain ⟨hdr, hsign⟩ := eq_envelope_imp hr hd h
    have hts : 0 < t * s := by rwa [mul_comm t s]
    have hc : 0 < t * s / r := div_pos hts hr
    have hdnonpos : d ≤ 0 := nonpos_of_mul_nonneg_right hsign (by linarith)
    have h1 : |d| = -d := abs_of_nonpos hdnonpos
    linarith
  · intro hd'
    rw [hd']
    have hts : 0 < t * s := by rwa [mul_comm t s]
    have hpos : 0 < r + t * s / r := add_pos hr (div_pos hts hr)
    have h1 : -r - t * s / r = -(r + t * s / r) := by ring
    rw [h1, abs_neg, abs_of_pos hpos, abs_of_pos hst]
    ring

/-- **目标 1（等号分类，`s*t < 0`）**：此时 `t*s/r < 0`，取等迫使 `|d| = r` 且
`d ≥ 0`，故 `d = r`；反之 `d = r` 直接给出等号。 -/
theorem abs_delta_eq_envelope_iff_of_neg {r s t d : ℝ} (hr : 0 < r) (hd : |d| ≤ r)
    (hst : s * t < 0) : |d - t * s / r| = r + |s * t| / r ↔ d = r := by
  constructor
  · intro h
    obtain ⟨hdr, hsign⟩ := eq_envelope_imp hr hd h
    have hts : t * s < 0 := by rwa [mul_comm t s]
    have hc : t * s / r < 0 := div_neg_of_neg_of_pos hts hr
    have hdnonneg : 0 ≤ d := nonneg_of_mul_nonneg_right hsign (by linarith)
    have h1 : |d| = d := abs_of_nonneg hdnonneg
    linarith
  · intro hd'
    rw [hd']
    have hts : t * s < 0 := by rwa [mul_comm t s]
    have hneg : t * s / r < 0 := div_neg_of_neg_of_pos hts hr
    have hpos : 0 < r - t * s / r := by linarith
    rw [abs_of_pos hpos, abs_of_neg hst]
    ring

/-- **目标 1（等号分类，`s*t = 0`）**：此时 `t*s/r = 0` 且 `|s*t|/r = 0`，两边同时退化为
`|d| = r`，故等号资格与 `d` 的符号无关。`hr`、`hd` 为与另两条分类保持同一接口而保留，
本分支的等价不需要它们。 -/
theorem abs_delta_eq_envelope_iff_of_zero {r s t d : ℝ} (hr : 0 < r) (hd : |d| ≤ r)
    (hst : s * t = 0) : |d - t * s / r| = r + |s * t| / r ↔ |d| = r := by
  have _ := hr
  have _ := hd
  have hts : t * s = 0 := by rw [mul_comm t s]; exact hst
  rw [hts, zero_div, sub_zero, hst, abs_zero, zero_div, add_zero]

/-! ## 2. 目标 2：接真实 D10 `pivotSchur` 与冻结 D13 语义 -/

/-- `Fin 1` 上的 `(0,0)` 处比较：唯一的条目与自身相等，故任何 `1 × 1` 矩阵都在
`(0,0)` 有完整主元。最后阶段的“主元性质”不是假设，而是可证的。 -/
theorem isCompletePivot_fin_one (B : Matrix (Fin 1) (Fin 1) ℝ) :
    Rho5.Pivot.IsCompletePivot B 0 0 := by
  intro i j
  fin_cases i
  fin_cases j
  exact le_refl _

private theorem fin_succ_zero_two : (0 : Fin 1).succ = (1 : Fin 2) := by decide

/-- **目标 2（消元唯一条目 = δ）**：`2 × 2` 矩阵在 `(0,0)` 处的真实 D10 `pivotSchur`
只剩一个条目，其值正是 `T 1 1 - T 1 0 * T 0 1 / T 0 0`（即卡上的
`δ = d - t*s/r`，其中 `d = T 1 1`、`s = T 0 1`、`t = T 1 0`、`r = T 0 0`）。
公式是全定义的，因此 `T 0 0 = 0` 时该等式同样成立（此时它只描述真实除法语义）。 -/
theorem delta_eq_pivotSchur_zero_zero (T : Matrix (Fin 2) (Fin 2) ℝ) :
    Rho5.PivotReindex.pivotSchur T 0 0 0 0 = T 1 1 - T 1 0 * T 0 1 / T 0 0 := by
  simp only [Rho5.PivotReindex.pivotSchur_apply, Rho5.LeadingTrace.remainingIndex_zero,
    fin_succ_zero_two]

/-- **目标 2（尾部 zeroStop 分支）**：最后 `1 × 1` 块为零时，D13 语义给出
`LegalTrace B [0]`（`zeroStop`），**不要求**最后主元非零。 -/
theorem legalTrace_one_zeroStop {B : Matrix (Fin 1) (Fin 1) ℝ} (hB : B = 0) :
    Rho5.CompletePivotPath.LegalTrace B [0] :=
  Rho5.CompletePivotPath.LegalTrace.zeroStop hB

/-- **目标 2（尾部 step 分支）**：最后 `1 × 1` 块的条目非零时，`(0,0)` 是真实合法主元，
迹为 `[|B 0 0|]`（其 `0 × 0` 尾巴走 `empty`）。 -/
theorem legalTrace_one_step {B : Matrix (Fin 1) (Fin 1) ℝ} (hne : B 0 0 ≠ 0) :
    Rho5.CompletePivotPath.LegalTrace B [|B 0 0|] := by
  refine Rho5.CompletePivotPath.LegalTrace.step 0 0 (isCompletePivot_fin_one B) hne ?_
  have hz : Rho5.PivotReindex.pivotSchur B 0 0 = 0 := by
    funext i j
    exact Fin.elim0 i
  rw [hz]
  exact Rho5.CompletePivotPath.LegalTrace.empty

/-- **目标 2（尾部总形式）**：任意 `1 × 1` 矩阵都有真实迹 `[|B 0 0|]`，两个分支都在
定理内部处理：零矩阵走 `zeroStop`（此时 `|B 0 0| = 0`），非零矩阵走 `step`。
这是“不能假设最后主元非零”的正面陈述。 -/
theorem legalTrace_one (B : Matrix (Fin 1) (Fin 1) ℝ) :
    Rho5.CompletePivotPath.LegalTrace B [|B 0 0|] := by
  by_cases hne : B 0 0 = 0
  · have hB : B = 0 := by
      funext i j
      fin_cases i
      fin_cases j
      simpa using hne
    rw [hB]
    simpa using Rho5.CompletePivotPath.LegalTrace.zeroStop
      (rfl : (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0)
  · exact legalTrace_one_step hne

/-- **目标 2（真实 `LegalTrace T [|T 0 0|, |δ|]`）**：`T` 在 `(0,0)` 有真实完整主元且该主元
非零时，冻结 D13 关系给出以 `|T 0 0|` 开头、以真实尾部条目绝对值 `|δ|` 收尾的迹。
`δ = 0` 的情形由 `legalTrace_one` 的 `zeroStop` 分支覆盖，故本定理对 `δ` 不作任何非零假设。 -/
theorem legalTrace_two_of_pivot {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hne : T 0 0 ≠ 0) :
    Rho5.CompletePivotPath.LegalTrace T
      [|T 0 0|, |Rho5.PivotReindex.pivotSchur T 0 0 0 0|] :=
  Rho5.CompletePivotPath.LegalTrace.step 0 0 hmax hne
    (legalTrace_one (Rho5.PivotReindex.pivotSchur T 0 0))

/-- **目标 2（正主元写法）**：`0 < T 0 0` 时首项写成 `T 0 0` 本身（`|T 0 0| = T 0 0`），
与卡上 `r > 0` 的记号一致。 -/
theorem legalTrace_two_of_pivot_pos {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hpos : 0 < T 0 0) :
    Rho5.CompletePivotPath.LegalTrace T
      [T 0 0, |Rho5.PivotReindex.pivotSchur T 0 0 0 0|] := by
  simpa [abs_of_pos hpos] using legalTrace_two_of_pivot hmax (ne_of_gt hpos)

/-- **目标 2（显式 zeroStop 分支）**：尾部矩阵为零时迹恰为 `[|T 0 0|, 0]`；这是
`δ = 0` 的真实形态，可与 `legalTrace_two_step_tail` 并读以看清两个分支的差别。 -/
theorem legalTrace_two_zero_tail {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hne : T 0 0 ≠ 0)
    (hzero : Rho5.PivotReindex.pivotSchur T 0 0 = 0) :
    Rho5.CompletePivotPath.LegalTrace T [|T 0 0|, 0] :=
  Rho5.CompletePivotPath.LegalTrace.step 0 0 hmax hne
    (Rho5.CompletePivotPath.LegalTrace.zeroStop hzero)

/-- **目标 2（显式 step 分支）**：尾部矩阵非零时，`(0,0)` 是其真实合法主元，
迹为 `[|T 0 0|, |δ|]` 且尾部由 `step`（而非 `zeroStop`）产生。 -/
theorem legalTrace_two_step_tail {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hne : T 0 0 ≠ 0)
    (htail : Rho5.PivotReindex.pivotSchur T 0 0 ≠ 0) :
    Rho5.CompletePivotPath.LegalTrace T
      [|T 0 0|, |Rho5.PivotReindex.pivotSchur T 0 0 0 0|] := by
  have h00 : Rho5.PivotReindex.pivotSchur T 0 0 0 0 ≠ 0 := by
    intro h
    apply htail
    funext i j
    fin_cases i
    fin_cases j
    simpa using h
  refine Rho5.CompletePivotPath.LegalTrace.step 0 0 hmax hne ?_
  exact legalTrace_one_step h00

/-- **目标 2（D40 首位置口径，尾部总形式）**：同样的两个分支，但用 D40 的
`LeadingLegalTrace`（主元固定在 `(0,0)`，仍是真实 CP + 非零主元）。 -/
theorem leadingLegalTrace_one (B : Matrix (Fin 1) (Fin 1) ℝ) :
    Rho5.LeadingTrace.LeadingLegalTrace B [|B 0 0|] := by
  by_cases hne : B 0 0 = 0
  · have hB : B = 0 := by
      funext i j
      fin_cases i
      fin_cases j
      simpa using hne
    rw [hB]
    simpa using Rho5.LeadingTrace.LeadingLegalTrace.zeroStop
      (rfl : (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0)
  · refine Rho5.LeadingTrace.LeadingLegalTrace.step (isCompletePivot_fin_one B) hne ?_
    have hz : Rho5.PivotReindex.pivotSchur B 0 0 = 0 := by
      funext i j
      exact Fin.elim0 i
    rw [hz]
    exact Rho5.LeadingTrace.LeadingLegalTrace.empty

/-- **目标 2（D40 首位置口径）**：与 `legalTrace_two_of_pivot` 同一构造，只是关系换成
D40 的 `LeadingLegalTrace`；两者值表相同，且都可回落到冻结 D13 关系。 -/
theorem leadingLegalTrace_two_of_pivot {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hne : T 0 0 ≠ 0) :
    Rho5.LeadingTrace.LeadingLegalTrace T
      [|T 0 0|, |Rho5.PivotReindex.pivotSchur T 0 0 0 0|] :=
  Rho5.LeadingTrace.LeadingLegalTrace.step hmax hne
    (leadingLegalTrace_one (Rho5.PivotReindex.pivotSchur T 0 0))

/-- **目标 2（D40 首位置口径，正主元写法）**：`0 < T 0 0` 时首项写成 `T 0 0`。 -/
theorem leadingLegalTrace_two_of_pivot_pos {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hpos : 0 < T 0 0) :
    Rho5.LeadingTrace.LeadingLegalTrace T
      [T 0 0, |Rho5.PivotReindex.pivotSchur T 0 0 0 0|] := by
  simpa [abs_of_pos hpos] using leadingLegalTrace_two_of_pivot hmax (ne_of_gt hpos)

/-! ## 3. 目标 3：实际路径峰值、`E ≤ 2*r` 短推论与平衡薄适配 -/

/-- **目标 3（两阶段峰值）**：`tracePeak [a, b] = max a b`，只要 `0 ≤ b`
（真实轨迹的第二项是绝对值，故适用；`0 ≤ b` 不可省，因为空/零阶段峰值的单位元是 `0`）。 -/
theorem tracePeak_two {a b : ℝ} (hb : 0 ≤ b) :
    Rho5.GrowthModel.tracePeak [a, b] = max a b := by
  rw [Rho5.GrowthModel.tracePeak_cons, Rho5.GrowthModel.tracePeak_cons,
    Rho5.GrowthModel.tracePeak_nil, max_eq_left hb]

/-- **目标 3（路径峰值 ≤ 包络，`max` 形式）**：`max r |δ| ≤ E`。左项用 `E` 的定义展开，
右项是目标 1 的精确包络。 -/
theorem tracePeak_two_le_envelope {r s t d : ℝ} (hr : 0 < r) (hd : |d| ≤ r) :
    max r |d - t * s / r| ≤ r + |s * t| / r :=
  max_le (le_add_of_nonneg_right (div_nonneg (abs_nonneg (s * t)) (le_of_lt hr)))
    (abs_delta_le_envelope hr hd)

/-- **目标 3（实际路径峰值 ≤ 包络）**：把前两条拼成真实路径的读数
`tracePeak [r, |δ|] = max r |δ| ≤ E`。 -/
theorem tracePeak_two_envelope {r s t d : ℝ} (hr : 0 < r) (hd : |d| ≤ r) :
    Rho5.GrowthModel.tracePeak [r, |d - t * s / r|] ≤ r + |s * t| / r := by
  rw [tracePeak_two (abs_nonneg _)]
  exact tracePeak_two_le_envelope hr hd

/-- **目标 3（`E ≤ 2*r` 的一般形式）**：只用 `|s| ≤ r`、`|t| ≤ r`、`r > 0`。 -/
theorem envelope_le_two_mul {r s t : ℝ} (hr : 0 < r) (hs : |s| ≤ r) (ht : |t| ≤ r) :
    r + |s * t| / r ≤ 2 * r := by
  have h1 : |s * t| ≤ r * r := by
    rw [abs_mul]
    exact mul_le_mul hs ht (abs_nonneg t) (le_trans (abs_nonneg s) hs)
  have h2 : |s * t| / r ≤ r := by
    rw [div_le_iff₀ hr]
    linarith
  linarith

/-- **目标 3（`E ≤ 2*r` 的 CP 短推论）**：`T` 在 `(0,0)` 有真实完整主元且该主元非零时，
`|s| = |T 0 1| ≤ |T 0 0|`、`|t| = |T 1 0| ≤ |T 0 0|` 正是 CP 定义的两个实例，
无需任何额外假设。 -/
theorem envelope_le_two_mul_of_isCompletePivot {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hne : T 0 0 ≠ 0) :
    |T 0 0| + |T 0 1 * T 1 0| / |T 0 0| ≤ 2 * |T 0 0| :=
  envelope_le_two_mul (abs_pos.mpr hne) (hmax 0 1) (hmax 1 0)

/-- **目标 3（`E ≤ 2*r` 的 CP 短推论，正主元写法）**：与卡上 `r = T 0 0 > 0` 的记号一致。 -/
theorem envelope_le_two_mul_of_isCompletePivot_pos {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hpos : 0 < T 0 0) :
    T 0 0 + |T 0 1 * T 1 0| / T 0 0 ≤ 2 * T 0 0 := by
  simpa [abs_of_pos hpos] using envelope_le_two_mul_of_isCompletePivot hmax (ne_of_gt hpos)

/-- **目标 3（平衡薄适配）**：`d = -r` 且 `s*t ≥ 0` 时 `|δ| = r + s*t/r`，即最后主元
绝对值取 B24 的 `F` 形式。这里**只做同一尾块内的等号重写**：不声称 `d = -r` 可由外层
合法性推出、也不声称该平衡变形保持此前阶段的 CP/原盒合法。 -/
theorem abs_delta_eq_of_balanced {r s t d : ℝ} (hr : 0 < r) (hd : d = -r) (hst : 0 ≤ s * t) :
    |d - t * s / r| = r + s * t / r := by
  subst hd
  have hts : 0 ≤ t * s := by rwa [mul_comm t s]
  have hc : 0 ≤ t * s / r := div_nonneg hts (le_of_lt hr)
  have hpos : 0 ≤ r + t * s / r := add_nonneg (le_of_lt hr) hc
  have h1 : -r - t * s / r = -(r + t * s / r) := by ring
  rw [h1, abs_neg, abs_of_nonneg hpos]
  ring

/-- **目标 3（平衡薄适配，接真实 D10 条目）**：把上一条接到真实 `pivotSchur` 条目：
`T 1 1 = -T 0 0` 且 `0 ≤ T 0 1 * T 1 0` 时 `|δ| = T 0 0 + T 0 1 * T 1 0 / T 0 0`。 -/
theorem abs_pivotSchur_eq_of_balanced {T : Matrix (Fin 2) (Fin 2) ℝ} (hpos : 0 < T 0 0)
    (hd : T 1 1 = -T 0 0) (hst : 0 ≤ T 0 1 * T 1 0) :
    |Rho5.PivotReindex.pivotSchur T 0 0 0 0| = T 0 0 + T 0 1 * T 1 0 / T 0 0 := by
  rw [delta_eq_pivotSchur_zero_zero]
  exact abs_delta_eq_of_balanced hpos hd hst

/-- **目标 3（真实路径与 CP 前提下的合并读数）**：把目标 2 的真实迹、目标 3 的峰值等式与
目标 1 的包络合成一条：`T 0 0 > 0` 且 `T` 在 `(0,0)` 有完整主元时，

`tracePeak [T 0 0, |pivotSchur T 0 0 0 0|] ≤ T 0 0 + |T 0 1 * T 1 0| / T 0 0`。

`|d| ≤ r` 由 CP 在 `(1,1)` 的实例给出，不额外假设。 -/
theorem tracePeak_two_of_pivot_le_envelope {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hpos : 0 < T 0 0) :
    Rho5.GrowthModel.tracePeak [T 0 0, |Rho5.PivotReindex.pivotSchur T 0 0 0 0|]
      ≤ T 0 0 + |T 0 1 * T 1 0| / T 0 0 := by
  have hd : |T 1 1| ≤ T 0 0 := by simpa [abs_of_pos hpos] using hmax 1 1
  have h := tracePeak_two_envelope (r := T 0 0) (s := T 0 1) (t := T 1 0) (d := T 1 1)
    hpos hd
  rwa [← delta_eq_pivotSchur_zero_zero] at h

/-- **目标 3（最终短读数）**：与上一条同样的假设下，
`tracePeak [T 0 0, |pivotSchur T 0 0 0 0|] ≤ 2 * T 0 0`，直接由 `E ≤ 2*r` 的 CP
短推论得到；这是本卡能给出的最强“二阶尾块增长上界”，不含任何全局可行性声明。 -/
theorem tracePeak_two_of_pivot_le_two_mul {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hpos : 0 < T 0 0) :
    Rho5.GrowthModel.tracePeak [T 0 0, |Rho5.PivotReindex.pivotSchur T 0 0 0 0|]
      ≤ 2 * T 0 0 :=
  (tracePeak_two_of_pivot_le_envelope hmax hpos).trans
    (envelope_le_two_mul_of_isCompletePivot_pos hmax hpos)

/-- **目标 2 + 目标 3（实际路径存在性读数）**：`T 0 0 > 0` 且 `T` 在 `(0,0)` 有完整主元时，
**存在**一条真实 D13 合法迹，其峰值不超过 `2 * T 0 0`。这条把目标 2 的真实迹与目标 3 的
包络接在一起：见证正是 `[T 0 0, |pivotSchur T 0 0 0 0|]`。仍然只是**二阶尾块内部**的读数，
不含任何“平衡变形保持外层合法”或全局 alpha 声明。 -/
theorem exists_legalTrace_peak_le_two_mul {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hmax : Rho5.Pivot.IsCompletePivot T 0 0) (hpos : 0 < T 0 0) :
    ∃ values : List ℝ, Rho5.CompletePivotPath.LegalTrace T values ∧
      Rho5.GrowthModel.tracePeak values ≤ 2 * T 0 0 :=
  ⟨[T 0 0, |Rho5.PivotReindex.pivotSchur T 0 0 0 0|],
    legalTrace_two_of_pivot_pos hmax hpos, tracePeak_two_of_pivot_le_two_mul hmax hpos⟩

end Rho5.TailEnvelope
