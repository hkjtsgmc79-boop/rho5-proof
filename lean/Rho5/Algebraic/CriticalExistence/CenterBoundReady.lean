/-
D47 — G04 `concrete_center` 独立修复：半径读取与终点不等式（ready 辅助模块）
================================================================================

阻塞（D30 六种同根因尝试已冻结，见 `inputs/NOTES_INSTANCE_PRECHECK.md`）：原目标

  `theorem concrete_center (i : Fin 4) :
      |(newtonExpr i).eval midpoint - midpoint i| ≤ radius i / 2`

在 `i = 0/1` 可通过、`i = 2/3` 残留 `↑(![…] 2)` 形态的向量字面量应用。

**根因（本卡独立查明，可复现）**：`radQ : Fin 4 → ℚ := ![a,b,c,d]` 是函数型向量字面量，
其应用 `![…] k` **不能**被 `norm_num` / `simp only [Matrix.cons_val*]` / `push_cast`
约化（小向量 `![1,2,3,4] 2 = 3` 上同样失败：`norm_num`/`simp` 失败而 `rfl` 成功）。
因此算术求值从未开始——问题不在 ℝ 上的强制转换本身，而在于转换之内那个未被 δ-约化的
向量应用。六种旧形态都在让 `norm_num`/`simp` 去看穿这个应用，所以同根因全部失败。

**新路线（本模块）**：先把半径读取在 ℚ 层付清（`rfl` 级定义约化，使用 Data.lean 中的
原字面分母），再把 ℝ 层的终点不等式交给 `norm_num`——此时目标里只剩闭有理字面量，
`norm_num` 可以正常求值。全程复用已验的 Circuit 与 CenterBounds，不重做证书。

交付接口（namespace `Rho5.Algebraic.CriticalExistence.CenterBoundReady`）：
* `radQ_*` / `radius_*`：原 `radQ` 的四项读取等式（字面形式由 `rfl` 给出，幂形式另附）；
* `centerBound12255/12269/12283/12297`：恰好是原证明 `h.trans` 所需的类型
  `↑(max |cvNNNNN.lo| |cvNNNNN.hi|) ≤ radius i / 2`；
* `centerBranch*`：`change` 之后的整支目标 `|eNNNNN.eval midpoint| ≤ radius i / 2`；
* `concrete_center_ready`：**原目标的完整陈述**，仅用上述 ready 引理证明。

无 `sorry`/`admit`/`native_decide`/项目 axiom；不改动 D30/D31 任何源。
-/
import Rho5.Algebraic.CriticalExistence.Circuit
import Rho5.Algebraic.CriticalExistence.CenterBounds

namespace Rho5.Algebraic.CriticalExistence.CenterBoundReady

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 262144

/-! ## 1. `radQ` 读取等式（ℚ 层，字面形式由定义约化 `rfl` 给出） -/

theorem radQ_zero : radQ 0 = (1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := rfl
theorem radQ_one : radQ 1 = (1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := rfl
theorem radQ_two : radQ 2 = (1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := rfl
theorem radQ_three : radQ 3 = (1 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := rfl

/-! ### 幂形式的同一读取（便于阅读与下游引用） -/

theorem radQ_zero_pow : radQ 0 = (1 : ℚ) / 10 ^ 180 := by
  rw [show radQ 0 = (1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 from rfl]; norm_num
theorem radQ_one_pow : radQ 1 = (1 : ℚ) / 10 ^ 180 := by
  rw [show radQ 1 = (1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 from rfl]; norm_num
theorem radQ_two_pow : radQ 2 = (1 : ℚ) / 10 ^ 180 := by
  rw [show radQ 2 = (1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 from rfl]; norm_num
theorem radQ_three_pow : radQ 3 = (1 : ℚ) / (2 * 10 ^ 200) := by
  rw [show radQ 3 = (1 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 from rfl]; norm_num

/-! ## 2. `radius` 读取等式（经 `radius = fun i => (radQ i : ℝ)` 传到 ℝ） -/

theorem radius_zero : radius 0 = (((1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  simp only [radius]; rw [radQ_zero]
theorem radius_one : radius 1 = (((1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  simp only [radius]; rw [radQ_one]
theorem radius_two : radius 2 = (((1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  simp only [radius]; rw [radQ_two]
theorem radius_three : radius 3 = (((1 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  simp only [radius]; rw [radQ_three]

theorem radius_zero_pow : radius 0 = (((1 : ℚ) / 10 ^ 180 : ℚ) : ℝ) := by
  simp only [radius]; rw [radQ_zero_pow]
theorem radius_one_pow : radius 1 = (((1 : ℚ) / 10 ^ 180 : ℚ) : ℝ) := by
  simp only [radius]; rw [radQ_one_pow]
theorem radius_two_pow : radius 2 = (((1 : ℚ) / 10 ^ 180 : ℚ) : ℝ) := by
  simp only [radius]; rw [radQ_two_pow]
theorem radius_three_pow : radius 3 = (((1 : ℚ) / (2 * 10 ^ 200) : ℚ) : ℝ) := by
  simp only [radius]; rw [radQ_three_pow]

/-! ## 3. 终点不等式：恰好是原证明 `h.trans` 所缺的那一步

`h : |eNNNNN.eval midpoint| ≤ ↑(max |cvNNNNN.lo| |cvNNNNN.hi|)`（由 `QI.abs_le_of_mem` 与
已验 `centerNNNNN` 给出），原目标右端是 `radius i / 2`。以下四条的**类型就是**
`h.trans` 需要的 `↑(max …) ≤ radius i / 2`。 -/

theorem centerBound12255 : ((max |cv12255.lo| |cv12255.hi| : ℚ) : ℝ) ≤ radius 0 / 2 := by
  rw [radius_zero]; norm_num [cv12255]
theorem centerBound12269 : ((max |cv12269.lo| |cv12269.hi| : ℚ) : ℝ) ≤ radius 1 / 2 := by
  rw [radius_one]; norm_num [cv12269]
theorem centerBound12283 : ((max |cv12283.lo| |cv12283.hi| : ℚ) : ℝ) ≤ radius 2 / 2 := by
  rw [radius_two]; norm_num [cv12283]
theorem centerBound12297 : ((max |cv12297.lo| |cv12297.hi| : ℚ) : ℝ) ≤ radius 3 / 2 := by
  rw [radius_three]; norm_num [cv12297]

/-- 同上，但半径读取走显式数值形式（`1/10^180`、`1/(2·10^200)`）。 -/
theorem centerBound12255_pow : ((max |cv12255.lo| |cv12255.hi| : ℚ) : ℝ) ≤ radius 0 / 2 := by
  rw [radius_zero_pow]; norm_num [cv12255]
theorem centerBound12269_pow : ((max |cv12269.lo| |cv12269.hi| : ℚ) : ℝ) ≤ radius 1 / 2 := by
  rw [radius_one_pow]; norm_num [cv12269]
theorem centerBound12283_pow : ((max |cv12283.lo| |cv12283.hi| : ℚ) : ℝ) ≤ radius 2 / 2 := by
  rw [radius_two_pow]; norm_num [cv12283]
theorem centerBound12297_pow : ((max |cv12297.lo| |cv12297.hi| : ℚ) : ℝ) ≤ radius 3 / 2 := by
  rw [radius_three_pow]; norm_num [cv12297]

/-! ## 4. 四支完整目标（`change` 之后的形式），供最薄调用 -/

theorem centerBranch12255 : |e12255.eval midpoint| ≤ radius 0 / 2 :=
  (QI.abs_le_of_mem (center12255 midpoint midpoint_mem_point)).trans centerBound12255
theorem centerBranch12269 : |e12269.eval midpoint| ≤ radius 1 / 2 :=
  (QI.abs_le_of_mem (center12269 midpoint midpoint_mem_point)).trans centerBound12269
theorem centerBranch12283 : |e12283.eval midpoint| ≤ radius 2 / 2 :=
  (QI.abs_le_of_mem (center12283 midpoint midpoint_mem_point)).trans centerBound12283
theorem centerBranch12297 : |e12297.eval midpoint| ≤ radius 3 / 2 :=
  (QI.abs_le_of_mem (center12297 midpoint midpoint_mem_point)).trans centerBound12297

/-! ## 5. 原目标完整陈述（供 D30 直接薄引用） -/

theorem concrete_center_ready (i : Fin 4) :
    |(newtonExpr i).eval midpoint - midpoint i| ≤ radius i / 2 := by
  rw [delta_formula]
  fin_cases i
  · have h := QI.abs_le_of_mem (center12255 midpoint midpoint_mem_point)
    change |e12255.eval midpoint| ≤ radius 0/2
    exact h.trans centerBound12255
  · have h := QI.abs_le_of_mem (center12269 midpoint midpoint_mem_point)
    change |e12269.eval midpoint| ≤ radius 1/2
    exact h.trans centerBound12269
  · have h := QI.abs_le_of_mem (center12283 midpoint midpoint_mem_point)
    change |e12283.eval midpoint| ≤ radius 2/2
    exact h.trans centerBound12283
  · have h := QI.abs_le_of_mem (center12297 midpoint midpoint_mem_point)
    change |e12297.eval midpoint| ≤ radius 3/2
    exact h.trans centerBound12297

end
end Rho5.Algebraic.CriticalExistence.CenterBoundReady
