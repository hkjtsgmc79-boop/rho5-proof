/-
D35 — 编译例子：末端不多加 `0`
================================

**卡目标 4（例子）**：`n = 0`、零 `1×1`、非零 `1×1` 三个编译例子，用来核对
(a) 补零轨迹长度恰为阶数、(b) `0×0` 的 `[]` 与正阶零矩阵的 `[0]` 分别对应原关系的
`empty` 与 `zeroStop`、(c) 非零 `1×1` 的轨迹就是 `[|a|]`，末尾**没有**多加 `0`。

全部例子都是 `example`（不产生新公理），编译即检查。
-/
import Rho5.Shared.PaddedTrace.Peak

namespace Rho5.PaddedTrace

open Rho5 Rho5.GrowthModel

/-! ## `n = 0`：唯一轨迹是 `[]`（对应原构造器 `LegalTrace.empty`） -/

example : PaddedLegalTrace (0 : Matrix (Fin 0) (Fin 0) ℝ) [] := PaddedLegalTrace.empty

example {padded : List ℝ} (h : PaddedLegalTrace (0 : Matrix (Fin 0) (Fin 0) ℝ) padded) :
    padded = [] :=
  padded_zero_eq_replicate h

example {padded : List ℝ} (h : PaddedLegalTrace (0 : Matrix (Fin 0) (Fin 0) ℝ) padded) :
    padded.length = 0 := padded_length h

/-! ## 零 `1×1`：轨迹恰为 `[0]`（对应原构造器 `LegalTrace.zeroStop`，值 `[0]`） -/

example : PaddedLegalTrace (0 : Matrix (Fin 1) (Fin 1) ℝ) [0] :=
  padded_zero_replicate 1

example {padded : List ℝ} (h : PaddedLegalTrace (0 : Matrix (Fin 1) (Fin 1) ℝ) padded) :
    padded = [0] :=
  padded_zero_eq_replicate h

example : Rho5.GrowthModel.tracePeak ([0] : List ℝ) = 0 :=
  tracePeak_replicate_zero 1

/-! ## 非零 `1×1`：轨迹恰为 `[|a|]`，长度 `1`，末端不多加 `0` -/

example (a : ℝ) : PaddedLegalTrace (fun _ _ : Fin 1 => a) [|a|] := by
  have htail : PaddedLegalTrace
      (Rho5.PivotReindex.pivotSchur (fun _ _ : Fin 1 => a) 0 0) [] := by
    have h : Rho5.PivotReindex.pivotSchur (fun _ _ : Fin 1 => a) 0 0 = 0 :=
      Subsingleton.elim _ _
    rw [h]
    exact PaddedLegalTrace.empty
  have h := PaddedLegalTrace.step (A := fun _ _ : Fin 1 => a) 0 0
    (by intro i j; simp) htail
  simpa using h

example (a : ℝ) {padded : List ℝ}
    (h : PaddedLegalTrace (fun _ _ : Fin 1 => a) padded) : padded.length = 1 :=
  padded_length h

/-- 非零 `1×1` 的补零轨迹长度恰好是 `1`，所以它不能是 `[|a|, 0]` 这类多补零的列表：
长度检查是最直接的“末端不多加 0”验证。 -/
example (a : ℝ) {padded : List ℝ}
    (h : PaddedLegalTrace (fun _ _ : Fin 1 => a) padded) : padded ≠ [|a|, 0] := by
  intro hbad
  have hlen := padded_length h
  rw [hbad] at hlen
  simp at hlen

/-- 非零 `1×1` 的补零轨迹与原轨迹峰值一致（目标 4 在该实例上的核对）。 -/
example (a : ℝ) {padded : List ℝ}
    (h : PaddedLegalTrace (fun _ _ : Fin 1 => a) padded) :
    ∃ values : List ℝ,
      Rho5.CompletePivotPath.LegalTrace (fun _ _ : Fin 1 => a) values
        ∧ tracePeak padded = tracePeak values :=
  exists_legalTrace_peak_eq h

end Rho5.PaddedTrace
