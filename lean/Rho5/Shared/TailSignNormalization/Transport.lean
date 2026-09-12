/-
D53 — 沿真实 Schur 链的符号运输（D22 `pivotSchur_signedEntries` 逐阶应用）
=============================================================================

给定真实 `M : Matrix5` 与末位行/列符号 `sigma5 ε`/`sigma5 η`，令
`N = signedEntries M (sigma5 ε) (sigma5 η)`。本模块用 D22 的**真实** Schur 符号运输
`pivotSchur_signedEntries`（带显式非零前提 `M 0 0 ≠ 0`、`p M ≠ 0`、`k M ≠ 0`）逐阶得到

* `S4 N = signedEntries (S4 M) (sigma4 ε) (sigma4 η)`；
* `S3 N = signedEntries (S3 M) (sigma3 ε) (sigma3 η)`；
* `T2 N = signedEntries (T2 M) (sigma2 ε) (sigma2 η)`（真实 D37 同名 Schur 定义）；

于是 `p N = p M`、`k N = k M`、`r N = r M`，而末位的 `s`/`t`/`d` 分别只被列/行末位符号
乘上：`s N = η * s M`、`t N = ε * t M`、`T2 N 1 1 = ε * η * (T2 M 1 1)`。

没有平衡尾块假设，也没有新增非零前提：三个非零前提是**真实 Schur 运输本身**要求的，
在本卡中由 `M 0 0 = 1`、`p M > 0`、`k M > 0` 提供。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.TailSignNormalization.Signs
import Rho5.Shared.LeadingTrace
import Rho5.Certificate.B24Extraction.Extract

namespace Rho5.TailSignNormalization

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **D22 运输（阶 5 → 4）**：末位符号整矩阵的 `(0,0)` Schur 更新就是原 `S4` 上的同型符号变换，
末位下标降到 3（`sigma4`）。 -/
theorem S4_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) :
    S4 (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) =
      Rho5.TraceSigns.signedEntries (S4 M) (sigma4 ε) (sigma4 η) := by
  have h1 : (fun i : Fin 4 => sigma5 ε (Rho5.PivotReindex.remainingIndex (0 : Fin 5) i)) =
      sigma4 ε := by
    funext i
    rw [Rho5.LeadingTrace.remainingIndex_zero]
    exact congrFun (tail_sigma5 ε) i
  have h2 : (fun j : Fin 4 => sigma5 η (Rho5.PivotReindex.remainingIndex (0 : Fin 5) j)) =
      sigma4 η := by
    funext j
    rw [Rho5.LeadingTrace.remainingIndex_zero]
    exact congrFun (tail_sigma5 η) j
  rw [S4, S4, Rho5.TraceSigns.pivotSchur_signedEntries M (isSign_sigma5 hε) (isSign_sigma5 hη)
    0 0 h00, h1, h2]

/-- **D22 运输（阶 4 → 3）**：需要 `S4 M 0 0 = p M ≠ 0`。 -/
theorem S3_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) :
    S3 (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) =
      Rho5.TraceSigns.signedEntries (S3 M) (sigma3 ε) (sigma3 η) := by
  have h1 : (fun i : Fin 3 => sigma4 ε (Rho5.PivotReindex.remainingIndex (0 : Fin 4) i)) =
      sigma3 ε := by
    funext i
    rw [Rho5.LeadingTrace.remainingIndex_zero]
    exact congrFun (tail_sigma4 ε) i
  have h2 : (fun j : Fin 3 => sigma4 η (Rho5.PivotReindex.remainingIndex (0 : Fin 4) j)) =
      sigma3 η := by
    funext j
    rw [Rho5.LeadingTrace.remainingIndex_zero]
    exact congrFun (tail_sigma4 η) j
  rw [S3, S3, S4_signedEntries M hε hη h00,
    Rho5.TraceSigns.pivotSchur_signedEntries (S4 M) (isSign_sigma4 hε) (isSign_sigma4 hη)
      0 0 hp, h1, h2]

/-- **D22 运输（阶 3 → 2）**：需要 `S3 M 0 0 = k M ≠ 0`。 -/
theorem T2_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) :
    T2 (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) =
      Rho5.TraceSigns.signedEntries (T2 M) (sigma2 ε) (sigma2 η) := by
  have h1 : (fun i : Fin 2 => sigma3 ε (Rho5.PivotReindex.remainingIndex (0 : Fin 3) i)) =
      sigma2 ε := by
    funext i
    rw [Rho5.LeadingTrace.remainingIndex_zero]
    exact congrFun (tail_sigma3 ε) i
  have h2 : (fun j : Fin 2 => sigma3 η (Rho5.PivotReindex.remainingIndex (0 : Fin 3) j)) =
      sigma2 η := by
    funext j
    rw [Rho5.LeadingTrace.remainingIndex_zero]
    exact congrFun (tail_sigma3 η) j
  rw [T2, T2, S3_signedEntries M hε hη h00 hp,
    Rho5.TraceSigns.pivotSchur_signedEntries (S3 M) (isSign_sigma3 hε) (isSign_sigma3 hη)
      0 0 hk, h1, h2]

/-! ## 四个真实坐标的读数 -/

/-- `p N = p M`：末位符号在 `(0,0)` 处都是 `1`。 -/
theorem p_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) :
    p (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) = p M := by
  rw [p, S4_signedEntries M hε hη h00, p, Rho5.TraceSigns.signedEntries_apply]
  simp

/-- `k N = k M`。 -/
theorem k_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) :
    k (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) = k M := by
  rw [k, S3_signedEntries M hε hη h00 hp, k, Rho5.TraceSigns.signedEntries_apply]
  simp

/-- `r N = r M`。 -/
theorem r_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) :
    r (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) = r M := by
  rw [r, T2_signedEntries M hε hη h00 hp hk, r, Rho5.TraceSigns.signedEntries_apply]
  simp

/-- `s N = η * s M`：二阶尾块 `(0,1)` 只带**列**末位符号。 -/
theorem s_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) :
    s (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) = η * s M := by
  rw [s, T2_signedEntries M hε hη h00 hp hk, s, Rho5.TraceSigns.signedEntries_apply]
  simp [mul_comm]

/-- `t N = ε * t M`：二阶尾块 `(1,0)` 只带**行**末位符号。 -/
theorem t_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) :
    t (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) = ε * t M := by
  rw [t, T2_signedEntries M hε hη h00 hp hk, t, Rho5.TraceSigns.signedEntries_apply]
  simp

/-- `d N = ε * η * d M`（`d = T2 · 1 1`）：二阶尾块 `(1,1)` 同时带行、列末位符号。 -/
theorem d_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) :
    T2 (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) 1 1 = ε * η * (T2 M 1 1) := by
  rw [T2_signedEntries M hε hη h00 hp hk, Rho5.TraceSigns.signedEntries_apply]
  simp [mul_comm, mul_left_comm, mul_assoc]

end Rho5.TailSignNormalization
