/-
D96 — 最终等式的四面端点装配接口：具名的四条未付端点义务
==========================================================

本文件**只做接口**：把外脑最终需要填的数学义务写成**四条各自显式量化**的实际
`PolyCP` 域端点界，并给出「更强的统一定理如何推出这四条」的归约引理。这里没有新证明
技巧、没有 `RootSpec`、没有抽象未定义模型、也没有把四面合并成一个平衡面。

四条义务对应 D70 `SchurFaces` 的四个析取项（顺序完全一致）：

1. `M 4 4 = -1`（原矩阵本身的最后一行列饱和）；
2. `S4 M 3 3 = -p M`（`S4 M` 是 `M` 的实际 Schur/B24 提取矩阵）；
3. `S3 M 2 2 = -k M`（`S3 M` 同上）；
4. `T2 M 1 1 = -r M`（`T2 M` 是尾块提取矩阵）。

每一面都要求：原矩阵 `M : Matrix5`、`M 0 0 = 1`、`PolyCP M`、排序前提
`0 ≤ m4 M 0 1 ≤ m4 M 1 0`，以及该面的原方程；结论是该矩阵的**原行列式**被
`alpha * C M` 控制，其中 `C M` 是 D67 的实际四阶边框子式（`Rho5.MinorGrowthThreshold.C`），
`alpha` 是 D09 的实际常数（D82 已验证它是实际达到值）。

**不假定**任何点属于 V43 立方体，**不假定**平衡，**不合并**为单一平衡面。
-/
import Rho5.Shared.MinorCPDomain
import Rho5.Shared.MinorGrowthThreshold
import Rho5.Shared.MinorBoundaryFaces
import Rho5.Algebraic.AlphaRoot.Root
import Rho5.Certificate.B24Extraction

namespace Rho5.Shared.FinalEndpointAssembly

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r)
open Rho5.MinorCPDomain (PolyCP)

/-- **四条未付端点义务**（外脑最终只需填这一个结构）。每条都是独立的、全量词显式的
端点界；结构与 D70 `SchurFaces` 的四个析取项一一对应。 -/
structure FourFaceEndpointBounds : Prop where
  /-- 面 1：`M 4 4 = -1`。 -/
  face1 : ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
    0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
      Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
        M 4 4 = -1 →
          |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M
  /-- 面 2：`S4 M 3 3 = -p M`（`S4 M` 为实际 Schur 提取矩阵）。 -/
  face2 : ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
    0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
      Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
        S4 M 3 3 = -p M →
          |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M
  /-- 面 3：`S3 M 2 2 = -k M`。 -/
  face3 : ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
    0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
      Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
        S3 M 2 2 = -k M →
          |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M
  /-- 面 4：`T2 M 1 1 = -r M`（`T2 M` 为实际尾块提取矩阵）。 -/
  face4 : ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
    0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
      Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
        T2 M 1 1 = -r M →
          |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M

/-- **归约（排序四面域上的单一 det 界 ⟹ 四条义务）**：外脑若给出更强的统一定理——
在整个排序四面域上只证一条 `|det M| ≤ alpha * C M`——则四条义务全部得到。 -/
theorem fourFaceEndpointBounds_of_boundaryFace_bound
    (h : ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
      0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
        Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
          Rho5.MinorBoundaryFaces.BoundaryFace M →
            |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M) :
    FourFaceEndpointBounds where
  face1 M h00 hpoly hm1 hm2 h44 :=
    h M h00 hpoly hm1 hm2
      ((Rho5.MinorBoundaryFaces.boundaryFace_iff_schurFaces_of_polyCP M h00 hpoly).mpr
        (Or.inl h44))
  face2 M h00 hpoly hm1 hm2 h4 :=
    h M h00 hpoly hm1 hm2
      ((Rho5.MinorBoundaryFaces.boundaryFace_iff_schurFaces_of_polyCP M h00 hpoly).mpr
        (Or.inr (Or.inl h4)))
  face3 M h00 hpoly hm1 hm2 h3 :=
    h M h00 hpoly hm1 hm2
      ((Rho5.MinorBoundaryFaces.boundaryFace_iff_schurFaces_of_polyCP M h00 hpoly).mpr
        (Or.inr (Or.inr (Or.inl h3))))
  face4 M h00 hpoly hm1 hm2 h2 :=
    h M h00 hpoly hm1 hm2
      ((Rho5.MinorBoundaryFaces.boundaryFace_iff_schurFaces_of_polyCP M h00 hpoly).mpr
        (Or.inr (Or.inr (Or.inr h2))))

/-- **归约（全域单一 det 界 ⟹ 四条义务）**：更强的全域版本（目标 A 的右端）当然也足够。 -/
theorem fourFaceEndpointBounds_of_det_endpoint
    (h : ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
      |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M) :
    FourFaceEndpointBounds where
  face1 M h00 hpoly _ _ _ := h M h00 hpoly
  face2 M h00 hpoly _ _ _ := h M h00 hpoly
  face3 M h00 hpoly _ _ _ := h M h00 hpoly
  face4 M h00 hpoly _ _ _ := h M h00 hpoly

end Rho5.Shared.FinalEndpointAssembly
