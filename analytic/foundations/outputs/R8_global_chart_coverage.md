# R8：D/X 核心饱和与全局根盒覆盖

日期：2026-08-19

## 0. 结论与证明状态

本轮把 R3、R4 中的“无损限制到 D/X 饱和核心”补成了一个含退化情形、
符号规范化、转置边界和闭根盒的构造性证明。

严格结论是：给定任意归一化、固定顺序完全主元的三阶核心 \(C\)，以及
任意可行的两步提升见证，存在只压缩核心第二行、第二列的对角压缩，把它
送到

\[
\mathcal B_D:\ |w|=|r|
\qquad\text{或}\qquad
\mathcal B_X:\ |s|=|t|=|r|,                    \tag{0.1}
\]

同时：

1. 原来的提升尺度 \(p_3\) 仍然可行；
2. 核心仍按同一固定顺序完全主元；
3. 最后主元 \(q(C)\) 不变；
4. 若原点是反例，压缩后的点仍是数值完全相同的反例。

所以需要覆盖的不是通用八维核心盒，而只是四个 D 根盒和八个 X 根盒。
这完成的是全局证明的**无损降维入口**，不是全局不等式本身。

这里不会漏掉在较早阶段取得的增长。独立的
`R8_scalar_root_bounds.md` 对三阶尖锐包络作两次嵌套应用，证明任意规范
完全主元五阶矩阵的前四个主元均不超过 (4)。由于目标常数
(alpha>4)，任何增长超过 (alpha) 的反例必由第五主元
(p_5=p_3q(C)) 产生。因此本报告只为最后核心主元建立根盒是一个已证明的
归约，而不是额外假设。

有一个措辞必须特别精确：该构造证明“每个点都能被送到一个不更差的饱和
点”，并不证明原来的极大点自身已经饱和；也不证明压缩前后
\(\operatorname{Cap}\) 相等，只证明压缩后容量不减。

---

## 1. 固定顺序核心坐标

通过核心内部的独立行、列符号变换，可令 \(C_{11}=1\)，并令第一行、第一列
其余四项非负。写

\[
C=C(a,b,c,d,r,s,t,w)=
\begin{bmatrix}
1&a&b\\
c&ca+r&cb+s\\
d&da+t&db+w
\end{bmatrix},                                  \tag{1.1}
\]

其中

\[
a,b,c,d\in[0,1],\qquad
S=\begin{bmatrix}r&s\\t&w\end{bmatrix}.          \tag{1.2}
\]

这里 \(S\) 是消去核心第一主元后的二阶 Schur 尾。固定顺序完全主元条件正好
包括

\[
|C_{ij}|\le1,\qquad |s|,|t|,|w|\le|r|.           \tag{1.3}
\]

若 \(r\ne0\)，带符号的最后主元与其绝对值为

\[
h(C)=w-\frac{ts}{r},\qquad q(C)=|h(C)|.           \tag{1.4}
\]

若 \(r=0\)，(1.3) 强制 \(s=t=w=0\)。在这个退化面定义

\[
\widetilde q(C)=0,                                \tag{1.5}
\]

这正是 \(q\) 的连续延拓。任何正目标值、等号候选或反例都不在这个退化面。

由 \(C_{ij}\in[-1,1]\) 及 \(a,b,c,d\in[0,1]\)，每个 Schur 坐标都满足独立的
尖锐轴界

\[
r,s,t,w\in[-2,1].                                 \tag{1.6}
\]

例如 \(r=C_{22}-ca\in[-2,1]\)，其余三项相同。这比仅写
\([-2,2]\) 更适合作为根盒。

---

## 2. 提升集合的对角压缩封闭性

设 \(p_3C\) 有一个精确两步提升见证

\[
W=(a_0,b_0,u,v,x,y,p_2,p_3),
\]

第二主元符号已经由早先证明的行符号对称性规范为 \(+1\)。取任意对角矩阵

\[
R=\operatorname{diag}(\rho_1,\rho_2,\rho_3),
\quad
K=\operatorname{diag}(\kappa_1,\kappa_2,\kappa_3),
\quad
0\le \rho_i,\kappa_j\le1.                       \tag{2.1}
\]

对应的完整五阶矩阵是

\[
A(W,C)=
\begin{bmatrix}
1&a_0&v^T\\
b_0&a_0b_0+p_2&(b_0v+p_2y)^T\\
u&a_0u+p_2x&p_3C+uv^T+p_2xy^T
\end{bmatrix}.                                   \tag{2.2}
\]

把见证改成

\[
u'=Ru,\quad x'=Rx,\qquad v'=Kv,\quad y'=Ky,       \tag{2.3}
\]

核心改成 \(C'=RCK\)，而 \(a_0,b_0,p_2,p_3\) 不变。两组耦合尾块逐项变为

\[
p_3C'+p_2x'(y')^T=R(p_3C+p_2xy^T)K,              \tag{2.4}
\]

\[
p_3C'+u'(v')^T+p_2x'(y')^T
=R(p_3C+uv^T+p_2xy^T)K.                           \tag{2.5}
\]

令

\[
\widehat R=\operatorname{diag}(1,1,R),\qquad
\widehat K=\operatorname{diag}(1,1,K).            \tag{2.6}
\]

则上述变换不是形式类比，而是完整矩阵恒等式

\[
A(W',C')=\widehat R\,A(W,C)\,\widehat K.          \tag{2.7}
\]

所以第一阶段所有条目只被模不超过一的行列因子压缩，第一主元 \(p_1=1\)
不变。第一步 Schur 尾和第二步 Schur 尾满足

\[
A'^{(2)}
=\operatorname{diag}(1,R)\,A^{(2)}\,
 \operatorname{diag}(1,K),                       \tag{2.8}
\]

\[
A'^{(3)}=R\,A^{(3)}K=p_3RCK.                     \tag{2.9}
\]

因此第二阶段所有非主元条目也只会缩小，\(p_2\) 不变。一般的 \(R,K\)
说明“可提升 Schur 块”对任意独立对角压缩封闭；本报告实际使用的
\(R_\lambda,K_\mu\) 的第一个对角元都是 \(1\)，故第三主元
\(p_3\) 也原样不变，且 \(C'_{11}=1\)。

这已经在完整 \(A\) 和全部早期 CP 不等式层证明了封闭性，而不只是核对
三阶核心。特别地，侧边约束分别被一个行因子或列因子压缩，标量约束
\(|a_0b_0+p_2|\le1\) 完全不变。这一步是在原见证上逐项构造，不依赖容量
上确界或连续性。

---

## 3. 构造性 D/X 饱和引理

只压缩核心中与 \(r\) 对应的第二行、第二列：

\[
R_\lambda=\operatorname{diag}(1,\lambda,1),
\qquad
K_\mu=\operatorname{diag}(1,\mu,1),
\qquad 0\le\lambda,\mu\le1.                     \tag{3.1}
\]

由 (1.1) 直接计算，新坐标是

\[
\begin{aligned}
a'&=\mu a,& b'&=b,& c'&=\lambda c,& d'&=d,\\
r'&=\lambda\mu r,& s'&=\lambda s,&
t'&=\mu t,& w'&=w.
\end{aligned}                                    \tag{3.2}
\]

因此尾块为

\[
S'=\begin{bmatrix}
\lambda\mu r&\lambda s\\
\mu t&w
\end{bmatrix}.                                   \tag{3.3}
\]

### 3.1 非退化构造

设 \(r\ne0\)，并记

\[
\sigma=\left|\frac{s}{r}\right|,
\qquad
\tau=\left|\frac{t}{r}\right|,
\qquad
\upsilon=\left|\frac{w}{r}\right|.              \tag{3.4}
\]

由 (1.3)，三者都在 \([0,1]\)。分两种情形。

**D 情形：** 若 \(\upsilon\ge\sigma\tau\)，令

\[
\lambda=\max\{\tau,\upsilon\},
\qquad
\mu=\frac{\upsilon}{\lambda}.                  \tag{3.5}
\]

当 \(\lambda>0\) 时，\(\lambda\ge\tau\)、\(\mu\ge\sigma\)、
\(\lambda\mu=\upsilon\)，故

\[
|s'|,|t'|\le|r'|,\qquad |w'|=|r'|.               \tag{3.6}
\]

证明 \(\mu\ge\sigma\) 只需分
\(\lambda=\tau\) 与 \(\lambda=\upsilon\)：前者用
\(\upsilon\ge\sigma\tau\)，后者有 \(\mu=1\)。

若 (3.5) 中 \(\lambda=0\)，则 \(t=w=0\)，从而原最后主元也是零；取
\((\lambda,\mu)=(0,1)\) 即可，见退化讨论。

**X 情形：** 若 \(\upsilon\le\sigma\tau\)，令

\[
\lambda=\tau,\qquad\mu=\sigma.                  \tag{3.7}
\]

于是

\[
|s'|=|t'|=|r'|,\qquad |w'|\le|r'|.               \tag{3.8}
\]

等号 \(\upsilon=\sigma\tau\) 时，(3.5) 与 (3.7) 给出同一压缩；所得点同时
位于 D、X 两个边界上。两个 chart 在交面重复覆盖是有意的。

### 3.2 固定顺序完全主元与最后主元

由 (3.6) 或 (3.8)，新尾块仍以 \(r'\) 为第二核心主元；第一阶段矩阵条目由
对角压缩只会减小。因此 \(C'\) 仍按同一固定顺序完全主元。

当 \(\lambda\mu>0\) 时，带符号的最后主元逐字不变：

\[
w'-\frac{t's'}{r'}
=w-\frac{(\mu t)(\lambda s)}{\lambda\mu r}
=w-\frac{ts}{r}.                                 \tag{3.9}
\]

而且若原来的 \(q(C)>0\)，上述构造必有 \(\lambda\mu>0\)：

- D 情形若 \(\lambda\mu=\upsilon=0\)，则
  \(\upsilon\ge\sigma\tau\) 强制 \(\sigma\tau=0\)，所以 \(q=0\)；
- X 情形若 \(\lambda\mu=\sigma\tau=0\)，则
  \(\upsilon\le\sigma\tau\) 强制 \(\upsilon=0\)，所以 \(q=0\)。

因此所有正目标点都可直接使用 (3.9)。零目标退化时，压缩后
\(r'=s'=t'=w'=0\)，用连续延拓 (1.5) 仍有
\(\widetilde q(C')=\widetilde q(C)=0\)。这修补了 R3 中在
\(\lambda\mu=0\) 时仍形式上写除法的边界缺口。

### 3.3 对全局目标的无损性

第 2 节把任意原提升见证 \(W\) 显式送到 \(C'\) 的见证 \(W'\)，且 \(p_3\)
不变；本节又证明 \(q(C')=q(C)\)。所以在见证层面

\[
p_3q(C')=p_3q(C).                                 \tag{3.10}
\]

这两边正是完整五阶消元的最终主元绝对值：

\[
|p_5(A')|=p_3q(C')=p_3q(C)=|p_5(A)|.             \tag{3.11}
\]

在容量语言中只能推出

\[
\operatorname{Cap}(C')\ge\operatorname{Cap}(C),
\qquad
q(C')\operatorname{Cap}(C')
\ge q(C)\operatorname{Cap}(C),                   \tag{3.12}
\]

不应宣称容量相等。反向不等式不需要，也通常没有由压缩构造给出。

因为 D/X 是原可行域的子集，而每个原可行见证又可无损送到 D/X，得到精确
的上确界等式

\[
\sup_{C,W}p_3q(C)
=\sup_{C\in\mathcal B_D\cup\mathcal B_X,\,W}p_3q(C). \tag{3.13}
\]

若从一个全局极大点出发，压缩后的点不可能严格更大，否则原点并非全局极大；
所以至少存在一个 D/X 上的全局极大代表。原极大点本身未必饱和。

---

## 4. 符号、转置、置换与边界

### 4.1 第一行、第一列符号规范化

精确提升表示已经有 \(p_3>0,C_{11}=1\)。选对角符号矩阵

\[
D_R=\operatorname{diag}(1,\delta_2,\delta_3),
\qquad
D_C=\operatorname{diag}(1,\gamma_2,\gamma_3),     \tag{4.1}
\]

依次取 \(\gamma_2,\gamma_3\) 使 \(C\) 的第一行非负，取
\(\delta_2,\delta_3\) 使第一列非负。零条目的符号任取，所得零值相同，
因此不会漏掉边界。第一对角元固定为 \(1\)，故 \(C_{11}=1\) 和 \(p_3\)
不变。

这一步必须、也确实能在完整五阶矩阵上实现。令

\[
\widehat D_R=\operatorname{diag}(1,1,D_R),\qquad
\widehat D_C=\operatorname{diag}(1,1,D_C).        \tag{4.2}
\]

则

\[
\widehat D_R A(W,C)\widehat D_C
=A(W^\#,D_RCD_C),                                \tag{4.3}
\]

其中

\[
u^\#=D_Ru,\quad x^\#=D_Rx,\qquad
v^\#=D_Cv,\quad y^\#=D_Cy,                       \tag{4.4}
\]

而 \(a_0,b_0,p_2,p_3\) 不变。它与 (2.7)--(2.9) 是同一个块矩阵恒等式，
只是对角因子现在为 \(\pm1\)。所以完整 \(A\)、\(A^{(2)}\)、\(A^{(3)}\)
的绝对值 CP 条件都逐项不变，三个早期主元和最终主元绝对值均不变。

在消去 \(a_0,v,y\) 后的坐标中，这个变换明确诱导

\[
\beta=(b_0,u,x,p_2)
\longmapsto
\beta^\#=(b_0,D_Ru,D_Rx,p_2).                    \tag{4.5}
\]

列符号作用在已经被最小化掉的 \(v,y\) 上；上述完整见证恒等式保证相应
Chebyshev 可行点仍存在。因此首行/首列非负不是单独对核心做的非法规范化。
饱和压缩因子非负，所以之后仍保持这个符号规范。

### 4.2 chart 的离散符号

对正目标点 \(r'\ne0\)。D 分支有唯一标签

\[
w'=\varepsilon_w r',\qquad\varepsilon_w\in\{\pm1\}; \tag{4.6}
\]

X 分支有唯一标签

\[
s'=\varepsilon_s r',\qquad
t'=\varepsilon_t r',\qquad
(\varepsilon_s,\varepsilon_t)\in\{\pm1\}^2.      \tag{4.7}
\]

此外必须显式分开 \(r'<0\) 与 \(r'>0\)。这给出 \(2\times2=4\) 个 D 根和
\(4\times2=8\) 个 X 根。第二主元符号已经在完整五阶矩阵层规范为 \(+1\)，
无需再复制一个同构根；保留两份虽安全，但不是必要覆盖责任。

### 4.3 转置不产生第三种 chart

由 (1.1) 精确计算，转置在 Schur 坐标上作用为

\[
(a,b,c,d,r,s,t,w)
\longmapsto(c,d,a,b,r,t,s,w).                    \tag{4.8}
\]

因此 D 根在转置下仍是同一 \(\varepsilon_w\) 的 D 根；X 根只交换
\(\varepsilon_s,\varepsilon_t\)。下面列出的十二个根本身已经对转置封闭，
所以当前覆盖**不使用转置来删根**，也不需要额外 transpose 标签。

如果以后为了提速按转置取商，manifest 必须显式保存轨道展开。尤其在已经
消去 \(a_0,v,y\) 的八维 \(\beta=(b_0,u,x,p_2)\) 表示中，不能未经证明就把
转置理解成 \(\beta\) 坐标的简单置换；安全方案是保留两侧，或在完整提升见证
层使用

\[
(a_0,b_0,u,v,x,y)\leftrightarrow
(b_0,a_0,v,u,y,x).                               \tag{4.9}
\]

### 4.4 行列置换与主元并列

从原五阶矩阵提取核心时，完全主元算法已经把所选主元置于每个尾块左上角，
所以 (1.1) 覆盖每一条固定的合法主元路径。主元并列时任选一条合法路径即可，
饱和构造沿该路径工作。

当前十二根没有用剩余两行或两列交换来删分支。此类交换只有在相应 Schur
条目并列为最大值时才保持同一固定顺序描述；将来若利用它，必须像转置一样
保存显式轨道，不能由 worker 默认等价。

---

## 5. 十二个紧致核心根盒

令 \([\alpha_-,\alpha_+]\) 是目标代数数的已认证有理隔离区间，并定义

\[
\tau_-:=\frac{4\alpha_-}{9},
\qquad
\eta:=\frac{\tau_-}{2}=\frac{2\alpha_-}{9}.      \tag{5.1}
\]

当前隔离区间给出

\[
\tau_-\approx1.836674257169988,\qquad
\eta\approx0.918337128584994.                    \tag{5.2}
\]

这里使用 `R8_scalar_root_bounds.md` 中独立证明的三阶标量定理

\[
p_3\le\frac94,\qquad q(C)\le\frac94.             \tag{5.3}
\]

若 \(p_3q(C)>\alpha\)，或者某个全局极大点的值至少为已知候选值 \(\alpha\)，
则

\[
p_3>\tau_-,\qquad q(C)>\tau_-,
\qquad |r|>\eta,                                 \tag{5.4}
\]

最后一步来自 \(q(C)\le2|r|\)。使用 \(\alpha_-\) 和闭端点只会扩大覆盖，
不会删掉等号点或严格反例。

所有根都有

\[
(a,b,c,d)\in[0,1]^4.                             \tag{5.5}
\]

### 5.1 四个 D 根

在每个根内精确重构 \(w=\varepsilon_w r\)：

| \(\varepsilon_w\) | \(r\) 符号 | \(r\) 根区间 | \(s,t\) 轴区间 |
|---:|:---:|:---:|:---:|
| \(+1\) | \(-\) | \([-2,-\eta]\) | \([-2,1]\) |
| \(+1\) | \(+\) | \([\eta,1]\) | \([-1,1]\) |
| \(-1\) | \(-\) | \([-1,-\eta]\) | \([-1,1]\) |
| \(-1\) | \(+\) | \([\eta,1]\) | \([-1,1]\) |

\(\varepsilon_w=-1\) 时的 \(r\in[-1,1]\) 不是猜测：它是
\(r\in[-2,1]\) 与 \(w=-r\in[-2,1]\) 的精确轴盒交。

根盒内部还必须施加以下闭的精确筛选条件：

\[
\begin{gathered}
|ca+r|,\ |cb+s|,\ |da+t|,\ |db+\varepsilon_wr|\le1,\\
|s|,|t|\le|r|,\\
|\varepsilon_wr^2-ts|\ge\tau_-|r|.              \tag{5.6}
\end{gathered}
\]

最后一行等价于 \(q(C)\ge\tau_-\)，但没有区间除法。

### 5.2 八个 X 根

对每个
\((\varepsilon_s,\varepsilon_t)\in\{\pm1\}^2\)，精确重构

\[
s=\varepsilon_sr,\qquad t=\varepsilon_tr.         \tag{5.7}
\]

| \((\varepsilon_s,\varepsilon_t)\) | \(r\) 符号 | \(r\) 根区间 | \(w\) 轴区间 |
|:---:|:---:|:---:|:---:|
| \((+1,+1)\) | \(-\) | \([-2,-\eta]\) | \([-2,1]\) |
| \((+1,+1)\) | \(+\) | \([\eta,1]\) | \([-1,1]\) |
| 其余三组 | \(-\) | \([-1,-\eta]\) | \([-1,1]\) |
| 其余三组 | \(+\) | \([\eta,1]\) | \([-1,1]\) |

“其余三组”的每一组各给两个根，因此总数是 \(2+3\times2=8\)。只要
\(\varepsilon_s\) 或 \(\varepsilon_t\) 为负，对应的
\(-r\in[-2,1]\) 就把 \(r\) 精确限制到 \([-1,1]\)。

根盒内部的精确筛选条件为

\[
\begin{gathered}
|ca+r|,\ |cb+\varepsilon_sr|,
\ |da+\varepsilon_tr|,\ |db+w|\le1,\\
|w|\le|r|,\\
|w-\varepsilon_s\varepsilon_t r|\ge\tau_-.       \tag{5.8}
\end{gathered}
\]

这里最后主元已经约成

\[
q(C)=|w-\varepsilon_s\varepsilon_t r|.            \tag{5.9}
\]

根盒只是闭的轴对齐 over-cover；(5.6)、(5.8) 是证书树必须检查的真实
半代数域。二者不能混为一谈。

---

## 6. 联合 \(\beta\) 根盒

消去第一提升变量 \(a_0\) 后，使用不与核心坐标 \(b\) 混淆的记号

\[
\beta=(b_0,u_1,u_2,u_3,x_1,x_2,x_3,p_2).         \tag{6.1}
\]

完整无剪枝域原本是

\[
(b_0,u,x)\in[-1,1]^7,\qquad p_2\in(0,2].         \tag{6.2}
\]

第二主元的离散符号只需取 \(+1\)：若原符号为
\(s_2\in\{\pm1\}\)，把完整 \(A\) 的第二行乘以 \(s_2\)，则

\[
(s_2,b_0,y)\longmapsto(1,s_2b_0,s_2y),
\]

其余提升变量不变，所有 CP 绝对值条件及全部主元绝对值不变。因此 trusted
roots 可、也应在 manifest 中统一声明 pivot_sign \(=+1\)，而不是把符号
交给 worker 猜测。

任意潜在反例均落在闭盒

\[
(b_0,u,x)\in[-1,1]^7,
\qquad p_2\in[\eta,2].                            \tag{6.3}
\]

上界 \(p_2\le2\) 来自 \(|a_0b_0+p_2|\le1\)。下界无需调用完整
\(\Phi\) 包络：由核心 \(C_{11}=1\) 对应的第二阶段约束

\[
|p_3+p_2x_1y_1|\le p_2
\]

直接得 \(p_3\le2p_2\)，再结合 \(p_3>\tau_-\) 即得
\(p_2>\eta\)。闭盒写成 \(p_2\ge\eta\) 是安全 over-cover。

盒内仍需检查精确 Helly 条件

\[
\begin{aligned}
p_2&\le1+|b_0|,\\
p_2|x_i|&\le1+|u_i|,\\
p_2|u_i-b_0x_i|&\le|b_0|+|u_i|,\\
p_2|x_iu_k-x_ku_i|&\le|u_i|+|u_k|\quad(i<k).
\end{aligned}                                    \tag{6.4}
\]

因此 proof-relevant 联合根一共有十二个，每个是一个 6/7 维核心根与同一个
八维 \(\beta\) 根的直积，再与 (5.6)/(5.8)、(6.4) 相交。不存在额外 generic
核心根的覆盖责任。

---

## 7. 覆盖定理

**定理。** 假设三阶标量界 (5.3)，且 \(4<\alpha_-\le\alpha\)。若存在
规范完全主元五阶矩阵的增长超过 \(\alpha\)，则该增长由第五主元产生；相应
精确两步提升见证满足

\[
p_3q(C)>\alpha,                                   \tag{7.1}
\]

则十二个 D/X 联合根中至少一个包含另一个精确提升见证，且该见证仍满足
\(p_3q(C')>\alpha\)。

**证明。**

1. 由 `R8_scalar_root_bounds.md` 的前四主元上界，增长超过
   \(\alpha>4\) 只能来自 \(p_5=p_3q(C)\)，故得到 (7.1)。
2. 用第 4.1 节的行列符号把核心规范到 (1.1)，不改变目标值。
3. 由 (5.3) 与 (7.1)，\(p_3,q(C)>4\alpha/9>\tau_-\)。
4. 由 \(q(C)\le2|r|\)，有 \(|r|>\eta\)。第 6 节同理给
   \(p_2>\eta\)。
5. 第 3 节构造 \(C'\in\mathcal B_D\cup\mathcal B_X\)，并在见证层保持
   \(p_3\) 和 \(q\) 不变。
6. 因目标为正，压缩后的 \(r'\ne0\)，故有唯一的 \(r'\) 符号和 D/X 离散
   符号。轴界 (1.6)、chart 等式和 \(|r'|>\eta\) 把它放入表中唯一一个相应
   根盒（D/X 交面可放入两个）。
7. \(C'\) 完全主元且目标 \(q(C')>\tau_-\)，所以它自动满足
   (5.6) 或 (5.8)；压缩后的实际提升见证保证新 \(\beta\) 满足 (6.3)、(6.4)。
8. 由 (3.10)，新见证仍满足 (7.1)。

证毕。

若把严格反例换成全局极大点，已知候选给出
\(G_5\ge\alpha>\alpha_-\)，同一证明仍适用。因此十二根也覆盖至少一个正的
全局极大代表。

---

## 8. 与现有架构的接口及审计结论

### 8.1 已补上的证明责任

1. R3 的压缩公式是正确的；本报告补出了它对**完整提升见证**的作用，因而
   不是只在核心几何上移动。
2. 补出了 \(q>0\) 时 \(\lambda\mu>0\) 的证明，并把 \(q=0\) 的除零边界改成
   连续延拓处理。
3. 明确了只能说容量不减，不能说容量保持。
4. 把 R4 中抽象的 C0 根生成责任落实为 4 个 D 根、8 个 X 根及各自精确
   半代数筛选条件。
5. 说明了 transpose 不产生遗漏，但当前不靠 transpose 或残余置换删根。
6. 给出了紧致联合 \(\beta\) 根 \(p_2\in[\eta,2]\)，从根节点排除了 \(p_2=0\)。

### 8.2 尚未由本报告完成的部分

- 十二个根内的 circuit/Helly 分裂树仍需全局覆盖；
- `R8_scalar_root_bounds.md` 的前四主元界、(5.3) 的 \(9/4\) 标量定理与
  \(\alpha_-\) 根证书是本模块的显式上游依赖；
- 候选邻域的局部定理与远场盒覆盖仍需在最终 manifest 中拼接；
- 当前是普通数学证明和精确检查脚本，不进行 Lean 形式化。

一个实现层面的注意点是：现有 global_leaf_checker.py 支持 D/X 重构，但
仅检查单叶，不会自行证明十二个根的并集覆盖。最终 tree manifest 必须把本报告
的十二根（包括所有离散符号与 \(r\) 符号）逐一列为根节点；generic chart 只可
用于调试或过渡，不能替代这项根完备性清单。

---

## 9. Fraction 回归检查

新增文件：

- work/core_saturation.py
- work/test_core_saturation.py

脚本只用 fractions.Fraction，实现：

- (1.1) 的精确重构；
- (3.2) 与直接矩阵对角压缩的恒等核对；
- D/X 因子的精确构造；
- 完全主元尾条件、最后主元保持和退化分支；
- 转置坐标公式 (4.3)；
- 十二个闭根盒的生成与包含检查。

七项测试通过：

    Ran 7 tests in 0.113s
    OK

其中包含固定种子的 600 个有理尾块回归。随机/有限回归只用于发现实现错误；
本报告第 2--7 节的普遍恒等式与不等式才是证明。
