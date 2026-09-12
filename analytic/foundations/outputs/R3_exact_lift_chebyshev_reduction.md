# R3: exact two-step lift and finite Chebyshev reduction for the (5\times5) conjecture

Date: 2026-08-19

## 0. Result and status

This note advances the global (5\times5) complete-pivoting problem, but
does **not** claim to prove the conjecture.

The main result is an exact reformulation.  The six column variables
(v,y\), the scalar (a), and the scale (p_3) can all be eliminated.
For a fixed normalized completely pivoted (3\times3) core (C), the
remaining lift problem has eight real parameters

\[
\beta=(b,u_1,u_2,u_3,x_1,x_2,x_3,p_2),
\]

and its maximum third-pivot scale is the reciprocal of a finite maximum of
explicit (2\times2) determinant ratios.  In particular, the conjecture is
equivalent to one universal, finite-piece semialgebraic inequality

\[
\boxed{q(C)\leq\alpha\,\delta_\beta(C)}. \tag{0.1}
\]

Here (q(C)) is the last pivot of (C),

\[
\alpha=4.1325170786324728542\ldots,
\]

and (\delta_\beta(C)) is given explicitly by at most (3\binom93=252)
three-row circuit expressions.  This identifies the exact remaining global
proof obligation without guessing an equality pattern.

## 1. Exact inverse elimination theorem

Let (s\in\{\pm1\}), (p_2,p_3>0), (a,b\in\mathbb R), and
(u,v,x,y\in\mathbb R^3).  For a (3\times3) matrix (C), define

\[
A=
\begin{bmatrix}
1&a&v^T\\
b&ab+s p_2&(bv+p_2y)^T\\
u&au+p_2x&p_3C+uv^T+s p_2xy^T
\end{bmatrix}. \tag{1.1}
\]

Direct Schur complementation gives

\[
A^{(2)}=
\begin{bmatrix}
s p_2&p_2y^T\\
p_2x&p_3C+s p_2xy^T
\end{bmatrix},
\qquad A^{(3)}=p_3C. \tag{1.2}
\]

Consequently (A) is normalized and completely pivoted in this fixed
order if and only if (C) is normalized and completely pivoted and

\[
\begin{aligned}
&|a|,|b|,\|u\|_\infty,\|v\|_\infty\leq1,\\
&|ab+s p_2|\leq1,\\
&\|au+p_2x\|_\infty\leq1,\\
&\|bv+p_2y\|_\infty\leq1,\\
&\|x\|_\infty,\|y\|_\infty\leq1,\\
&\|p_3C+s p_2xy^T\|_{\max}\leq p_2,\\
&\|p_3C+uv^T+s p_2xy^T\|_{\max}\leq1.
\end{aligned} \tag{1.3}
\]

These are necessary **and** sufficient.  They retain the original-matrix
and second-stage couplings discarded by the rank-two necessary test in
Lemma 3.1 of the paper.

Multiplying the second row of (A) by (s) preserves all absolute-value
complete-pivoting conditions and sends

\[
(s,b,y)\longmapsto(1,sb,sy).
\]

Thus (s=1) may be imposed without loss of generality.

## 2. Exact elimination of (a)

For fixed (b,u,x,p_2), the only conditions containing (a) are the five
one-dimensional bands

\[
|a|\leq1,\qquad |ba+p_2|\leq1,
\qquad |u_i a+p_2x_i|\leq1. \tag{2.1}
\]

Intervals in (\mathbb R) have Helly number two.  Two bands

\[
|ra+c|\leq1,\qquad |r'a+c'|\leq1
\]

intersect if and only if

\[
|cr'-c'r|\leq |r|+|r'|. \tag{2.2}
\]

Therefore (2.1) is feasible if and only if all of the following explicit
inequalities hold:

\[
\begin{aligned}
p_2&\leq1+|b|,\\
p_2|x_i|&\leq1+|u_i|,\\
p_2|u_i-bx_i|&\leq|b|+|u_i|,\\
p_2|x_i u_k-x_k u_i|&\leq|u_i|+|u_k|
\quad(1\leq i<k\leq3).
\end{aligned} \tag{2.3}
\]

Together with (b,u_i,x_i\in[-1,1]) and (p_2>0), these define the
admissible (\beta)-domain without the quantified variable (a).

## 3. Three independent two-dimensional Chebyshev problems

Fix an admissible (\beta=(b,u,x,p_2)) and a core (C).  Define the
(9\times2) matrix

\[
B_\beta=
\begin{bmatrix}
1&0\\
0&1\\
b&p_2\\
0&x_1\\
0&x_2\\
0&x_3\\
u_1&p_2x_1\\
u_2&p_2x_2\\
u_3&p_2x_3
\end{bmatrix} \tag{3.1}
\]

and, for the (j)-th column of (C),

\[
d_j=
\left(
0,0,0,
\frac{C_{1j}}{p_2},\frac{C_{2j}}{p_2},\frac{C_{3j}}{p_2},
C_{1j},C_{2j},C_{3j}
\right)^T. \tag{3.2}
\]

All nine pairs of column inequalities in (1.3) are exactly

\[
\left\|B_\beta
\binom{v_j}{y_j}+p_3d_j\right\|_\infty\leq1. \tag{3.3}
\]

Set

\[
\delta_{\beta,j}(C)=
\min_{r\in\mathbb R^2}\|B_\beta r+d_j\|_\infty,
\qquad
\delta_\beta(C)=\max_j\delta_{\beta,j}(C). \tag{3.4}
\]

Positive homogeneity in (3.3) proves the exact equivalence

\[
\boxed{
p_3C\text{ has a lift with fixed }(\beta,C)
\iff p_3\delta_\beta(C)\leq1.
} \tag{3.5}
\]

Hence the exact fixed-parameter capacity is

\[
\boxed{p_3^{\max}(\beta,C)=\frac1{\delta_\beta(C)}.} \tag{3.6}
\]

There is no relaxation in (3.5).  The minimizers in (3.4) reconstruct
(v,y) at the boundary (p_3=1/\delta_\beta(C)).

## 4. LP duality turns the criterion into 84 circuits

The dual of each problem in (3.4) is

\[
\delta_{\beta,j}(C)=
\max\{z^Td_j:B_\beta^Tz=0,\ \|z\|_1\leq1\}. \tag{4.1}
\]

The first two rows of (B_\beta) are the coordinate vectors, so
(\operatorname{rank}B_\beta=2).  On a fixed sign face, an extreme point
of the dual polytope is determined by the two equations (B_\beta^Tz=0)
and the equation (\|z\|_1=1).  It therefore has at most three nonzero
entries.

For a row triple (I=\{r,s,t\}), put

\[
\omega_I=
\bigl(
\det(B_s,B_t),
\det(B_t,B_r),
\det(B_r,B_s)
\bigr),
\qquad D_I=\|\omega_I\|_1. \tag{4.2}
\]

Whenever (D_I>0), (B_I^T\omega_I=0), and

\[
\phi_{I,j}(\beta,C)=
\frac{|\omega_I^T(d_j)_I|}{D_I} \tag{4.3}
\]

is a valid dual lower bound.  Conversely every extreme dual point is
captured by such a triple.  A one- or two-row degenerate circuit can be
extended by an independent row; the extra determinant weight is zero.
Thus

\[
\boxed{
\delta_{\beta,j}(C)=\max_{|I|=3,D_I>0}\phi_{I,j}(\beta,C),
\qquad
\delta_\beta(C)=\max_{j,I}\phi_{I,j}(\beta,C).
} \tag{4.4}
\]

There are only (\binom93=84) triples per column.  Formula (4.4), made
only of additions, multiplications, absolute values and division by a
positive sum, is suited to outward-rounded interval evaluation.

## 5. A shear exposes additional planar structure

For each column set

\[
t=v_j,\qquad r=bv_j+p_2y_j,
\qquad A_i=u_i-bx_i. \tag{5.1}
\]

Then (3.3) is equivalently generated by the nine row normals

\[
e_1,e_2,q,x_1q,x_2q,x_3q,R_1,R_2,R_3,
\quad
q=\left(-\frac b{p_2},\frac1{p_2}\right),
\quad R_i=(A_i,x_i). \tag{5.2}
\]

The three stage-two normals are now parallel.  Moreover the circuits using
the original rows ((b,p_2),(u_i,p_2x_i),(u_k,p_2x_k)) give the particularly
simple, (b,p_2)-independent family

\[
\delta_{\beta,j}(C)\geq
\frac{|A_kC_{ij}-A_iC_{kj}|}
{|A_ix_k-A_kx_i|+|A_i|+|A_k|}. \tag{5.3}
\]

This is the first explicit bridge from lift geometry to directional
combinations of rows of (C).  It is strictly more informative than a
bound using only the pivot magnitudes.

This subfamily is not sufficient by itself.  There is an exact rational
test case

\[
C=\begin{bmatrix}
1&1&1/2\\1&-1/2&-1\\1/2&-1&1
\end{bmatrix},
\qquad q(C)=\frac94,
\]

with admissible (p_2=1,b=a=0,u=(1,0,0),x=(0,1,1)), for which the maximum
of all ratios in (5.3) is only (1/2).  Thus

\[
\frac{q(C)}{\max\phi^{(5.3)}}=\frac92>\alpha.
\]

The complete 252-circuit family raises the corresponding Chebyshev error
to (1).  Therefore a proof must retain circuits involving the other box
and stage-two rows; (5.3) is a useful pruning family, not a standalone
global certificate.

The (a)-layer uses the same planar geometry.  If

\[
d=ab+p_2,
\]

then admissibility can be written as

\[
|a|,|b|,|d|,|x_i|,|A_i+bx_i|,|aA_i+dx_i|\leq1,
\qquad p_2=d-ab>0. \tag{5.4}
\]

## 6. Exact global reformulation

Define

\[
\operatorname{Cap}(C)=
\sup\{p_3:p_3C\text{ has an exact two-step lift}\}.
\]

Equations (3.5)--(3.6) give

\[
\operatorname{Cap}(C)
=\sup_{\beta\ \mathrm{admissible}}
\frac1{\delta_\beta(C)}
=\frac1{\inf_{\beta\ \mathrm{admissible}}\delta_\beta(C)}. \tag{6.1}
\]

Let (q(C)) be the final pivot of the normalized completely pivoted core.
Then the (5\times5) last pivot is (p_3q(C)), and therefore

\[
\boxed{
G_5=\sup_{C,\beta}\frac{q(C)}{\delta_\beta(C)}
=\sup_C q(C)\operatorname{Cap}(C).
} \tag{6.2}
\]

The conjecture (G_5=\alpha) is consequently equivalent to (0.1) for
every normalized completely pivoted (C) and every admissible (\beta).

If one tracks all intermediate pivots, put

\[
\rho_3(C)=\max\{1,\text{second core pivot},q(C)\}.
\]

The constructed (5\times5) pivot sequence is

\[
1,\ p_2,\ \delta^{-1},\
(\text{second core pivot})\delta^{-1},\ q(C)\delta^{-1}.
\]

Since (p_2\leq2<\alpha), the corresponding full-growth statement is
equivalently (\rho_3(C)\leq\alpha\delta_\beta(C)).  For the last-pivot
conjecture, (0.1) is the weaker and sufficient target.

Zero pivot cases cause no loss.  If (p_2=0), complete pivoting makes the
entire second Schur tail zero; if (p_3=0), the third tail is zero.  Neither
can violate a bound (>2).  Also (\delta_\beta(C)>0), because its vanishing
would force (v=y=0) from the first two rows of (B_\beta), and then
(C=0), contradicting normalization.

## 7. Exact contraction and a lossless core-boundary reduction

If a lift witness is feasible, then for arbitrary (\lambda,\mu\in[0,1])

\[
u,x\mapsto\lambda(u,x),\qquad
v,y\mapsto\mu(v,y),\qquad
p_3\mapsto\lambda\mu p_3 \tag{7.1}
\]

preserves every exact lift inequality.  Hence feasible (p_3)-values form
a downward interval; there are no isolated feasible islands.

The liftable Schur blocks are also closed under independent diagonal row
and column contractions.  This yields a constructive saturation lemma.
Let the last (2\times2) Schur tail of a liftable, completely pivoted core
be

\[
S=\begin{bmatrix}r&s\\t&u\end{bmatrix},
\qquad |s|,|t|,|u|\leq|r|. \tag{7.2}
\]

Contract the core row and column corresponding to (r) by
(\lambda,\mu\leq1).  The new tail is

\[
S'=\begin{bmatrix}
\lambda\mu r&\lambda s\\
\mu t&u
\end{bmatrix}, \tag{7.3}
\]

while its final pivot remains exactly

\[
u-\frac{ts}{r}. \tag{7.4}
\]

Writing

\[
\sigma=|s/r|,\quad\tau=|t/r|,\quad\upsilon=|u/r|,
\]

choose

\[
(\lambda,\mu)=
\begin{cases}
(\max\{\tau,\upsilon\},\ \upsilon/\lambda),
&\upsilon\geq\sigma\tau,\\
(\tau,\sigma),&\upsilon\leq\sigma\tau.
\end{cases} \tag{7.5}
\]

Complete pivoting is preserved, and respectively

\[
|S'_{11}|=|S'_{22}|,
\quad\text{or}\quad
|S'_{11}|=|S'_{12}|=|S'_{21}|. \tag{7.6}
\]

Thus the global search may be restricted without loss to the union of
these two boundary branches.  The algebraic candidate lies at their
intersection:

\[
S_*\approx0.996042439744
\begin{bmatrix}1&1\\-1&1\end{bmatrix}. \tag{7.7}
\]

This is a rigorous saturation statement obtained by construction, not a
generic-rank claim about the number of active constraints.

## 8. Candidate diagnostic and sparse certificates

For the reported algebraic candidate, double-precision extraction gives

\[
\begin{aligned}
p_2&\approx1.4532249098468375,\\
p_3&\approx2.0744683729015683,\\
q(C_*)&\approx1.9920848794876074,\\
p_3q(C_*)&\approx4.132517078632473.
\end{aligned}
\]

The three independent Chebyshev values are

\[
\delta_{\beta_*,1}(C_*)
=\delta_{\beta_*,2}(C_*)
=\delta_{\beta_*,3}(C_*)
\approx0.4820512151753346
=\frac1{p_3}. \tag{8.1}
\]

Using the row order in (3.1), maximizing dual triples are:

| core column | active row triple (one-based) | value |
|---:|:---:|---:|
| 1 | \(\{5,8,9\}\) | 0.4820512151753346 |
| 2 | \(\{3,7,8\}\) | 0.4820512151753347 |
| 3 | \(\{3,7,9\}\) | 0.4820512151753345 |

Each column has a support-three dual certificate, and all three columns
equioscillate at the same scale.  This is strong evidence that the observed
active pattern is structural.  The calculation is a numerical diagnostic;
an exact algebraic or outward-rounded verification should replace the
displayed decimals in a final proof.

A multistart fixed-core search found

\[
\operatorname{Cap}(C_*)\approx p_3,
\]

whereas the paper's rank-two necessary relaxation permits (p_3=2.25) for
the same core.  Thus the discarded outer coupling is not a small correction:
it is exactly what cuts the relaxed value down to the candidate scale.

## 9. What scalar bounds can and cannot do

Standard three-, four-, and five-dimensional determinant inequalities give
pointwise lower bounds such as

\[
\delta\geq\frac1{\Phi(p_2)},
\qquad
\delta^3\geq
\frac{p_2\,h(C)\,q(C)}{48}, \tag{9.1}
\]

where (h(C)) is the second core pivot and

\[
\Phi(t)=
\begin{cases}
2t,&t\leq1,\\
t(3-t),&1\leq t\leq2.
\end{cases}
\]

Combining the sharp scalar pivot envelope with the determinant bound
recovers the analytic constant

\[
\frac{q(C)}{\delta_\beta(C)}
\leq5.0039311916803555\ldots<5.004. \tag{9.2}
\]

This is essentially a reconstruction of Cohen's 1974 (<5.005) bound and
is weaker than the paper's computer-assisted (4.84).  More importantly,
at the conjectured candidate the strongest scalar bound gives only

\[
\delta\geq0.444877\ldots,
\]

while the required value is (0.482051\ldots), an (8.36\%\) gap.  Pivot
magnitudes and determinants erase the three columns' different circuit
supports.  The remaining proof must use that directional information.

## 10. Concrete route to a global certificate

A putative counterexample satisfies

\[
p_3q(C)>\alpha,
\qquad p_3,q(C)\leq\frac94.
\]

Hence

\[
p_3,q(C)>\frac{\alpha}{9/4}\approx1.83667425717,
\]

and at least one of them exceeds

\[
\sqrt\alpha\approx2.03285933567. \tag{10.1}
\]

This gives two high-growth branches: the leading (3\times3) block is
above (\sqrt\alpha), or the core is.  The known (>2) three-dimensional
sign classification applies on the appropriate side.  The candidate is in
the first branch: (p_3>\sqrt\alpha) but (q(C)<2).

A certified proof can now proceed as follows.

1. Cover only cores with (q(C)>\alpha/(9/4)), using the two boundary
   branches (7.6) and the (>2) sign classification where applicable.
2. Branch over the eight-dimensional admissible (\beta)-domain, pruning
   immediately with the quantifier-free Helly inequalities (2.3) and the
   scalar tests (9.1).
3. On each surviving ((C,\beta))-box, use outward rounding on one or more
   circuit ratios (4.3).  It is enough to certify
   
   \[
   \inf_{\mathrm{box}}\phi_{I,j}
   \geq
   \frac{\sup_{\mathrm{box}}q(C)}{\alpha}.
   \]
4. Near the candidate orbit, freeze the observed three circuit supports,
   solve the resulting stationarity equations with interval Newton, and
   connect the isolated solution to the already verified degree-61
   algebraic number.

This route replaces enumeration of arbitrary active-constraint patterns by
a fixed family of sparse dual certificates.

## 11. Reproducibility

The implementation is in `work/exact_two_step_lift.py`.  It includes:

- exact coordinate extraction and reconstruction;
- the (a)-interval and pairwise Helly tests;
- the two-dimensional LP formulation;
- the closed 84-triple determinant evaluator;
- the sheared coordinates (5.2);
- exact contraction and core-tail saturation constructions.

`work/test_exact_two_step_lift.py` performs eight regression tests,
including 300 random column LP-versus-circuit comparisons, 1,000 random
parameter draws for the Helly-versus-interval check (both signs), 300 random
sheared-coordinate column comparisons, and 100 random core saturation
checks.  All tests pass.  These are numerical
implementation checks, not substitutes for outward-rounded certification.
