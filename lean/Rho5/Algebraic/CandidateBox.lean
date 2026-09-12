import Rho5.Algebraic.EliminationData

noncomputable section
namespace Rho5.Algebraic

/-! Exact endpoints imported from CANDIDATE_BOX.json. No decimal approximations. -/
def xLower : ℝ := (-154383169220456773686510736892915350419780230985919542728430415611267295981728899857587884472210406483410632282643665477237554953804043699023138110447621160118150434144333986124110497813062680362224242270466894358854191640027 : ℝ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def xUpper : ℝ := (-154383169220456773686510736892915350419780230985919542728430415611267295981728899857587884472210406483410632282643665477237554953804043699023138110447621160118150434144333986124109997813062680362224242270466894358854191640027 : ℝ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def yLower : ℝ := (-779150742216311061144934942459038900301281850854312081668422760365271742335015447212481930082268450983863651857926663281063368672667450988457321392459417010071603914261937195685135244418622142845316315647135946460051943986519 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def yUpper : ℝ := (-779150742216311061144934942459038900301281850854312081668422760365271742335015447212481930082268450983863651857926663281063368672667450988457321392459417010071603914261937195685133244418622142845316315647135946460051943986519 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def zLower : ℝ := (453224909846837467183709959977529473640881626821152195148225061062990962144765019673420236660910849584214877622458824690105378454219470392948909375556264458495010224674420035639014853124582109276572435805320420126271854303861 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def zUpper : ℝ := (453224909846837467183709959977529473640881626821152195148225061062990962144765019673420236660910849584214877622458824690105378454219470392948909375556264458495010224674420035639016853124582109276572435805320420126271854303861 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def gLower : ℝ := (413251707863247285422334685327737126995279153779908769454418052196743783429681764825855179985483022630152515659887825271609554209934703653072223897312925069088264378769458915450759171541549166637560269 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def gUpper : ℝ := (41325170786324728542233468532773712699527915377990876945441805219674378342968176482585517998548302263015251565988782527160955420993470365307222389731292506908826437876945891545075917154154916663756027 : ℝ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

structure CandidateBox (x y z g : ℝ) : Prop where
  x_lower : xLower ≤ x
  x_upper : x ≤ xUpper
  y_lower : yLower ≤ y
  y_upper : y ≤ yUpper
  z_lower : zLower ≤ z
  z_upper : z ≤ zUpper
  g_lower : gLower ≤ g
  g_upper : g ≤ gUpper

/-- A deliberately much coarser box suffices for every cancellation. -/
structure CoarseBox (x y z g : ℝ) : Prop where
  xl : -(5:ℝ)/8 ≤ x
  xu : x ≤ -(3:ℝ)/5
  yl : -(4:ℝ)/5 ≤ y
  yu : y ≤ -(3:ℝ)/4
  zl : (2:ℝ)/5 ≤ z
  zu : z ≤ (1:ℝ)/2
  gl : 4 < g
  gu : g < 5

theorem CandidateBox.coarse {x y z g : ℝ} (h : CandidateBox x y z g) :
    CoarseBox x y z g := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (by norm_num [xLower] : -(5:ℝ)/8 ≤ xLower) h.x_lower
  · exact le_trans h.x_upper (by norm_num [xUpper] : xUpper ≤ -(3:ℝ)/5)
  · exact le_trans (by norm_num [yLower] : -(4:ℝ)/5 ≤ yLower) h.y_lower
  · exact le_trans h.y_upper (by norm_num [yUpper] : yUpper ≤ -(3:ℝ)/4)
  · exact le_trans (by norm_num [zLower] : (2:ℝ)/5 ≤ zLower) h.z_lower
  · exact le_trans h.z_upper (by norm_num [zUpper] : zUpper ≤ (1:ℝ)/2)
  · exact lt_of_lt_of_le (by norm_num [gLower] : (4:ℝ) < gLower) h.g_lower
  · exact lt_of_le_of_lt h.g_upper (by norm_num [gUpper] : gUpper < (5:ℝ))

/-- These are proved below; they are not assumptions of the exported bridge. -/
structure GuardAt (v : Point) : Prop where
  y_ne : ev v yVar ≠ 0
  z_ne : ev v zVar ≠ 0
  zm1_ne : ev v (zVar-1) ≠ 0
  zp1_ne : ev v (zVar+1) ≠ 0
  f_ne : ev v cancelF ≠ 0
  d_ne : ev v cancelD ≠ 0
  r_ne : ev v cancelR ≠ 0
  g2_ne : ev v (gVar-2) ≠ 0
  g4_ne : ev v (gVar-4) ≠ 0

theorem guards_of_coarse {x y z g : ℝ} (h : CoarseBox x y z g) :
    GuardAt (point x y z g) := by
  have hx0 : x ≤ 0 := by linarith [h.xu]
  have hz0 : 0 ≤ z := by linarith [h.zl]
  have hy0 : y < 0 := by linarith [h.yu]
  have hzpos : 0 < z := by linarith [h.zl]
  have hxm : 0 ≤ x + 5/8 := by linarith [h.xl]
  have hxp : 0 ≤ (5:ℝ)/8 - x := by linarith [h.xu]
  have hxx : x^2 ≤ (25:ℝ)/64 := by nlinarith [mul_nonneg hxm hxp]
  have hzz : z^2 ≤ (1:ℝ)/4 := by
    have hp : 0 ≤ (1:ℝ)/2-z := by linarith [h.zu]
    nlinarith [mul_nonneg hz0 hp, h.zu]
  have hxz : x*z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx0 hz0
  have hxzz : x*z^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx0 (sq_nonneg z)
  have hxxz : x^2*z ≤ (25:ℝ)/128 := by
    calc
      x^2*z ≤ (25/64)*z := mul_le_mul_of_nonneg_right hxx hz0
      _ ≤ 25/128 := by linarith [h.zu]
  have hd : 2*x^2*z+x*z^2+x*z-2*x-2 ≤ -(23:ℝ)/64 := by
    nlinarith [hxxz, hxzz, hxz, h.xl]
  have ht0 : 0 ≤ 2*x+z+1 := by linarith [h.xl, h.zl]
  have ht1 : 2*x+z+1 ≤ (1:ℝ)/2 := by linarith [h.xu, h.zu]
  have hyv0 : 0 ≤ y+1 := by linarith [h.yl]
  have hyv1 : y+1 ≤ 1 := by linarith [h.yu]
  have hzt : z*(2*x+z+1) ≤ (1:ℝ)/4 := by
    calc
      z*(2*x+z+1) ≤ (1/2)*(1/2) :=
        mul_le_mul h.zu ht1 ht0 (by norm_num)
      _ = 1/4 := by norm_num
  have hprod : z*(2*x+z+1)*(y+1) ≤ (1:ℝ)/4 := by
    calc
      z*(2*x+z+1)*(y+1) ≤ (1/4)*(y+1) :=
        mul_le_mul_of_nonneg_right hzt hyv0
      _ ≤ 1/4 := by linarith
  have hfneg : x*z+z^2-2 < 0 := by nlinarith [hxz,hzz]
  have hdneg : 2*x^2*z+x*z^2+x*z-2*x-2 < 0 := by linarith
  have hrneg : 2*x^2*z+x*z^2+x*z-2*x-2 +
      z*(2*x+z+1)*(y+1) < 0 := by linarith [hd,hprod]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [point] using (ne_of_lt hy0)
  · simpa [point] using (ne_of_gt hzpos)
  · have hn : z-1 ≠ 0 := by linarith [h.zu]
    simpa [point, map_sub] using hn
  · have hn : z+1 ≠ 0 := by linarith [h.zl]
    simpa [point, map_add] using hn
  · simpa [cancelF, point, map_add, map_sub, map_mul, map_pow]
      using (ne_of_lt hfneg)
  · simpa [cancelD, point, map_add, map_sub, map_mul, map_pow]
      using (ne_of_lt hdneg)
  · simpa [cancelR, cancelD, point, map_add, map_sub, map_mul, map_pow]
      using (ne_of_lt hrneg)
  · have hn : g-2 ≠ 0 := by linarith [h.gl]
    simpa [point, map_sub] using hn
  · have hn : g-4 ≠ 0 := by linarith [h.gl]
    simpa [point, map_sub] using hn

theorem guards_of_box {x y z g : ℝ} (h : CandidateBox x y z g) :
    GuardAt (point x y z g) := guards_of_coarse h.coarse

theorem factor1_ne (v : Point) (h : GuardAt v) : ev v factor1 ≠ 0 := by
  simpa only [factor1, map_mul] using
    mul_ne_zero (mul_ne_zero h.zp1_ne h.z_ne) h.f_ne

theorem factor2_ne (v : Point) (h : GuardAt v) : ev v factor2 ≠ 0 := by
  simpa only [factor2, map_mul, map_pow] using
    mul_ne_zero (mul_ne_zero h.zp1_ne h.z_ne) (pow_ne_zero 2 h.f_ne)

theorem factor3_ne (v : Point) (h : GuardAt v) : ev v factor3 ≠ 0 := by
  simpa only [factor3, map_mul, map_pow] using
    mul_ne_zero (mul_ne_zero h.zp1_ne (pow_ne_zero 2 h.f_ne)) h.r_ne

theorem scale1_ne (v : Point) (h : GuardAt v) : ev v scale1 ≠ 0 := by
  simpa only [scale1, map_mul, map_neg] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h.y_ne) h.r_ne)
      h.zm1_ne) h.d_ne

theorem scale2_ne (v : Point) (h : GuardAt v) : ev v scale2 ≠ 0 := by
  simpa only [scale2, map_mul, map_pow] using
    mul_ne_zero (mul_ne_zero h.z_ne h.zm1_ne) (pow_ne_zero 2 h.d_ne)

theorem scale3_ne (v : Point) (h : GuardAt v) : ev v scale3 ≠ 0 := by
  have hn : (8:ℝ) ≠ 0 := by norm_num
  simpa [scale3, map_mul, map_pow] using mul_ne_zero hn (pow_ne_zero 2 h.z_ne)

theorem triangular_multiplier_ne (v : Point) (h : GuardAt v) :
    ev v (4*zVar*yDen) ≠ 0 := by
  have h4 : (4:ℝ) ≠ 0 := by norm_num
  have h2 : (2:ℝ) ≠ 0 := by norm_num
  have hdy : ev v yDen ≠ 0 := by
    simpa [yDen, map_mul] using mul_ne_zero (mul_ne_zero h2 h.z_ne) h.zm1_ne
  simpa [map_mul] using mul_ne_zero (mul_ne_zero h4 h.z_ne) hdy

end Rho5.Algebraic
