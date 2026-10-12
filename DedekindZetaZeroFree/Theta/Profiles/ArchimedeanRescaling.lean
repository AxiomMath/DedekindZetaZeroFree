module

public import DedekindZetaZeroFree.Theta.Profiles.UniformSectionPowerBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling
open NumberField MeasureTheory ThetaProfileHaarSheets
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]

lemma arch_rescale (B r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    archPowerMajorant B (r * c) ≤
      max (c ^ (1 / 4 : ℝ)) (c ^ (-B)) * archPowerMajorant B r := by
  change min (Real.rpow (r * c) (1 / 4)) (Real.rpow (r * c) (-B)) ≤
    max (Real.rpow c (1 / 4)) (Real.rpow c (-B)) *
      min (Real.rpow r (1 / 4)) (Real.rpow r (-B))
  have hq : Real.rpow (r * c) (1 / 4) = Real.rpow r (1 / 4) * Real.rpow c (1 / 4) :=
    Real.mul_rpow hr.le hc.le
  have hb : Real.rpow (r * c) (-B) = Real.rpow r (-B) * Real.rpow c (-B) :=
    Real.mul_rpow hr.le hc.le
  rw [hq, hb]
  have hn : 0 ≤ max (Real.rpow c (1 / 4)) (Real.rpow c (-B)) :=
    (Real.rpow_nonneg hc.le _).trans (le_max_left _ _)
  rw [mul_min_of_nonneg (Real.rpow r (1 / 4)) (Real.rpow r (-B)) hn]
  apply min_le_min
  · exact (mul_le_mul_of_nonneg_left (le_max_left (Real.rpow c (1 / 4)) (Real.rpow c (-B)))
      (Real.rpow_nonneg hr.le _)).trans_eq (mul_comm _ _)
  · exact (mul_le_mul_of_nonneg_left (le_max_right (Real.rpow c (1 / 4)) (Real.rpow c (-B)))
      (Real.rpow_nonneg hr.le _)).trans_eq (mul_comm _ _)

def radial (A : SArithmeticData F) (t : ℝ) : A.G :=
  A.radialSection (Real.exp t) (Real.exp_pos t)

lemma continuous_radial (A : SArithmeticData F) : Continuous (radial A) :=
  A.continuous_radialSection.comp (Real.continuous_exp.subtype_mk Real.exp_pos)

def rescaleCost (A : SArithmeticData F) (B u t : ℝ) : ℝ :=
  ∏ w : InfinitePlace F,
    let c := (‖((radial A t).1 w : w.Completion)‖ ^ 2) /
      (‖((radial A u).1 w : w.Completion)‖ ^ 2)
    max (c ^ (1 / 4 : ℝ)) (c ^ (-B))

lemma continuous_rescaleCost (A : SArithmeticData F) (B u : ℝ) :
    Continuous (rescaleCost A B u) := by
  apply continuous_finset_prod
  intro w hw
  have hc : Continuous (fun t => (‖((radial A t).1 w : w.Completion)‖ ^ 2) /
      (‖((radial A u).1 w : w.Completion)‖ ^ 2)) := by
    exact (show Continuous (fun t : ℝ => ‖((radial A t).1 w : w.Completion)‖ ^ 2) from
      (Units.continuous_val.comp
        ((continuous_apply w).comp (continuous_fst.comp (continuous_radial A)))).norm.pow 2).div_const _
  have hp (t : ℝ) : 0 < (‖((radial A t).1 w : w.Completion)‖ ^ 2) /
      (‖((radial A u).1 w : w.Completion)‖ ^ 2) :=
    div_pos (pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2)
      (pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2)
  exact (hc.rpow_const (fun t => Or.inl (hp t).ne')).max
    (hc.rpow_const (fun t => Or.inl (hp t).ne'))

lemma product_rescale (A : SArithmeticData F) (M B u t : ℝ) (y : A.G) :
    productPowerMajorant A M B (y * radial A t) ≤
      rescaleCost A B u t * productPowerMajorant A M B (y * radial A u) := by
  have hn (w : InfinitePlace F) (t : ℝ) :
      ‖((y * radial A t).1 w : w.Completion)‖ ^ 2 =
        ‖(y.1 w : w.Completion)‖ ^ 2 * ‖((radial A t).1 w : w.Completion)‖ ^ 2 := by
    simp only [Prod.fst_mul, Pi.mul_apply, Units.val_mul, norm_mul, mul_pow]
  have ha : (∏ w : InfinitePlace F,
      archPowerMajorant B (‖((y * radial A t).1 w : w.Completion)‖ ^ 2)) ≤
      rescaleCost A B u t * ∏ w : InfinitePlace F,
        archPowerMajorant B (‖((y * radial A u).1 w : w.Completion)‖ ^ 2) := by
    rw [rescaleCost, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro w hw
      exact archPowerMajorant_nonneg _ _ (sq_nonneg _)
    · intro w hw
      have hp (t : ℝ) : 0 < ‖((radial A t).1 w : w.Completion)‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2
      have hr : 0 < ‖((y * radial A u).1 w : w.Completion)‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2
      have he : ‖((y * radial A t).1 w : w.Completion)‖ ^ 2 =
          (‖((y * radial A u).1 w : w.Completion)‖ ^ 2) *
          ((‖((radial A t).1 w : w.Completion)‖ ^ 2) /
            (‖((radial A u).1 w : w.Completion)‖ ^ 2)) := by
        rw [hn, hn]
        field_simp
      rw [he]
      exact arch_rescale B _ _ hr (div_pos (hp t) (hp u))
  have hf (t : ℝ) (p : A.Sf) : (y * radial A t).2 p = y.2 p := by
    simp [radial, SArithmeticData.radialSection]
  unfold productPowerMajorant
  simp_rw [hf]
  have hfin : 0 ≤ ∏ p : A.Sf, finitePowerMajorant M ‖(y.2 p : p.val.adicCompletion F)‖ :=
    Finset.prod_nonneg fun p _ => finitePowerMajorant_nonneg M _ (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left ha hfin).trans_eq (by ring)

end DedekindZetaZeroFree.SheetRescaling

end
