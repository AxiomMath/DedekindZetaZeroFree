module

public import DedekindZetaZeroFree.Analysis.WeakH2.LocalizedTranslation
public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.FirstOrderSmoothProducts
public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.H1TestContinuity

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.WeakH2.FluxRaw

open MeasureTheory Filter Topology KPContLocalNorm
open KPContLocalEnergy.SobolevEnergyEstimates.Raw

def WeightedFirstBound {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (L : ℝ) : Prop :=
  ∀ x ∈ B.carrier, ∀ i j k : Fin n,
    ‖fderiv ℝ (fun y => D.density y * D.matrix y i j) x
      (EuclideanSpace.single k 1)‖ ≤ L

def cutoffValue {n : ℕ} {B : LocalBall n} (η : TestFunction B.toOpens ℝ ⊤)
    (q : IntegerSobolev B 1) : Space n → ℂ :=
  B.carrier.indicator (fun x => (η x : ℂ) ^ 2 * value q x)

def cutoffGradient {n : ℕ} {B : LocalBall n} (η : TestFunction B.toOpens ℝ ⊤)
    (q : IntegerSobolev B 1) (j : Fin n) : Space n → ℂ :=
  B.carrier.indicator (fun x => (η x : ℂ) ^ 2 * gradient q j x +
    2 * (η x : ℂ) * coordinateDerivativeList [j] (fun y => (η y : ℂ)) x * value q x)

namespace DifferenceTestAtoms

theorem quotient_memLp {n : ℕ} (f : Space n → ℂ) (hf : MemLp f 2 volume)
    (k : Fin n) (t : ℝ) : MemLp (differenceQuotient k t f) 2 volume := by
  exact ((hf.comp_measurePreserving (measurePreserving_add_right volume _)).sub hf).const_mul _

theorem exactIBP {n : ℕ} (f g : Space n → ℂ) (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (k : Fin n) (t : ℝ) :
    (∫ x, f x * (-differenceQuotient k (-t) g x)) =
      ∫ x, differenceQuotient k t f x * g x := by
  have hfg := hf.integrable_mul hg
  have hfgt := hf.integrable_mul
    (hg.comp_measurePreserving (measurePreserving_add_right volume ((-t) • EuclideanSpace.single k 1)))
  have hftg := (hf.comp_measurePreserving
    (measurePreserving_add_right volume (t • EuclideanSpace.single k 1))).integrable_mul hg
  change Integrable (fun x => f x * g x) volume at hfg
  change Integrable (fun x => f x * g (x + (-t) • EuclideanSpace.single k 1)) volume at hfgt
  change Integrable (fun x => f (x + t • EuclideanSpace.single k 1) * g x) volume at hftg
  have hshift : (∫ x, f x * g (x + (-t) • EuclideanSpace.single k 1)) =
      ∫ x, f (x + t • EuclideanSpace.single k 1) * g x := by
    have h := integral_add_right_eq_self
      (fun x => f x * g (x + (-t) • EuclideanSpace.single k 1))
      (t • EuclideanSpace.single k 1) (μ := volume)
    simpa only [neg_smul, add_neg_cancel_right] using h.symm
  simp only [differenceQuotient, Complex.ofReal_neg, inv_neg, neg_mul, neg_neg]
  have hleft : (∫ x, f x * ((t : ℂ)⁻¹ *
      (g (x + (-t) • EuclideanSpace.single k 1) - g x))) =
      (t : ℂ)⁻¹ * ((∫ x, f x * g (x + (-t) • EuclideanSpace.single k 1)) - ∫ x, f x * g x) := by
    simp_rw [mul_left_comm (f _) (t : ℂ)⁻¹]
    change (∫ x, (t : ℂ)⁻¹ * (f x * (g (x + (-t) • EuclideanSpace.single k 1) - g x))) = _
    rw [integral_const_mul]
    simp_rw [mul_sub]
    rw [integral_sub hfgt hfg, mul_sub]
  have hright : (∫ x, (t : ℂ)⁻¹ *
      (f (x + t • EuclideanSpace.single k 1) - f x) * g x) =
      (t : ℂ)⁻¹ * ((∫ x, f (x + t • EuclideanSpace.single k 1) * g x) - ∫ x, f x * g x) := by
    simp_rw [mul_assoc, sub_mul]
    rw [integral_const_mul, integral_sub hftg hfg]
  rw [hleft, hright, hshift]

theorem global_indicator_ae {n : ℕ} {B : LocalBall n}
    (K : Set (Space n)) (hKB : K ⊆ B.carrier) (f : BallL2 B) (g : Space n → ℂ)
    (hfg : ∀ᵐ x ∂volume.restrict B.carrier, f x = g x)
    (hg : ∀ x, x ∉ K → g x = 0) :
    KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K f =ᵐ[volume]
      B.carrier.indicator g := by
  filter_upwards [(ae_restrict_iff' Metric.isOpen_ball.measurableSet).1 hfg] with x hx
  by_cases hxK : x ∈ K
  · simp [KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension,
      hxK, hKB hxK, hx (hKB hxK)]
  · by_cases hxB : x ∈ B.carrier
    · simp [KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension, hxK, hxB, hg x hxK]
    · simp [KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension, hxK, hxB]

open KPContLocalEnergy.SobolevEnergyEstimates KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation

theorem weighted_coefficient_difference_bound {n : ℕ} (mid outer : LocalBall n)
    {cρ Cρ κ Λ L : ℝ} (D : Coefficients outer cρ Cρ κ Λ)
    (hD : WeightedFirstBound D L) (hcenter : mid.center = outer.center)
    (k : Fin n) (t : ℝ) (ht : t ≠ 0)
    (hsafe : |t| < outer.radius - mid.radius)
    (x : Space n) (hx : x ∈ mid.carrier) (i j : Fin n) :
    ‖differenceQuotient k t (fun y => (D.density y * D.matrix y i j : ℝ)) x‖ ≤ L := by
  let a : Space n → ℝ := fun y => D.density y * D.matrix y i j
  let e : Space n := EuclideanSpace.single k 1
  have hmem (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : x + (s * t) • e ∈ outer.carrier := by
    have hnorm : ‖(s * t) • e‖ ≤ |t| := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1]
      simp only [e, EuclideanSpace.norm_single, norm_one, mul_one]
      nlinarith [abs_nonneg t, hs.2]
    have hx' : dist x outer.center < mid.radius := by
      simpa only [LocalBall.carrier, Metric.mem_ball, hcenter] using hx
    change dist (x + (s * t) • e) outer.center < outer.radius
    have htri := dist_triangle (x + (s * t) • e) x outer.center
    have heq : dist (x + (s * t) • e) x = ‖(s * t) • e‖ := by simp [dist_eq_norm]
    rw [heq] at htri
    linarith
  have hda (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      DifferentiableAt ℝ a (x + (s * t) • e) := by
    have hsm : ContDiffOn ℝ (⊤ : ℕ∞) a outer.carrier := D.density_smooth.mul (D.matrix_smooth i j)
    exact (hsm.differentiableOn (by simp) _ (hmem s hs)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hmem s hs))
  have hd (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s : ℝ => a (x + (s * t) • e))
        (t * fderiv ℝ a (x + (s * t) • e) e) (Set.Icc 0 1) s := by
    have hline := (((hasDerivAt_id s).mul_const t).smul_const e).const_add x
    convert ((hda s hs).hasFDerivAt.comp_hasDerivAt s hline).hasDerivWithinAt using 1
    · rfl
    · simp only [one_mul, map_smul, smul_eq_mul]
  have hb (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
      ‖t * fderiv ℝ a (x + (s * t) • e) e‖ ≤ |t| * L := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hD _ (hmem s ⟨hs.1, hs.2.le⟩) i j k) (abs_nonneg t)
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  simp only [one_mul, zero_mul, zero_smul, add_zero] at hm
  change ‖(t : ℂ)⁻¹ * ((a (x + t • e) : ℂ) - (a x : ℂ))‖ ≤ L
  rw [norm_mul, norm_inv, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have htpos : 0 < |t| := abs_pos.mpr ht
  exact (inv_mul_le_iff₀ htpos).2 (by simpa only [Real.norm_eq_abs] using hm)

theorem quotient_star {n : ℕ} (f : Space n → ℂ) (k : Fin n) (t : ℝ) :
    differenceQuotient k t (fun x => star (f x)) = fun x => star (differenceQuotient k t f x) := by
  funext x
  simp [differenceQuotient]

end DifferenceTestAtoms

private theorem flux_matrix_bound {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ} (D : Coefficients B cρ Cρ κ Λ)
    (hκ : 0 < κ) (x : Space n) (hx : x ∈ B.carrier) (i j : Fin n) :
    |D.matrix x i j| ≤ |Λ| := by
  classical
  have hd (k : Fin n) : 0 ≤ D.matrix x k k := by
    have h := D.ellipticity x hx (EuclideanSpace.single k 1)
    simp [EuclideanSpace.norm_single, EuclideanSpace.single_apply] at h
    linarith
  have hu (k : Fin n) : D.matrix x k k ≤ Λ := by
    have h := D.upper_bound x hx (EuclideanSpace.single k 1)
    simpa [EuclideanSpace.norm_single, EuclideanSpace.single_apply] using h
  by_cases hij : i = j
  · subst j
    rw [abs_of_nonneg (hd i)]
    exact (hu i).trans (le_abs_self Λ)
  have hnorm (t : ℝ) :
      ‖(EuclideanSpace.single i 1 + EuclideanSpace.single j t : Space n)‖ ^ 2 = 1 + t ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, PiLp.add_apply, EuclideanSpace.single_apply,
      add_sq, Finset.sum_add_distrib, hij, Ne.symm hij]
  have hquad (t : ℝ) := D.upper_bound x hx
    (EuclideanSpace.single i 1 + EuclideanSpace.single j t)
  simp only [hnorm] at hquad
  have hq (t : ℝ) :
      D.matrix x i i + 2 * D.matrix x i j * t + D.matrix x j j * t ^ 2 ≤ Λ * (1 + t ^ 2) := by
    have h := hquad t
    simp [PiLp.add_apply, mul_add, add_mul, Finset.sum_add_distrib,
      EuclideanSpace.single_apply, D.symmetric x hx j i] at h
    nlinarith [h]
  apply abs_le.mpr
  constructor <;> nlinarith [hq 1, hq (-1), hd i, hd j, le_abs_self Λ]

private theorem flux_density_memLp {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hcρ : 0 < cρ) :
    MemLp (fun x => (D.density x : ℂ)) ⊤ (volume.restrict B.carrier) := by
  apply memLp_top_of_bound
    ((Complex.continuous_ofReal.comp_continuousOn D.density_smooth.continuousOn).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet) Cρ
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_trans hcρ.le (D.density_bounds x hx).1)]
  exact (D.density_bounds x hx).2

private theorem flux_matrix_memLp {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hκ : 0 < κ) (i j : Fin n) :
    MemLp (fun x => (D.matrix x i j : ℂ)) ⊤ (volume.restrict B.carrier) := by
  apply memLp_top_of_bound
    ((Complex.continuous_ofReal.comp_continuousOn (D.matrix_smooth i j).continuousOn).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet) |Λ|
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  simpa using flux_matrix_bound D hκ x hx i j

private theorem flux_cutoffGradient_memLp {n : ℕ} {B : LocalBall n}
    (η : TestFunction B.toOpens ℝ ⊤) (q : IntegerSobolev B 1) (i : Fin n) :
    MemLp (cutoffGradient η q i) 2 volume := by
  obtain ⟨v, hv, hg⟩ := KPContLocalEnergy.SobolevEnergyEstimates.multiply_smooth_compact B η q
  apply (memLp_indicator_iff_restrict (s := B.carrier) Metric.isOpen_ball.measurableSet.nullMeasurableSet).2
  exact (Lp.memLp (gradient v i)).ae_eq (hg i)

private theorem flux_pairing {n : ℕ} (mid outer : LocalBall n)
    (f g : Space n → ℂ) (hf : MemLp f 2 (volume.restrict outer.carrier))
    (hg : MemLp g 2 volume) (hgs : ∀ x, x ∉ mid.carrier → g x = 0)
    (k : Fin n) (t : ℝ) :
    (∫ x in outer.carrier, f x * (-differenceQuotient k (-t) g x)) =
      ∫ x in mid.carrier, differenceQuotient k t (outer.carrier.indicator f) x * g x := by
  have hF : MemLp (outer.carrier.indicator f) 2 volume :=
    (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet).2 hf
  calc
    _ = ∫ x in outer.carrier, outer.carrier.indicator f x *
        (-differenceQuotient k (-t) g x) := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro x hx
      simp only [Set.indicator_of_mem (show x ∈ outer.carrier from hx)]
    _ = ∫ x, outer.carrier.indicator f x * (-differenceQuotient k (-t) g x) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hx])
    _ = ∫ x, differenceQuotient k t (outer.carrier.indicator f) x * g x :=
      DifferenceTestAtoms.exactIBP _ _ hF hg k t
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hgs x hx, mul_zero])).symm

theorem difference_flux_identity_of_tested {n : ℕ} (mid outer : LocalBall n)
    (hcenter : mid.center = outer.center) (hgap : mid.radius < outer.radius)
    (η : TestFunction mid.toOpens ℝ ⊤) (k : Fin n) (t : ℝ) (ht : t ≠ 0)
    (hstep : |t| < outer.radius - mid.radius)
    (hsafe : Metric.cthickening |t| (tsupport (fun x => η x)) ⊆ mid.carrier)
    {cρ Cρ κ Λ : ℝ} (hcρ : 0 < cρ) (hκ : 0 < κ)
    (D : Coefficients outer cρ Cρ κ Λ) (z : ℂ)
    (u : IntegerSobolev outer 1) (h : BallL2 outer)
    (q : IntegerSobolev mid 1)
    (hqvalue : ∀ᵐ x ∂volume.restrict mid.carrier,
      value q x = differenceQuotient k t (zeroExtension (value u)) x)
    (hqgradient : ∀ j : Fin n, ∀ᵐ x ∂volume.restrict mid.carrier,
      gradient q j x = differenceQuotient k t (zeroExtension (gradient u j)) x)
    (w : IntegerSobolev outer 1)
    (hwvalue : ∀ᵐ x ∂volume.restrict outer.carrier,
      value w x = -differenceQuotient k (-t) (cutoffValue η q) x)
    (hwgradient : ∀ i : Fin n, ∀ᵐ x ∂volume.restrict outer.carrier,
      gradient w i x = -differenceQuotient k (-t) (cutoffGradient η q i) x)
    (hpde : (∫ x in outer.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x * star (gradient w i x)) -
      z * (∫ x in outer.carrier, (D.density x : ℂ) * value u x * star (value w x)) =
        ∫ x in outer.carrier, (D.density x : ℂ) * h x * star (value w x)) :
    (∫ x in mid.carrier, ∑ i : Fin n, ∑ j : Fin n,
      (((D.density (x + t • EuclideanSpace.single k 1) *
          D.matrix (x + t • EuclideanSpace.single k 1) i j : ℝ) : ℂ) *
          differenceQuotient k t (zeroExtension (gradient u j)) x +
        differenceQuotient k t (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) x *
          gradient u j x) * star (cutoffGradient η q i x)) =
      z * (∫ x in outer.carrier, (D.density x : ℂ) * value u x * star (value w x)) +
        (∫ x in outer.carrier, (D.density x : ℂ) * h x * star (value w x)) := by
  classical
  have hsub : mid.carrier ⊆ outer.carrier := by
    intro x hx
    change dist x outer.center < outer.radius
    have hx' : dist x outer.center < mid.radius := by
      simpa only [LocalBall.carrier, Metric.mem_ball, hcenter] using hx
    exact hx'.trans hgap
  let a : Fin n → Fin n → Space n → ℂ := fun i j x =>
    ((D.density x * D.matrix x i j : ℝ) : ℂ)
  let f : Fin n → Fin n → Space n → ℂ := fun i j x => a i j x * gradient u j x
  let F : Fin n → Fin n → Space n → ℂ := fun i j => outer.carrier.indicator (f i j)
  have hf (i j : Fin n) : MemLp (f i j) 2 (volume.restrict outer.carrier) := by
    have hm : MemLp (fun x => (D.matrix x i j : ℂ) * gradient u j x) 2
        (volume.restrict outer.carrier) :=
      (flux_matrix_memLp D hκ i j).fun_mul (Lp.memLp (gradient u j))
    have hd : MemLp (fun x => (D.density x : ℂ) *
        ((D.matrix x i j : ℂ) * gradient u j x)) 2 (volume.restrict outer.carrier) :=
      (flux_density_memLp D hcρ).fun_mul hm
    simpa only [f, a, Complex.ofReal_mul, mul_assoc] using hd
  have hF (i j : Fin n) : MemLp (F i j) 2 volume :=
    (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet).2 (hf i j)
  let E : Fin n → Fin n → Space n → ℂ := fun i j x =>
    (a i j (x + t • EuclideanSpace.single k 1) *
      differenceQuotient k t (zeroExtension (gradient u j)) x +
      differenceQuotient k t (a i j) x * gradient u j x) * star (cutoffGradient η q i x)
  have hexp (i j : Fin n) (x : Space n) (hx : x ∈ mid.carrier) :
      E i j x = differenceQuotient k t (F i j) x * star (cutoffGradient η q i x) := by
    have hxB := hsub hx
    have hxt := safe_segment_mem mid outer hcenter k t hstep hx (le_refl |t|)
    simp only [E, F, f, differenceQuotient, zeroExtension,
      Set.indicator_of_mem hxB, Set.indicator_of_mem hxt]
    ring
  have hE (i j : Fin n) : Integrable (E i j) (volume.restrict mid.carrier) := by
    apply (((DifferenceTestAtoms.quotient_memLp _ (hF i j) k t).mono_measure
      Measure.restrict_le_self).integrable_mul
      ((flux_cutoffGradient_memLp η q i).star.mono_measure Measure.restrict_le_self)).congr
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact (hexp i j x hx).symm
  have hp (i j : Fin n) :
      (∫ x in outer.carrier, f i j x * star (gradient w i x)) =
        ∫ x in mid.carrier, E i j x := by
    calc
      _ = ∫ x in outer.carrier, f i j x *
          (-differenceQuotient k (-t) (fun y => star (cutoffGradient η q i y)) x) := by
        apply integral_congr_ae
        filter_upwards [hwgradient i] with x hx
        simp only [hx, star_neg, DifferenceTestAtoms.quotient_star]
      _ = ∫ x in mid.carrier, differenceQuotient k t (F i j) x *
          star (cutoffGradient η q i x) :=
        flux_pairing mid outer _ _ (hf i j) (flux_cutoffGradient_memLp η q i).star
          (fun x hx => by simp [cutoffGradient, hx]) k t
      _ = _ := by
        apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
        intro x hx
        exact (hexp i j x hx).symm
  have henergy :
      (∫ x in outer.carrier, (D.density x : ℂ) * ∑ i, ∑ j,
        (D.matrix x i j : ℂ) * gradient u j x * star (gradient w i x)) =
      ∫ x in mid.carrier, ∑ i, ∑ j, E i j x := by
    have hi (i j : Fin n) : Integrable (fun x => f i j x * star (gradient w i x))
        (volume.restrict outer.carrier) :=
      (hf i j).integrable_mul (Lp.memLp (gradient w i)).star
    calc
      _ = ∫ x in outer.carrier, ∑ i, ∑ j, f i j x * star (gradient w i x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [Finset.mul_sum, f, a, Complex.ofReal_mul, mul_assoc]
      _ = ∑ i, ∑ j, ∫ x in outer.carrier, f i j x * star (gradient w i x) := by
        rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
        congr 1
        funext i
        exact integral_finset_sum _ (fun j _ => hi i j)
      _ = ∑ i, ∑ j, ∫ x in mid.carrier, E i j x := by
        simp_rw [hp]
      _ = _ := by
        rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hE i j))]
        congr 1
        funext i
        exact (integral_finset_sum _ (fun j _ => hE i j)).symm
  change (∫ x in mid.carrier, ∑ i, ∑ j, E i j x) = _
  rw [← henergy]
  exact sub_eq_iff_eq_add.mp hpde |>.trans (add_comm _ _)

end DedekindZetaZeroFree.WeakH2.FluxRaw

end
