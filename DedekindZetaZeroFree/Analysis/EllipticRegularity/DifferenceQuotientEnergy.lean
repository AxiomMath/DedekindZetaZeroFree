module

public import DedekindZetaZeroFree.Analysis.WeakH2.FluxIdentity
public import DedekindZetaZeroFree.Analysis.EllipticEquations.EnergyEstimates.CutoffQuadraticForms

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.WeakH2.CoerciveDifference

open MeasureTheory KPContLocalNorm
open KPContLocalEnergy.SobolevEnergyEstimates.Raw

private theorem quotient_value_norm_le {n : ℕ} (mid outer : LocalBall n)
    (hcenter : mid.center = outer.center) (hgap : mid.radius < outer.radius)
    (u : IntegerSobolev outer 1) (k : Fin n) (t : ℝ)
    (ht : t ≠ 0) (hsafe : |t| < outer.radius - mid.radius)
    (q : IntegerSobolev mid 1)
    (hq : ∀ᵐ x ∂volume.restrict mid.carrier,
      value q x = differenceQuotient k t (zeroExtension (value u)) x) :
    ‖value q‖ ≤ ‖gradient u k‖ := by
  obtain ⟨q', hq', _, hnorm⟩ :=
    localized_difference_quotient mid outer hcenter hgap u k t ht hsafe
  have he : value q = value q' := by
    apply Lp.ext
    filter_upwards [hq, hq'] with x hx hx'
    exact hx.trans hx'.symm
  simpa only [he] using hnorm

private theorem gradient_norm_le_sobolevNorm {n : ℕ} {outer : LocalBall n}
    (u : IntegerSobolev outer 1) (k : Fin n) :
    ‖gradient u k‖ ≤ u.sobolevNorm := by
  have hs : ‖gradient u k‖ ^ 2 ≤ u.sobolevNorm ^ 2 := by
    rw [u.sobolevNorm_sq]
    exact Finset.single_le_sum (fun α _ => sq_nonneg ‖u.derivatives α‖)
      (Finset.mem_univ (firstIndex k))
  have hu : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (gradient u k)]

private theorem l2_pairing_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g : X → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * star (g x) ∂μ‖ ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have he : (∫ x, f x * star (g x) ∂μ) = inner ℂ (hg.toLp g) (hf.toLp f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    simp [RCLike.inner_apply, hx, hy]
  rw [he]
  exact (norm_inner_le_norm _ _).trans_eq (mul_comm _ _)

private theorem l2_multiplier_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (a f : X → ℂ) (hf : MemLp f 2 μ) (ha : MemLp a ⊤ μ)
    (C : ℝ) (hC : 0 ≤ C) (hab : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    ‖(show MemLp (fun x => a x * f x) 2 μ from ha.fun_mul hf).toLp (fun x => a x * f x)‖ ≤ C * ‖hf.toLp f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hm : MemLp (fun x => a x * f x) 2 μ := ha.fun_mul hf
  filter_upwards [hm.coeFn_toLp, hf.coeFn_toLp, hab] with x hx hy hb
  rw [hx, hy, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

private theorem component_norm_le_sobolevNorm {n : ℕ} {outer : LocalBall n}
    (u : IntegerSobolev outer 1) (α : MultiIndex n 1) :
    ‖u.derivatives α‖ ≤ u.sobolevNorm := by
  have hs : ‖u.derivatives α‖ ^ 2 ≤ u.sobolevNorm ^ 2 := by
    rw [u.sobolevNorm_sq]
    exact Finset.single_le_sum (fun β _ => sq_nonneg ‖u.derivatives β‖) (Finset.mem_univ α)
  have hu : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (u.derivatives α)]

private theorem compact_sobolev_extension {n : ℕ} (B T : LocalBall n)
    (v : IntegerSobolev B 1) (K : Set (Space n)) (hK : IsCompact K)
    (hKB : K ⊆ B.carrier) (hKT : K ⊆ T.carrier)
    (hv : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → value v x = 0) :
    ∃ V : IntegerSobolev T 1, ∀ α : MultiIndex n 1,
      (∀ᵐ x ∂volume.restrict T.carrier, V.derivatives α x =
        KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K (v.derivatives α) x) ∧
      ‖V.derivatives α‖ = ‖v.derivatives α‖ := by
  let F := fun α => KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K (v.derivatives α)
  have hF : ∀ α, MemLp (F α) 2 volume := fun α =>
    KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension_memLp hK hKB _
  let d := fun α => ((hF α).mono_measure (Measure.restrict_le_self (s := T.carrier))).toLp (F α)
  have hd : ∀ α, ∀ᵐ x ∂volume.restrict T.carrier, d α x = F α x := fun α => MemLp.coeFn_toLp _
  have hw : ∀ α, IsWeakDerivative T α (d (zeroIndex n 1)) (d α) := by
    intro α φ
    have he := KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension_weak_identity
      B v K hK hKB hv α (fun y => φ y) φ.contDiff
    change (∫ x in T.carrier, d (zeroIndex n 1) x * coordinateDerivative α (fun y => φ y) x) =
      (-1 : ℂ) ^ α.degree * ∫ x in T.carrier, d α x * φ x
    have hleft : (∫ x in T.carrier, d (zeroIndex n 1) x * coordinateDerivative α (fun y => φ y) x) =
        ∫ x, F (zeroIndex n 1) x * coordinateDerivative α (fun y => φ y) x := by
      calc
        _ = ∫ x in T.carrier, F (zeroIndex n 1) x * coordinateDerivative α (fun y => φ y) x := by
          apply integral_congr_ae
          filter_upwards [hd (zeroIndex n 1)] with x hx
          rw [hx]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          have hn : x ∉ K := fun h => hx (hKT h)
          simp [F, KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension, hn])
    have hright : (∫ x in T.carrier, d α x * φ x) = ∫ x, F α x * φ x := by
      calc
        _ = ∫ x in T.carrier, F α x * φ x := by
          apply integral_congr_ae
          filter_upwards [hd α] with x hx
          rw [hx]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          have hn : x ∉ K := fun h => hx (hKT h)
          simp [F, KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension, hn])
    rw [hleft, hright]
    exact he
  refine ⟨⟨d, hw⟩, fun α => ⟨hd α, ?_⟩⟩
  have hz := KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.weak_derivatives_zero_off_compact B v K hK hv α
  have ha := KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension_ae (v.derivatives α) hz
  have he : eLpNorm (F α) 2 (volume.restrict T.carrier) =
      eLpNorm (v.derivatives α) 2 (volume.restrict B.carrier) := by
    calc
      _ = eLpNorm (F α) 2 volume := by
        rw [← eLpNorm_indicator_eq_eLpNorm_restrict (show MeasurableSet T.carrier from Metric.isOpen_ball.measurableSet).nullMeasurableSet]
        congr 1
        ext x
        by_cases hx : x ∈ T.carrier
        · simp [hx]
        · have hn : x ∉ K := fun h => hx (hKT h)
          simp [hx, F, KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension, hn]
      _ = eLpNorm (F α) 2 (volume.restrict B.carrier) := by
        rw [← eLpNorm_indicator_eq_eLpNorm_restrict (show MeasurableSet B.carrier from Metric.isOpen_ball.measurableSet).nullMeasurableSet]
        congr 1
        ext x
        by_cases hx : x ∈ B.carrier
        · simp [hx]
        · have hn : x ∉ K := fun h => hx (hKB h)
          simp [hx, F, KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension, hn]
      _ = _ := eLpNorm_congr_ae ha
  change ‖d α‖ = _
  rw [Lp.norm_toLp, Lp.norm_def, he]

private theorem compact_difference_value_norm_le {n : ℕ} (B outer : LocalBall n)
    (v : IntegerSobolev B 1) (K : Set (Space n)) (hK : IsCompact K)
    (hKB : K ⊆ B.carrier) (hKO : K ⊆ outer.carrier)
    (hv : ∀ᵐ x ∂volume.restrict B.carrier, x ∉ K → value v x = 0)
    (k : Fin n) (t : ℝ) (ht : t ≠ 0) (w : IntegerSobolev outer 1)
    (hw : ∀ᵐ x ∂volume.restrict outer.carrier, value w x =
      -differenceQuotient k (-t)
        (KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K (value v)) x) :
    ‖value w‖ ≤ ‖gradient v k‖ := by
  let T : LocalBall n := ⟨outer.dimension_pos, outer.center,
    outer.radius + |t| + 1, by have := outer.radius_pos; positivity⟩
  have hOT : outer.carrier ⊆ T.carrier := by
    apply Metric.ball_subset_ball
    change outer.radius ≤ outer.radius + |t| + 1
    linarith [abs_nonneg t]
  obtain ⟨V, hV⟩ := compact_sobolev_extension B T v K hK hKB (hKO.trans hOT) hv
  have hglobal : zeroExtension (value V) =ᵐ[volume]
      KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K (value v) := by
    filter_upwards [(ae_restrict_iff' Metric.isOpen_ball.measurableSet).1 (hV (zeroIndex n 1)).1]
      with x hx
    by_cases hxT : x ∈ T.carrier
    · simp [zeroExtension, hxT, hx hxT, value]
    · have hn : x ∉ K := fun h => hxT (hOT (hKO h))
      simp [zeroExtension, hxT, KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension, hn]
  have hquot : differenceQuotient k (-t) (zeroExtension (value V)) =ᵐ[volume]
      differenceQuotient k (-t)
        (KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K (value v)) := by
    filter_upwards [hglobal, (measurePreserving_add_right volume
      ((-t) • EuclideanSpace.single k 1)).quasiMeasurePreserving.ae_eq_comp hglobal] with x hx hy
    change zeroExtension (value V) (x + (-t) • EuclideanSpace.single k 1) = _ at hy
    simp only [differenceQuotient, hx, hy, Function.comp_apply]
  obtain ⟨q, hq, _, hb⟩ := localized_difference_quotient outer T rfl
    (by change outer.radius < outer.radius + |t| + 1; linarith [abs_nonneg t])
    V k (-t) (neg_ne_zero.mpr ht) (by
      change |-t| < outer.radius + |t| + 1 - outer.radius
      rw [abs_neg]
      linarith)
  have he : value w = -(value q) := by
    apply Lp.ext
    filter_upwards [hw, hq, Lp.coeFn_neg (value q),
      hquot.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hy hz hq'
    simp only [Pi.neg_apply] at hz
    rw [hx, hz, hy, hq']
  rw [he, norm_neg]
  exact hb.trans_eq (hV (firstIndex k)).2

private theorem cutoff_leibniz_norm_bound {n : ℕ} (B : LocalBall n)
    (η : TestFunction B.toOpens ℝ ⊤) (q v : IntegerSobolev B 1)
    (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1) (G : ℝ) (hG : 0 ≤ G)
    (hd : ∀ (j : Fin n) x,
      ‖coordinateDerivativeList [j] (fun y => (η y : ℂ)) x‖ ≤ G)
    (hv : ∀ j : Fin n, ∀ᵐ x ∂volume.restrict B.carrier,
      gradient v j x = (η x : ℂ) ^ 2 * gradient q j x +
        2 * (η x : ℂ) * coordinateDerivativeList [j] (fun y => (η y : ℂ)) x * value q x)
    (k : Fin n) :
    ‖gradient v k‖ ≤ Real.sqrt (∑ j : Fin n, ∫ x in B.carrier,
      ‖(η x : ℂ) * gradient q j x‖ ^ 2) + 2 * G * ‖value q‖ := by
  let μ := volume.restrict B.carrier
  let a : Space n → ℂ := fun x => (η x : ℂ) * gradient q k x
  have hηm : MemLp (fun x => (η x : ℂ)) ⊤ μ := η.memLp_top.ofReal
  have ha : MemLp a 2 μ := hηm.fun_mul (Lp.memLp _)
  let b : Space n → ℂ := fun x => 2 * (η x : ℂ) *
    coordinateDerivativeList [k] (fun y => (η y : ℂ)) x
  have hdm : MemLp (coordinateDerivativeList [k] (fun y => (η y : ℂ))) ⊤ μ := by
    let ψ := TestFunction.postcompCLM Complex.ofRealCLM η
    let dψ : TestFunction B.toOpens ℂ ⊤ := TestFunction.lineDerivCLM ℝ (EuclideanSpace.single k 1) ψ
    have hp : MemLp (fun x => dψ x) ⊤ μ := dψ.memLp_top
    convert hp using 1
    ext x
    dsimp [dψ]
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ (by simp)]
    rfl
  have hb : MemLp b ⊤ μ := (hηm.const_mul (2 : ℂ)).fun_mul hdm
  have hηb : ∀ᵐ x ∂μ, ‖(η x : ℂ)‖ ≤ 1 := by
    filter_upwards with x
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hη x).1]
    exact (hη x).2
  have hbb : ∀ᵐ x ∂μ, ‖b x‖ ≤ 2 * G := by
    filter_upwards [hηb] with x hx
    dsimp [b]
    simp only [norm_mul]
    rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
    calc
      2 * ‖(η x : ℂ)‖ * ‖coordinateDerivativeList [k] (fun y => (η y : ℂ)) x‖ ≤
          2 * 1 * G := by gcongr; exact hd k x
      _ = 2 * G := by ring
  have hηa : MemLp (fun x => (η x : ℂ) * a x) 2 μ := hηm.fun_mul ha
  have hbq : MemLp (fun x => b x * value q x) 2 μ := hb.fun_mul (Lp.memLp _)
  have he : gradient v k = hηa.toLp (fun x => (η x : ℂ) * a x) +
      hbq.toLp (fun x => b x * value q x) := by
    apply Lp.ext
    filter_upwards [hv k, Lp.coeFn_add (hηa.toLp _) (hbq.toLp _),
      hηa.coeFn_toLp, hbq.coeFn_toLp] with x hx hs ha' hb'
    simp only [Pi.add_apply] at hs
    rw [hs, ha', hb', hx]
    dsimp [a, b]
    ring
  have haa := l2_multiplier_bound (fun x => (η x : ℂ)) a ha hηm 1 zero_le_one hηb
  have hba := l2_multiplier_bound b (fun x => value q x) (Lp.memLp _) hb (2 * G) (by positivity) hbb
  have hqn : ‖(Lp.memLp (value q)).toLp (fun x => value q x)‖ = ‖value q‖ := by
    congr 1
    apply Lp.ext
    exact MemLp.coeFn_toLp _
  have hsq : ‖ha.toLp a‖ ^ 2 = ∫ x in B.carrier, ‖a x‖ ^ 2 := by
    rw [KPContLocalEnergy.SobolevEnergyEstimates.lp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp] with x hx
    rw [hx]
  have hE : ‖ha.toLp a‖ ^ 2 ≤ ∑ j : Fin n, ∫ x in B.carrier,
      ‖(η x : ℂ) * gradient q j x‖ ^ 2 := by
    rw [hsq]
    exact Finset.single_le_sum (f := fun j : Fin n => ∫ x in B.carrier, ‖(η x : ℂ) * gradient q j x‖ ^ 2)
      (fun j _ => integral_nonneg (fun x => sq_nonneg _)) (Finset.mem_univ k)
  have hEn : 0 ≤ ∑ j : Fin n, ∫ x in B.carrier,
      ‖(η x : ℂ) * gradient q j x‖ ^ 2 := le_trans (sq_nonneg _) hE
  have han : ‖ha.toLp a‖ ≤ Real.sqrt (∑ j : Fin n, ∫ x in B.carrier,
      ‖(η x : ℂ) * gradient q j x‖ ^ 2) := by
    nlinarith [Real.sq_sqrt hEn, Real.sqrt_nonneg (∑ j : Fin n, ∫ x in B.carrier,
      ‖(η x : ℂ) * gradient q j x‖ ^ 2), norm_nonneg (ha.toLp a)]
  simp only [one_mul] at haa
  rw [he]
  exact (norm_add_le _ _).trans (by simpa only [one_mul, hqn] using add_le_add (haa.trans han) hba)

private theorem difference_test_value_norm_bound {n : ℕ} (mid outer : LocalBall n)
    (hsub : mid.carrier ⊆ outer.carrier) (η : TestFunction mid.toOpens ℝ ⊤)
    (q : IntegerSobolev mid 1) (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (G : ℝ) (hG : 0 ≤ G)
    (hd : ∀ (j : Fin n) x,
      ‖coordinateDerivativeList [j] (fun y => (η y : ℂ)) x‖ ≤ G)
    (k : Fin n) (t : ℝ) (ht : t ≠ 0)
    (w : IntegerSobolev outer 1)
    (hw : ∀ᵐ x ∂volume.restrict outer.carrier,
      value w x = -differenceQuotient k (-t) (FluxRaw.cutoffValue η q) x) :
    ‖value w‖ ≤ Real.sqrt (∑ j : Fin n, ∫ x in mid.carrier,
      ‖(η x : ℂ) * gradient q j x‖ ^ 2) + 2 * G * ‖value q‖ := by
  obtain ⟨v, hv, hvg⟩ := KPContLocalEnergy.SobolevEnergyEstimates.multiply_smooth_compact mid η q
  let K := tsupport (fun x => η x)
  have hK : IsCompact K := η.hasCompactSupport
  have hKB : K ⊆ mid.carrier := η.tsupport_subset
  have hvs : ∀ᵐ x ∂volume.restrict mid.carrier, x ∉ K → value v x = 0 := by
    filter_upwards [hv] with x hx hn
    rw [hx, image_eq_zero_of_notMem_tsupport hn]
    simp
  have hext := FluxRaw.DifferenceTestAtoms.global_indicator_ae K hKB (value v)
    (fun x => (η x : ℂ) ^ 2 * value q x) hv (fun x hn => by
      rw [image_eq_zero_of_notMem_tsupport hn]
      simp)
  have hquot : differenceQuotient k (-t)
      (KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K (value v)) =ᵐ[volume]
      differenceQuotient k (-t) (FluxRaw.cutoffValue η q) := by
    filter_upwards [hext, (measurePreserving_add_right volume
      ((-t) • EuclideanSpace.single k 1)).quasiMeasurePreserving.ae_eq_comp hext] with x hx hy
    simp only [differenceQuotient, Function.comp_apply, FluxRaw.cutoffValue] at *
    rw [hx, hy]
  have hwb : ∀ᵐ x ∂volume.restrict outer.carrier, value w x =
      -differenceQuotient k (-t)
        (KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K (value v)) x := by
    filter_upwards [hw, hquot.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hy
    exact hx.trans (congrArg Neg.neg hy.symm)
  have hvg' : ∀ j : Fin n, ∀ᵐ x ∂volume.restrict mid.carrier,
      gradient v j x = (η x : ℂ) ^ 2 * gradient q j x +
        2 * (η x : ℂ) * coordinateDerivativeList [j] (fun y => (η y : ℂ)) x * value q x := by
    intro j
    filter_upwards [hvg j] with x hx
    exact hx
  exact (compact_difference_value_norm_le mid outer v K hK hKB
    (hKB.trans hsub) hvs k t ht w hwb).trans
      (cutoff_leibniz_norm_bound mid η q v hη G hG hd hvg' k)

private theorem bounded_l2_pairing {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (a f g : X → ℂ) (ha : MemLp a ⊤ μ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (C : ℝ) (hC : 0 ≤ C) (hab : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    ‖∫ x, a x * f x * star (g x) ∂μ‖ ≤ C * ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have haf : MemLp (fun x => a x * f x) 2 μ := ha.fun_mul hf
  exact (l2_pairing_bound _ _ haf hg).trans
    (mul_le_mul_of_nonneg_right (l2_multiplier_bound a f hf ha C hC hab) (norm_nonneg _))

private theorem density_pairing_bound {n : ℕ} {outer : LocalBall n}
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ)
    (hcρ : 0 < cρ) (f g : BallL2 outer) :
    ‖∫ x in outer.carrier, (D.density x : ℂ) * f x * star (g x)‖ ≤ Cρ * ‖f‖ * ‖g‖ := by
  have hC : 0 ≤ Cρ := by
    have hx : outer.center ∈ outer.carrier := by
      simpa [LocalBall.carrier] using outer.radius_pos
    exact hcρ.le.trans ((D.density_bounds _ hx).1.trans (D.density_bounds _ hx).2)
  have hρ : MemLp (fun x => (D.density x : ℂ)) ⊤ (volume.restrict outer.carrier) := by
    apply memLp_top_of_bound
      ((Complex.continuous_ofReal.comp_continuousOn D.density_smooth.continuousOn).aestronglyMeasurable
        Metric.isOpen_ball.measurableSet) Cρ
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (hcρ.le.trans (D.density_bounds x hx).1)]
    exact (D.density_bounds x hx).2
  have hbound : ∀ᵐ x ∂volume.restrict outer.carrier, ‖(D.density x : ℂ)‖ ≤ Cρ := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (hcρ.le.trans (D.density_bounds x hx).1)]
    exact (D.density_bounds x hx).2
  have hfn : (Lp.memLp f).toLp (fun x => f x) = f := by
    apply Lp.ext
    exact MemLp.coeFn_toLp _
  have hgn : (Lp.memLp g).toLp (fun x => g x) = g := by
    apply Lp.ext
    exact MemLp.coeFn_toLp _
  simpa only [hfn, hgn] using bounded_l2_pairing _ _ _ hρ (Lp.memLp f) (Lp.memLp g) Cρ hC hbound

private theorem difference_lower_order_bound {n : ℕ} (mid outer : LocalBall n)
    (hsub : mid.carrier ⊆ outer.carrier) (η : TestFunction mid.toOpens ℝ ⊤)
    (q : IntegerSobolev mid 1) (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (G M : ℝ) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hd : ∀ (j : Fin n) x,
      ‖coordinateDerivativeList [j] (fun y => (η y : ℂ)) x‖ ≤ G)
    (k : Fin n) (t : ℝ) (ht : t ≠ 0)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ) (hcρ : 0 < cρ)
    (z : ℂ) (hz : ‖z‖ ≤ M) (u : IntegerSobolev outer 1) (h : BallL2 outer)
    (hq : ‖value q‖ ≤ u.sobolevNorm) (w : IntegerSobolev outer 1)
    (hw : ∀ᵐ x ∂volume.restrict outer.carrier,
      value w x = -differenceQuotient k (-t) (FluxRaw.cutoffValue η q) x) :
    let N := u.sobolevNorm + ‖h‖
    let E := ∑ j : Fin n, ∫ x in mid.carrier, ‖(η x : ℂ) * gradient q j x‖ ^ 2
    ‖z * (∫ x in outer.carrier, (D.density x : ℂ) * value u x * star (value w x)) +
      (∫ x in outer.carrier, (D.density x : ℂ) * h x * star (value w x))‖ ≤
      (2 * G * |Cρ| * (M + 1)) * N ^ 2 + |Cρ| * (M + 1) * N * Real.sqrt E := by
  dsimp only
  let N := u.sobolevNorm + ‖h‖
  let E := ∑ j : Fin n, ∫ x in mid.carrier, ‖(η x : ℂ) * gradient q j x‖ ^ 2
  have hu0 : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  have hN : 0 ≤ N := add_nonneg hu0 (norm_nonneg _)
  have hu : ‖value u‖ ≤ N := (component_norm_le_sobolevNorm u (zeroIndex n 1)).trans (by
    dsimp [N]; linarith [norm_nonneg h])
  have hh : ‖h‖ ≤ N := by dsimp [N]; linarith [hu0]
  have hqN : ‖value q‖ ≤ N := hq.trans (by dsimp [N]; linarith [norm_nonneg h])
  have hwN : ‖value w‖ ≤ Real.sqrt E + 2 * G * N := by
    exact (difference_test_value_norm_bound mid outer hsub η q hη G hG hd k t ht w hw).trans
      (by dsimp [E]; gcongr)
  have hf := (density_pairing_bound D hcρ (value u) (value w)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Cρ) (norm_nonneg _)) (norm_nonneg _))
  have hg := (density_pairing_bound D hcρ h (value w)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Cρ) (norm_nonneg _)) (norm_nonneg _))
  calc
    _ ≤ ‖z‖ * ‖∫ x in outer.carrier, (D.density x : ℂ) * value u x * star (value w x)‖ +
        ‖∫ x in outer.carrier, (D.density x : ℂ) * h x * star (value w x)‖ := by
      simpa only [norm_mul] using norm_add_le
        (z * (∫ x in outer.carrier, (D.density x : ℂ) * value u x * star (value w x)))
        (∫ x in outer.carrier, (D.density x : ℂ) * h x * star (value w x))
    _ ≤ M * (|Cρ| * N * (Real.sqrt E + 2 * G * N)) +
        |Cρ| * N * (Real.sqrt E + 2 * G * N) := by
      gcongr
      · exact hf.trans (by gcongr)
      · exact hg.trans (by gcongr)
    _ = _ := by dsimp [N, E]; ring

private theorem norm_toLp_self {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : (Lp.memLp f).toLp (fun x => f x) = f := by
  apply Lp.ext
  exact MemLp.coeFn_toLp _

private theorem l2_sq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : X → ℂ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

private theorem integrated_flux_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (n : ℕ) (a b : Fin n → Fin n → X → ℂ) (F H S U : Fin n → X → ℂ)
    (ha : ∀ i j, MemLp (a i j) ⊤ μ) (hb : ∀ i j, MemLp (b i j) ⊤ μ)
    (hF : ∀ j, MemLp (F j) 2 μ) (hH : ∀ j, MemLp (H j) 2 μ)
    (hS : ∀ j, MemLp (S j) 2 μ) (hU : ∀ j, MemLp (U j) 2 μ)
    (K L V W T c : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hW : 0 ≤ W) (hT : 0 ≤ T)
    (hab : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ K)
    (hbb : ∀ i j, ∀ᵐ x ∂μ, ‖b i j x‖ ≤ L)
    (hFn : ∀ j, ‖(hF j).toLp (F j)‖ ≤ V)
    (hHn : ∀ j, ‖(hH j).toLp (H j)‖ ≤ W)
    (hSn : ∀ j, ‖(hS j).toLp (S j)‖ ≤ V + W)
    (hUn : ∀ j, ‖(hU j).toLp (U j)‖ ≤ T)
    (hco : ∀ᵐ x ∂μ, c * (∑ j, ‖F j x‖ ^ 2) ≤
      (∑ i, ∑ j, a i j x * F j x * star (F i x)).re) :
    c * (∑ j, ∫ x, ‖F j x‖ ^ 2 ∂μ) ≤
      (∫ x, ∑ i, ∑ j, (a i j x * F j x * star (F i x) +
        a i j x * F j x * star (H i x) + b i j x * U j x * star (S i x)) ∂μ).re +
      (n : ℝ) ^ 2 * (K * V * W + L * T * (V + W)) := by
  classical
  let p := fun i j x => a i j x * F j x * star (F i x)
  let e := fun i j x => a i j x * F j x * star (H i x) + b i j x * U j x * star (S i x)
  have hp : ∀ i j, Integrable (p i j) μ := fun i j =>
    (show MemLp (fun x => a i j x * F j x) 2 μ from (ha i j).fun_mul (hF j)).integrable_mul (hF i).star
  have he : ∀ i j, Integrable (e i j) μ := fun i j =>
    ((show MemLp (fun x => a i j x * F j x) 2 μ from (ha i j).fun_mul (hF j)).integrable_mul (hH i).star).add
      ((show MemLp (fun x => b i j x * U j x) 2 μ from (hb i j).fun_mul (hU j)).integrable_mul (hS i).star)
  have hpi : Integrable (fun x => ∑ i, ∑ j, p i j x) μ :=
    integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hp i j))
  have hei : Integrable (fun x => ∑ i, ∑ j, e i j x) μ :=
    integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => he i j))
  have hmain : c * (∑ j, ∫ x, ‖F j x‖ ^ 2 ∂μ) ≤ (∫ x, ∑ i, ∑ j, p i j x ∂μ).re := by
    change _ ≤ RCLike.re (∫ x, ∑ i, ∑ j, p i j x ∂μ)
    rw [← integral_re hpi, ← integral_finset_sum _ (fun j _ => by
      simpa using (hF j).integrable_norm_rpow (by norm_num) (by norm_num)), ← integral_const_mul]
    apply integral_mono_ae
    · exact (integrable_finset_sum _ (fun j _ => by
        simpa using (hF j).integrable_norm_rpow (by norm_num) (by norm_num))).const_mul c
    · exact hpi.re
    · exact hco
  have heb : ∀ i j, ‖∫ x, e i j x ∂μ‖ ≤ K * V * W + L * T * (V + W) := by
    intro i j
    dsimp only [e]
    change ‖∫ x, (a i j x * F j x * star (H i x) + b i j x * U j x * star (S i x)) ∂μ‖ ≤ _
    have h1 : Integrable (fun x => a i j x * F j x * star (H i x)) μ :=
      (show MemLp (fun x => a i j x * F j x) 2 μ from (ha i j).fun_mul (hF j)).integrable_mul (hH i).star
    have h2 : Integrable (fun x => b i j x * U j x * star (S i x)) μ :=
      (show MemLp (fun x => b i j x * U j x) 2 μ from (hb i j).fun_mul (hU j)).integrable_mul (hS i).star
    rw [integral_add h1 h2]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (bounded_l2_pairing _ _ _ (ha i j) (hF j) (hH i) K hK (hab i j)).trans (by gcongr; exact hFn j; exact hHn i)
    · exact (bounded_l2_pairing _ _ _ (hb i j) (hU j) (hS i) L hL (hbb i j)).trans (by gcongr; exact hUn j; exact hSn i)
  have herr : ‖∫ x, ∑ i, ∑ j, e i j x ∂μ‖ ≤ (n : ℝ) ^ 2 * (K * V * W + L * T * (V + W)) := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => he i j))]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (K * V * W + L * T * (V + W)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [integral_finset_sum _ (fun j _ => he i j)]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => heb i j))
      _ = _ := by simp [pow_two, mul_assoc]; ring
  have hsplit : (∫ x, ∑ i, ∑ j, (p i j x + e i j x) ∂μ) =
      (∫ x, ∑ i, ∑ j, p i j x ∂μ) + ∫ x, ∑ i, ∑ j, e i j x ∂μ := by
    simp_rw [Finset.sum_add_distrib]
    exact integral_add hpi hei
  have hre : -(∫ x, ∑ i, ∑ j, e i j x ∂μ).re ≤ (n : ℝ)^2 * (K * V * W + L * T * (V + W)) :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans herr)
  have hz := congrArg Complex.re hsplit
  simp only [Complex.add_re] at hz
  dsimp only [p, e] at hz hmain hre
  simp only [add_assoc] at hz ⊢
  linarith

set_option maxHeartbeats 1600000 in

theorem uniform_difference_energy_inequality (n : ℕ) (hn : 0 < n)
    (r R cρ Cρ κ Λ L M G : ℝ) (hr : 0 < r) (hrR : r < R)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hL : 0 ≤ L) (hM : 0 ≤ M) (hG : 0 < G) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (mid outer : LocalBall n),
      mid.center = outer.center → mid.radius = (r + R) / 2 → outer.radius = R →
      ∀ η : TestFunction mid.toOpens ℝ ⊤,
        (∀ x, 0 ≤ η x ∧ η x ≤ 1) →
        (∀ (j : Fin n) (x : Space n),
          ‖coordinateDerivativeList [j] (fun y => (η y : ℂ)) x‖ ≤ G) →
        Metric.cthickening ((R - r) / 8) (tsupport (fun x => η x)) ⊆ mid.carrier →
        ∀ D : Coefficients outer cρ Cρ κ Λ,
          (∀ x ∈ outer.carrier, ∀ i j k : Fin n,
            ‖fderiv ℝ (fun y => D.density y * D.matrix y i j) x
              (EuclideanSpace.single k 1)‖ ≤ L) →
          ∀ z : ℂ, ‖z‖ ≤ M → ∀ (u : IntegerSobolev outer 1) (h : BallL2 outer),
            ∀ (k : Fin n) (t : ℝ), t ≠ 0 → |t| < (R - r) / 8 →
            ∀ (q : IntegerSobolev mid 1) (w : IntegerSobolev outer 1),
              (∀ᵐ x ∂volume.restrict mid.carrier,
                value q x = differenceQuotient k t (zeroExtension (value u)) x) →
              (∀ j : Fin n, ∀ᵐ x ∂volume.restrict mid.carrier,
                gradient q j x = differenceQuotient k t (zeroExtension (gradient u j)) x) →
              (∀ᵐ x ∂volume.restrict outer.carrier,
                value w x = -differenceQuotient k (-t)
                  (mid.carrier.indicator (fun y => (η y : ℂ) ^ 2 * value q y)) x) →
              (∀ j : Fin n, ∀ᵐ x ∂volume.restrict outer.carrier,
                gradient w j x = -differenceQuotient k (-t)
                  (mid.carrier.indicator (fun y => (η y : ℂ) ^ 2 * gradient q j y +
                    2 * (η y : ℂ) * coordinateDerivativeList [j]
                      (fun a => (η a : ℂ)) y * value q y)) x) →
              ((∫ x in outer.carrier, (D.density x : ℂ) *
                ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x * star (gradient w i x)) -
                z * (∫ x in outer.carrier, (D.density x : ℂ) * value u x * star (value w x)) =
                  ∫ x in outer.carrier, (D.density x : ℂ) * h x * star (value w x)) →
              let E := ∑ j : Fin n, ∫ x in mid.carrier,
                ‖(η x : ℂ) * differenceQuotient k t (zeroExtension (gradient u j)) x‖ ^ 2
              cρ * κ * E ≤ A * (u.sobolevNorm + ‖h‖) ^ 2 +
                B * (u.sobolevNorm + ‖h‖) * Real.sqrt E := by
  classical
  let K := |Cρ| * |Λ|
  let A := (2 * G * |Cρ| * (M + 1)) + (n : ℝ)^2 * (L * (2 * G))
  let B := |Cρ| * (M + 1) + (n : ℝ)^2 * (K * (2 * G) + L)
  refine ⟨A, B, by dsimp [A]; positivity, by dsimp [B, K]; positivity, ?_⟩
  intro mid outer hc hmr hor η hη hd hsupport D hD z hz u h k t ht hsmall q w hq hqg hw hwg hpde
  dsimp only
  have hgap : mid.radius < outer.radius := by rw [hmr, hor]; linarith
  have hstep : |t| < outer.radius - mid.radius := by rw [hmr, hor]; linarith
  have hsub : mid.carrier ⊆ outer.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hc]
    exact Metric.ball_subset_ball hgap.le
  have hshift : ∀ x ∈ mid.carrier, x + t • EuclideanSpace.single k 1 ∈ outer.carrier :=
    fun x hx => safe_segment_mem mid outer hc k t hstep hx (le_refl _)
  have hsafe : Metric.cthickening |t| (tsupport (fun x => η x)) ⊆ mid.carrier :=
    (Metric.cthickening_mono hsmall.le _).trans hsupport
  have hflux := FluxRaw.difference_flux_identity_of_tested mid outer hc hgap η k t ht hstep
    hsafe hcρ hκ D z u h q hq hqg w hw hwg hpde
  let μ := volume.restrict mid.carrier
  let N := u.sobolevNorm + ‖h‖
  let E := ∑ j : Fin n, ∫ x in mid.carrier, ‖(η x : ℂ) * gradient q j x‖ ^ 2
  have hN : 0 ≤ N := add_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hqN : ‖value q‖ ≤ N :=
    ((quotient_value_norm_le mid outer hc hgap u k t ht hstep q hq).trans
      (gradient_norm_le_sobolevNorm u k)).trans (by dsimp [N]; linarith [norm_nonneg h])
  have hqU : ‖value q‖ ≤ u.sobolevNorm :=
    (quotient_value_norm_le mid outer hc hgap u k t ht hstep q hq).trans
      (gradient_norm_le_sobolevNorm u k)
  let d := fun j x => coordinateDerivativeList [j] (fun y => (η y : ℂ)) x
  let F := fun j x => (η x : ℂ) * gradient q j x
  let H := fun j x => 2 * d j x * value q x
  let S := fun j x => F j x + H j x
  let U := fun j x => gradient u j x
  let a := fun i j x => ((D.density (x + t • EuclideanSpace.single k 1) *
      D.matrix (x + t • EuclideanSpace.single k 1) i j : ℝ) : ℂ)
  let b := fun i j x => differenceQuotient k t
      (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) x * (η x : ℂ)
  have hηb : ∀ x, ‖(η x : ℂ)‖ ≤ 1 := by
    intro x
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hη x).1]
    exact (hη x).2
  have hab : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ K := by
    intro i j
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hm := hshift x hx
    dsimp [a, K]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    apply mul_le_mul
    · rw [abs_of_nonneg (hcρ.le.trans (D.density_bounds _ hm).1)]
      exact (D.density_bounds _ hm).2.trans (le_abs_self _)
    · exact (D.matrix_entry_bound hκ.le _ hm i j).trans (le_abs_self _)
    · exact abs_nonneg _
    · exact abs_nonneg _
  have hbb : ∀ i j, ∀ᵐ x ∂μ, ‖b i j x‖ ≤ L := by
    intro i j
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    dsimp [b]
    rw [norm_mul]
    have hbound := FluxRaw.DifferenceTestAtoms.weighted_coefficient_difference_bound mid outer D hD hc k t ht hstep x hx i j
    exact (mul_le_mul hbound (hηb x) (norm_nonneg _) hL).trans_eq (mul_one _)
  have hac : ∀ i j, ContinuousOn (a i j) mid.carrier := by
    intro i j
    have hcont := Complex.continuous_ofReal.comp_continuousOn
      (D.density_smooth.mul (D.matrix_smooth i j)).continuousOn
    exact hcont.comp (by fun_prop) hshift
  have hbc : ∀ i j, ContinuousOn (b i j) mid.carrier := by
    intro i j
    have hcont := Complex.continuous_ofReal.comp_continuousOn
      (D.density_smooth.mul (D.matrix_smooth i j)).continuousOn
    have htcont := hcont.comp (by fun_prop) hshift
    have h0cont := hcont.mono hsub
    exact (continuousOn_const.mul (htcont.sub h0cont)).mul
      (Complex.continuous_ofReal.comp η.continuous).continuousOn
  have ha : ∀ i j, MemLp (a i j) ⊤ μ := fun i j => memLp_top_of_bound
    ((hac i j).aestronglyMeasurable Metric.isOpen_ball.measurableSet) K (hab i j)
  have hb : ∀ i j, MemLp (b i j) ⊤ μ := fun i j => memLp_top_of_bound
    ((hbc i j).aestronglyMeasurable Metric.isOpen_ball.measurableSet) L (hbb i j)
  have hdm : ∀ j, MemLp (d j) ⊤ μ := by
    intro j
    let ψ := TestFunction.postcompCLM Complex.ofRealCLM η
    let dψ : TestFunction mid.toOpens ℂ ⊤ := TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j 1) ψ
    have hp : MemLp (fun x => dψ x) ⊤ μ := dψ.memLp_top
    convert hp using 1
    ext x
    dsimp [dψ]
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ (by simp)]
    rfl
  have hF : ∀ j, MemLp (F j) 2 μ := fun j => η.memLp_top.ofReal.fun_mul (Lp.memLp _)
  have hH : ∀ j, MemLp (H j) 2 μ := fun j => ((hdm j).const_mul (2 : ℂ)).fun_mul (Lp.memLp _)
  have hS : ∀ j, MemLp (S j) 2 μ := fun j => (hF j).add (hH j)
  have hU : ∀ j, MemLp (U j) 2 μ := fun j => (Lp.memLp (gradient u j)).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))
  have hFn : ∀ j, ‖(hF j).toLp (F j)‖ ≤ Real.sqrt E := by
    intro j
    have hs : ‖(hF j).toLp (F j)‖ ^ 2 ≤ E := by
      rw [l2_sq_integral]
      exact Finset.single_le_sum (f := fun i : Fin n => ∫ x in mid.carrier, ‖F i x‖ ^ 2)
        (fun i _ => integral_nonneg (fun x => sq_nonneg _)) (Finset.mem_univ j)
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg E, norm_nonneg ((hF j).toLp (F j))]
  have hHn : ∀ j, ‖(hH j).toLp (H j)‖ ≤ 2 * G * N := by
    intro j
    have hh := l2_multiplier_bound (fun x => 2 * d j x) (fun x => value q x)
      (Lp.memLp _) ((hdm j).const_mul (2 : ℂ)) (2 * G) (by positivity) (by
        filter_upwards with x
        rw [norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left (hd j x) (by norm_num))
    rw [norm_toLp_self] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hqN (by positivity))
  have hSn : ∀ j, ‖(hS j).toLp (S j)‖ ≤ Real.sqrt E + 2 * G * N := by
    intro j
    have he : (hS j).toLp (S j) = (hF j).toLp (F j) + (hH j).toLp (H j) := by
      apply Lp.ext
      filter_upwards [(hS j).coeFn_toLp, (hF j).coeFn_toLp, (hH j).coeFn_toLp,
        Lp.coeFn_add ((hF j).toLp (F j)) ((hH j).toLp (H j))] with x hs hf hh he
      simpa only [Pi.add_apply, S, hs, hf, hh] using he.symm
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (hFn j) (hHn j))
  have hUn : ∀ j, ‖(hU j).toLp (U j)‖ ≤ N := by
    intro j
    have hh : ‖(hU j).toLp (U j)‖ ^ 2 ≤ ‖gradient u j‖ ^ 2 := by
      rw [l2_sq_integral, KPContLocalEnergy.SobolevEnergyEstimates.lp_norm_sq_eq_integral]
      exact setIntegral_mono_set (by simpa [U, IntegrableOn] using (Lp.memLp (gradient u j)).integrable_norm_rpow (by norm_num) (by norm_num))
        (by filter_upwards with x; exact sq_nonneg _) (Filter.Eventually.of_forall hsub)
    have hn : ‖(hU j).toLp (U j)‖ ≤ ‖gradient u j‖ := by nlinarith [norm_nonneg (gradient u j), norm_nonneg ((hU j).toLp (U j))]
    exact (hn.trans (gradient_norm_le_sobolevNorm u j)).trans (by dsimp [N]; linarith [norm_nonneg h])
  have hco : ∀ᵐ x ∂μ, cρ * κ * (∑ j, ‖F j x‖ ^ 2) ≤
      (∑ i, ∑ j, a i j x * F j x * star (F i x)).re := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hp := D.complex_ellipticity _ (hshift x hx) (fun j => F j x)
    have hρ := D.density_bounds _ (hshift x hx)
    have hn : 0 ≤ ∑ j, ‖F j x‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have he : (∑ i, ∑ j, a i j x * F j x * star (F i x)) =
      (D.density (x + t • EuclideanSpace.single k 1) : ℂ) *
        (∑ i, ∑ j, (D.matrix (x + t • EuclideanSpace.single k 1) i j : ℂ) * F j x * star (F i x)) := by
      simp only [a, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]
    rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      _ ≤ D.density (x + t • EuclideanSpace.single k 1) * (κ * ∑ j, ‖F j x‖^2) := by
        nlinarith [mul_le_mul_of_nonneg_right hρ.1 (mul_nonneg hκ.le hn)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (hcρ.le.trans hρ.1)
  have hib := integrated_flux_bound n a b F H S U ha hb hF hH hS hU K L
    (Real.sqrt E) (2 * G * N) N (cρ * κ) (by dsimp [K]; positivity) hL
    (Real.sqrt_nonneg _) (by positivity) hN hab hbb hFn hHn hSn hUn hco
  have hiEq : (∫ x, ∑ i, ∑ j, (a i j x * F j x * star (F i x) +
        a i j x * F j x * star (H i x) + b i j x * U j x * star (S i x)) ∂μ) =
      z * (∫ x in outer.carrier, (D.density x : ℂ) * value u x * star (value w x)) +
        (∫ x in outer.carrier, (D.density x : ℂ) * h x * star (value w x)) := by
    rw [← hflux]
    apply integral_congr_ae
    have hqgall := (Filter.eventually_all).2 hqg
    filter_upwards [hqgall, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hm
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [FluxRaw.cutoffGradient, Set.indicator_of_mem hm]
    rw [← hx j]
    dsimp [a, b, F, H, S, U, d]
    simp only [map_add, map_mul, map_pow, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [hiEq] at hib
  have hlower := difference_lower_order_bound mid outer hsub η q hη G M hG.le hM hd
    k t ht D hcρ z hz u h hqU w hw
  have hreal := (Complex.re_le_norm _).trans hlower
  have henergy : (∑ j : Fin n, ∫ x in mid.carrier,
      ‖(η x : ℂ) * differenceQuotient k t (zeroExtension (gradient u j)) x‖ ^ 2) = E := by
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [hqg j] with x hx
    rw [hx]
  rw [henergy]
  dsimp only [E, F] at hib
  dsimp only at hlower hreal
  have heq : A * N^2 + B * N * Real.sqrt E =
      (2 * G * |Cρ| * (M + 1)) * N^2 + |Cρ| * (M + 1) * N * Real.sqrt E +
        (n : ℝ)^2 * (K * Real.sqrt E * (2 * G * N) + L * N * (Real.sqrt E + 2 * G * N)) := by
    dsimp [A, B]; ring
  change cρ * κ * E ≤ A * N^2 + B * N * Real.sqrt E
  rw [heq]
  exact hib.trans (add_le_add hreal le_rfl)

end DedekindZetaZeroFree.WeakH2.CoerciveDifference

end
