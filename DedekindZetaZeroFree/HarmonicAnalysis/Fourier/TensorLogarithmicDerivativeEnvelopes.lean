module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.NormSheetLogarithmicOperators
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.TraceSchwartzTensors

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

namespace FourierEnvelopePrivate

def complexEuler (g : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (1 / 2 : ℝ) • SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.apply (E := ℂ) ℝ ℂ).flip
    (Function.HasTemperateGrowth.id') (SchwartzMap.fderivCLM ℝ ℂ ℂ g)

@[simp] theorem complexEuler_apply (g : SchwartzMap ℂ ℂ) (z : ℂ) :
    complexEuler g z = (1 / 2 : ℝ) • fderiv ℝ g z z := rfl

theorem hasDerivAt_complexNormFlow (g : SchwartzMap ℂ ℂ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => g ((Real.exp (v / 2) : ℂ) * z))
      (complexEuler g ((Real.exp (u / 2) : ℂ) * z)) u := by
  have h : HasDerivAt (fun v : ℝ => Real.exp (v / 2))
      (Real.exp (u / 2) / 2) u :=
    by simpa [div_eq_mul_inv] using ((hasDerivAt_id u).div_const 2).exp
  have hc := h.ofReal_comp.mul_const z
  have hd := g.differentiableAt.hasFDerivAt.comp_hasDerivAt u hc
  convert hd using 1
  · rfl
  · rw [complexEuler_apply, ← map_smul]
    congr 1
    simp [smul_eq_mul]
    ring

theorem iteratedDeriv_complexNormFlow (g : SchwartzMap ℂ ℂ) (k : ℕ) (z : ℂ) (u : ℝ) :
    iteratedDeriv k (fun v : ℝ => g ((Real.exp (v / 2) : ℂ) * z)) u =
      ((complexEuler^[k]) g) ((Real.exp (u / 2) : ℂ) * z) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hf : iteratedDeriv k (fun v : ℝ => g ((Real.exp (v / 2) : ℂ) * z)) =
        fun v : ℝ => ((complexEuler^[k]) g) ((Real.exp (v / 2) : ℂ) * z) := funext ih
    rw [hf, (hasDerivAt_complexNormFlow ((complexEuler^[k]) g) z u).deriv,
      Function.iterate_succ_apply']

set_option backward.isDefEq.respectTransparency false in
private theorem mixed_flow_complex (A : SArithmeticData F) (w : InfinitePlace F)
    (u : ℝ) (x : SLocalProduct F A.Sf) (v : {v : InfinitePlace F // v.IsComplex}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (complexNormFlowRaw A w u x).1).2 v =
      if v.val = w then (Real.exp (u / 2) : ℂ) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v
      else (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v := by
  change InfinitePlace.Completion.extensionEmbedding v.val
      (Function.update x.1 w
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
          (Real.exp (u / 2) : ℂ) * x.1 w) v.val) = _
  by_cases hv : v.val = w
  · subst w
    simp only [Function.update_self, ↓reduceIte]
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v.val))
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v.val)).symm
        (Real.exp (u / 2) : ℂ) * x.1 v.val) = _
    rw [map_mul, RingEquiv.apply_symm_apply]
    rfl
  · rw [Function.update_of_ne hv, if_neg hv]
    rfl

private theorem real_places_empty (A : SArithmeticData F) :
    IsEmpty {v : InfinitePlace F // v.IsReal} :=
  ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place v.val)) v.property⟩

private theorem tensor_flow_factor (A : SArithmeticData F) (w : InfinitePlace F)
    (g : (v : {v : InfinitePlace F // v.IsComplex}) → SchwartzMap ℂ ℂ)
    (u : ℝ) (x : SLocalProduct F A.Sf) :
    (∏ v, g v ((InfiniteAdeleRing.ringEquiv_mixedSpace F (complexNormFlowRaw A w u x).1).2 v)) =
      g ⟨w, A.complex_place w⟩ ((Real.exp (u / 2) : ℂ) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 ⟨w, A.complex_place w⟩) *
      ∏ v ∈ Finset.univ.erase ⟨w, A.complex_place w⟩,
        g v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ⟨w, A.complex_place w⟩)]
  congr 1
  · rw [mixed_flow_complex]; simp
  · apply Finset.prod_congr rfl
    intro v hv
    have hne : v.val ≠ w := by
      intro h
      exact (Finset.mem_erase.mp hv).1 (Subtype.ext h)
    rw [mixed_flow_complex, if_neg hne]

 theorem logDerivative_isSchwartzTensor (A : SArithmeticData F) (w : InfinitePlace F)
    (k : ℕ) (f : SLocalProduct F A.Sf → ℂ)
    (hf : ProbeSheetVerticalDecay.IsSchwartzTensor F A.Sf f) :
    ProbeSheetVerticalDecay.IsSchwartzTensor F A.Sf (logDerivativeRaw A w k f) := by
  obtain ⟨c, gr, gc, gf, hgf, hf⟩ := hf
  letI := real_places_empty A
  let v₀ : {v : InfinitePlace F // v.IsComplex} := ⟨w, A.complex_place w⟩
  let gc' := Function.update gc v₀ ((complexEuler^[k]) (gc v₀))
  refine ⟨c, gr, gc', gf, hgf, ?_⟩
  intro x
  have hflow : (fun u => f (complexNormFlowRaw A w u x)) =
      fun u => c * (gc v₀ ((Real.exp (u / 2) : ℂ) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v₀) *
        ∏ v ∈ Finset.univ.erase v₀,
          gc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) *
        ∏ v : ↥A.Sf, gf v (x.2 v) := by
    funext u
    rw [hf, tensor_flow_factor]
    simp [complexNormFlowRaw, v₀, mul_assoc]
  unfold logDerivativeRaw
  rw [hflow]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field,
    iteratedDeriv_complexNormFlow, zero_div, Real.exp_zero, Complex.ofReal_one, one_mul]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  have hp : (∏ v, gc' v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) =
      ((complexEuler^[k]) (gc v₀)) ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v₀) *
      ∏ v ∈ Finset.univ.erase v₀, gc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v₀)]
    simp only [gc', Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [Function.update_of_ne (Finset.mem_erase.mp hv).1]
  rw [hp]
  ring

private theorem schwartz_envelope (g : SchwartzMap ℂ ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖g z‖ ≤ C * (1 + ‖z‖ ^ 2) ^ (-(N : ℝ)) := by
  let C := (2 : ℝ) ^ N *
    (SchwartzMap.seminorm ℂ 0 0 g + SchwartzMap.seminorm ℂ (2*N) 0 g)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z
  have hpos : 0 < (1 + ‖z‖ ^ 2) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ hpos]
  by_cases hz : ‖z‖ ≤ 1
  · have hp : (1 + ‖z‖ ^ 2) ^ N ≤ (2 : ℝ) ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      have : ‖z‖ ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      norm_num only [one_pow] at this
      linarith
    calc
      ‖g z‖ * (1 + ‖z‖ ^ 2) ^ N ≤
          SchwartzMap.seminorm ℂ 0 0 g * (2 : ℝ) ^ N :=
        mul_le_mul (g.norm_le_seminorm ℂ z) hp (by positivity) (apply_nonneg _ _)
      _ ≤ C := by dsimp [C]; nlinarith [apply_nonneg (SchwartzMap.seminorm ℂ (2*N) 0) g,
        (show (0 : ℝ) ≤ 2 ^ N by positivity)]
  · have hr : 1 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z, lt_of_not_ge hz]
    have hp : (1 + ‖z‖ ^ 2) ^ N ≤ (2 * ‖z‖ ^ 2) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    have hb := g.norm_pow_mul_le_seminorm ℂ (2*N) z
    calc
      ‖g z‖ * (1 + ‖z‖ ^ 2) ^ N ≤ ‖g z‖ * (2 * ‖z‖ ^ 2) ^ N :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = (2 : ℝ) ^ N * (‖z‖ ^ (2*N) * ‖g z‖) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ (2 : ℝ) ^ N * SchwartzMap.seminorm ℂ (2*N) 0 g :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ C := by dsimp [C]; nlinarith [apply_nonneg (SchwartzMap.seminorm ℂ 0 0) g,
        (show (0 : ℝ) ≤ 2 ^ N by positivity)]

private theorem finite_bound {E : Type} [NormedAddCommGroup E]
    (g : E → ℂ) (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ B R : ℝ, 0 ≤ B ∧ 0 ≤ R ∧ (∀ z, ‖g z‖ ≤ B) ∧
      (∀ z, R < ‖z‖ → g z = 0) := by
  obtain ⟨b, hb⟩ := (hc.isCompact_range hg.continuous).exists_bound_of_continuousOn
    continuous_id.continuousOn
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : E)
  refine ⟨max b 0, max r 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro z
    exact (hb (g z) (Set.mem_range_self z)).trans (le_max_left _ _)
  · intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hh := hr hs
    rw [Metric.mem_closedBall, dist_zero_right] at hh
    exact (not_lt_of_ge (hh.trans (le_max_left _ _))) hz

end FourierEnvelopePrivate

def radialFiniteEnvelopeRaw (A : SArithmeticData F) (N : ℕ) (R : ℝ)
    (x : SLocalProduct F A.Sf) : ℝ :=
  (∏ v : InfinitePlace F, (1 + ‖x.1 v‖ ^ (2 : ℕ)) ^ (-(N : ℝ))) *
    (if ∀ v : ↥A.Sf, ‖x.2 v‖ ≤ R then 1 else 0)

set_option maxHeartbeats 1000000 in

theorem raw_fourier_log_derivative_envelope
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (w : InfinitePlace F) (k N : ℕ)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) :
    ∃ M R : ℝ, 0 ≤ M ∧ 0 < R ∧ ∀ x : SLocalProduct F A.Sf,
      ‖logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0) x‖ ≤
        M * radialFiniteEnvelopeRaw A N R x := by
  classical
  have hf := FourierEnvelopePrivate.logDerivative_isSchwartzTensor A w k
    (ProbeWeight.fourier F A.Sf e μ W0)
    (ProbeSheetVerticalDecay.fourier_isSchwartzTensor A.Sf e he hne μ hμ W0 hW0 hcompact)
  obtain ⟨c, gr, gc, gf, hgf, hf⟩ := hf
  letI : IsEmpty {v : InfinitePlace F // v.IsReal} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place v.val)) v.property⟩
  choose C hC hgc using fun v => FourierEnvelopePrivate.schwartz_envelope (gc v) N
  choose B R hB hR hgb hgzero using fun v =>
    FourierEnvelopePrivate.finite_bound (gf v) (hgf v).1 (hgf v).2
  let R₀ : ℝ := 1 + ∑ v, R v
  have hsR : 0 ≤ ∑ v : ↥A.Sf, R v := Finset.sum_nonneg (fun i _ => hR i)
  have hR₀ : 0 < R₀ := by dsimp only [R₀]; linarith
  have hRR (v : ↥A.Sf) : R v ≤ R₀ := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := R)
      (fun i _ => hR i) (Finset.mem_univ v)
    dsimp only [R₀]
    linarith
  let M : ℝ := ‖c‖ * (∏ v, C v) * ∏ v, B v
  have hpc : 0 ≤ ∏ v, C v := Finset.prod_nonneg (fun v _ => hC v)
  have hpb : 0 ≤ ∏ v, B v := Finset.prod_nonneg (fun v _ => hB v)
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (norm_nonneg c) hpc) hpb
  refine ⟨M, R₀, hM, hR₀, ?_⟩
  intro x
  have hnorm (v : {v : InfinitePlace F // v.IsComplex}) :
      ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v‖ = ‖x.1 v.val‖ := by
    change ‖InfinitePlace.Completion.extensionEmbedding v.val (x.1 v.val)‖ = _
    exact (InfinitePlace.Completion.isometry_extensionEmbedding v.val).norm_map_of_map_zero
      (map_zero _) _
  have hp : (∏ v : {v : InfinitePlace F // v.IsComplex},
        (1 + ‖x.1 v.val‖ ^ 2) ^ (-(N : ℝ))) =
      ∏ v : InfinitePlace F, (1 + ‖x.1 v‖ ^ 2) ^ (-(N : ℝ)) := by
    let ev : InfinitePlace F ≃ {v : InfinitePlace F // v.IsComplex} :=
      ⟨fun v => ⟨v, A.complex_place v⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
    exact (Finset.prod_equiv ev (fun _ => by simp) (fun _ _ => rfl)).symm
  rw [hf]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, norm_mul,
    norm_prod]
  by_cases hx : ∀ v : ↥A.Sf, ‖x.2 v‖ ≤ R₀
  · have harch : (∏ v, ‖gc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)‖) ≤
        (∏ v, C v) * ∏ v : InfinitePlace F,
          (1 + ‖x.1 v‖ ^ 2) ^ (-(N : ℝ)) := by
      rw [← hp, ← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro v _
      simpa only [hnorm] using hgc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)
    have hfin : (∏ v : ↥A.Sf, ‖gf v (x.2 v)‖) ≤ ∏ v, B v :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v _ => hgb v (x.2 v))
    have hupper : 0 ≤ (∏ v, C v) * ∏ v : InfinitePlace F,
        (1 + ‖x.1 v‖ ^ 2) ^ (-(N : ℝ)) := mul_nonneg hpc (Finset.prod_nonneg (fun _ _ => by positivity))
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_left harch (norm_nonneg c)) hfin
      (by positivity) (mul_nonneg (norm_nonneg c) hupper)
    simpa [radialFiniteEnvelopeRaw, hx, M, mul_assoc, mul_left_comm, mul_comm] using hh
  · obtain ⟨v, hv⟩ := not_forall.mp hx
    have hvz : gf v (x.2 v) = 0 :=
      hgzero v (x.2 v) ((hRR v).trans_lt (lt_of_not_ge hv))
    have hprod : (∏ v : ↥A.Sf, ‖gf v (x.2 v)‖) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hvz])
    simp only [hprod, radialFiniteEnvelopeRaw, if_neg hx, mul_zero, le_refl]

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
