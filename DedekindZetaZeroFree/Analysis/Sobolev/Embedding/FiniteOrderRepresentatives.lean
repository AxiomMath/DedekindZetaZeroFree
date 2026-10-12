module

public import DedekindZetaZeroFree.Analysis.Sobolev.Embedding.InteriorJetBounds

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets

open MeasureTheory KPContLocalNorm

namespace Regularization

open MeasureTheory KPContLocalNorm Filter Topology
open scoped Convolution

private theorem compact_lp_integrable {n : ℕ} (f : Lp ℂ 2 (volume : Measure (Space n)))
    {K : Set (Space n)} (hK : IsCompact K) (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    Integrable (fun x => f x) volume := by
  have he : K.indicator (fun x => f x) =ᵐ[volume] (fun x => f x) := by
    filter_upwards [hf] with x hx
    by_cases h : x ∈ K <;> simp [h, hx]
  apply Integrable.congr _ he
  apply (integrableOn_iff_integrable_of_support_subset Set.support_indicator_subset).mp
  exact ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hK |>.indicator hK.measurableSet

private theorem convolution_eq_real {n : ℕ} (φ : Space n → ℝ) (h : Space n → ℂ) :
    ((fun y => (φ y : ℂ)) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] h) =
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) := by
  ext x
  simp only [convolution_def, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, Complex.real_smul]

private theorem weak_derivative_convolution {n k : ℕ} (g : Interior.GlobalWeakSobolev n k)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (α : MultiIndex n k) :
    coordinateDerivative α
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) y)) =
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => g.derivatives α y)) := by
  ext x
  have heq := Interior.global_weak_coordinateDerivative_convolution g (fun y => (φ y : ℂ))
    (Complex.ofRealCLM.contDiff.comp hφ)
    (hc.comp_left (g := Complex.ofReal) rfl) α x
  simpa only [convolution_eq_real] using heq

def regularizedJet {n k : ℕ} (g : Interior.GlobalWeakSobolev n k)
    (α : MultiIndex n k) (t : ℕ) : Lp ℂ 2 (volume : Measure (Space n)) :=
  ∫ y, (Interior.radiusBump n (1 / (t + 1 : ℕ)) (by positivity)).normed volume y •
    KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 (g.derivatives α) y

theorem regularizedJet_tendsto {n k : ℕ} (g : Interior.GlobalWeakSobolev n k)
    (α : MultiIndex n k) :
    Tendsto (regularizedJet g α) atTop (𝓝 (g.derivatives α)) := by
  apply KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.averaged_translateL2_tendsto
  change Tendsto (fun t : ℕ => (1 : ℝ) / (t + 1 : ℕ)) atTop (𝓝 0)
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem regularizedJet_ae {n k : ℕ} (g : Interior.GlobalWeakSobolev n k)
    {K : Set (Space n)} (hK : IsCompact K)
    (hg : ∀ α : MultiIndex n k, ∀ᵐ x ∂volume, x ∉ K → g.derivatives α x = 0)
    (α : MultiIndex n k) (t : ℕ) :
    (fun x => regularizedJet g α t x) =ᵐ[volume]
      coordinateDerivative α (Interior.mollify (Interior.unitBump n |>.normed volume) 1
        (fun x => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x) t) := by
  have hto : (Lp.memLp (g.derivatives α)).toLp (fun x => g.derivatives α x) =
      g.derivatives α := Lp.toLp_coeFn _ _
  have he := KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.averaged_translateL2_ae
    (fun x => g.derivatives α x) (Lp.memLp _) (compact_lp_integrable _ hK (hg α))
    (Interior.radiusBump n (1 / (t + 1 : ℕ)) (by positivity))
  rw [hto] at he
  have hm : Interior.mollify (Interior.unitBump n |>.normed volume) 1
      (fun x => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x) t =
      (Interior.radiusBump n (1 / (t + 1 : ℕ)) (by positivity)).normed volume
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (fun x => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x) := by
    ext x
    exact Interior.mollify_eq_radiusBump_convolution _ (by positivity) _ x
  rw [hm, weak_derivative_convolution g _ (ContDiffBump.contDiff_normed _) (ContDiffBump.hasCompactSupport_normed _)]
  exact he

open MeasureTheory KPContLocalNorm Filter Topology
open scoped Convolution

private theorem smooth_list {n : ℕ} (l : List (Fin n)) {f : Space n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

private theorem derivativeList_sub {n : ℕ} (l : List (Fin n)) {f h : Space n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    coordinateDerivativeList l (f - h) = coordinateDerivativeList l f - coordinateDerivativeList l h := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    ext x
    simp only [coordinateDerivativeList, ih]
    rw [fderiv_sub ((smooth_list l hf).differentiable (by simp) x)
      ((smooth_list l hh).differentiable (by simp) x)]
    rfl

def mollifiedValue {n k : ℕ} (g : Interior.GlobalWeakSobolev n k) (t : ℕ) : Space n → ℂ :=
  Interior.mollify ((Interior.unitBump n).normed volume) 1
    (fun x => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x) t

theorem mollifiedValue_smooth {n k : ℕ} (g : Interior.GlobalWeakSobolev n k) (t : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedValue g t) := by
  have he : mollifiedValue g t =
      (Interior.radiusBump n (1 / (t + 1 : ℕ)) (by positivity)).normed volume
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (fun x => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x) := by
    ext x
    exact Interior.mollify_eq_radiusBump_convolution _ (by positivity) _ x
  rw [he]
  exact ContDiffBump.hasCompactSupport_normed _ |>.contDiff_convolution_left _
    (ContDiffBump.contDiff_normed _) ((Lp.memLp _).locallyIntegrable (by norm_num))

theorem mollifiedValue_support {n k : ℕ} (g : Interior.GlobalWeakSobolev n k)
    {K : Set (Space n)} (hK : IsCompact K)
    (hg : ∀ α : MultiIndex n k, ∀ᵐ x ∂volume, x ∉ K → g.derivatives α x = 0) (t : ℕ) :
    tsupport (mollifiedValue g t) ⊆ Metric.cthickening 1 K := by
  let a := Interior.radiusBump n (1 / (t + 1 : ℕ)) (by positivity)
  let f := g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k)
  have he : K.indicator (fun x => f x) =ᵐ[volume] (fun x => f x) := by
    filter_upwards [hg (⟨fun _ => 0, by simp⟩ : MultiIndex n k)] with x hx
    by_cases h : x ∈ K <;> simp [h, hx, f]
  have hm : mollifiedValue g t = (a.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => f x)) := by
    ext x
    exact Interior.mollify_eq_radiusBump_convolution _ (by positivity) _ x
  rw [hm, ← convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
    (Filter.Eventually.of_forall fun y => (rfl : a.normed volume y = a.normed volume y)) he]
  exact (KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.convolution_tsupport_subset_thickening a hK
    (closure_minimal Set.support_indicator_subset hK.isClosed) le_rfl).trans
      (Metric.cthickening_mono (by dsimp [a, Interior.radiusBump]; exact div_le_self (by norm_num) (by norm_cast; omega)) K)

theorem mollifiedValue_jet_difference {n k : ℕ} (g : Interior.GlobalWeakSobolev n k)
    {K : Set (Space n)} (hK : IsCompact K)
    (hg : ∀ α : MultiIndex n k, ∀ᵐ x ∂volume, x ∉ K → g.derivatives α x = 0)
    (α : MultiIndex n k) (t s : ℕ) :
    (∫ x, ‖coordinateDerivative α (mollifiedValue g t - mollifiedValue g s) x‖ ^ 2) =
      ‖regularizedJet g α t - regularizedJet g α s‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, coordinateDerivative,
    derivativeList_sub _ (mollifiedValue_smooth g t) (mollifiedValue_smooth g s)]
  apply integral_congr_ae
  filter_upwards [regularizedJet_ae g hK hg α t, regularizedJet_ae g hK hg α s,
    Lp.coeFn_sub (regularizedJet g α t) (regularizedJet g α s)] with x ht hs hts
  rw [hts]
  simp only [Pi.sub_apply]
  rw [ht, hs]
  rfl

theorem mollifiedValue_jets_uniformCauchy {n : ℕ} (m : ℕ)
    (g : Interior.GlobalWeakSobolev n (m + n)) (hn : 0 < n)
    {K : Set (Space n)} (hK : IsCompact K)
    (hg : ∀ α : MultiIndex n (m + n), ∀ᵐ x ∂volume, x ∉ K → g.derivatives α x = 0)
    (α : MultiIndex n m) :
    UniformCauchySeqOn (fun t => coordinateDerivative α (mollifiedValue g t)) atTop Set.univ := by
  obtain ⟨lower, upper, hbox, hcontain⟩ := Interior.exists_box_for_compact_thickening K hK
  obtain ⟨C, hC, hbound⟩ := full_mixed_integral_le_sobolev hn lower upper hbox m
  have hlim : Tendsto (fun p : ℕ × ℕ =>
      ∑ β : MultiIndex n (m + n), ‖regularizedJet g β p.1 - regularizedJet g β p.2‖ ^ 2)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have hβ (β : MultiIndex n (m + n)) : Tendsto (fun p : ℕ × ℕ =>
        ‖regularizedJet g β p.1 - regularizedJet g β p.2‖ ^ 2)
        (atTop ×ˢ atTop) (𝓝 0) := by
      have h' := ((regularizedJet_tendsto g β).comp tendsto_fst).sub
        ((regularizedJet_tendsto g β).comp tendsto_snd)
      simpa only [Function.comp_apply, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using h'.norm.pow 2
    simpa using tendsto_finset_sum Finset.univ (fun β _ => hβ β)
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have he : (0 : ℝ) < (ε / C) ^ 2 := sq_pos_of_pos (div_pos hε hC)
  have ht := hlim.eventually (eventually_lt_nhds he)
  rw [prod_atTop_atTop_eq, Filter.eventually_atTop_prod_self'] at ht
  obtain ⟨N, hN⟩ := ht
  refine ⟨N, ?_⟩
  intro t ht s hs x _
  have hts := hN t ht s hs
  have hsm : HasCompactSupport (mollifiedValue g t - mollifiedValue g s) := by
    apply HasCompactSupport.sub
    · exact (hK.cthickening (r := (1 : ℝ))).of_isClosed_subset isClosed_closure (mollifiedValue_support g hK hg t)
    · exact (hK.cthickening (r := (1 : ℝ))).of_isClosed_subset isClosed_closure (mollifiedValue_support g hK hg s)
  have hsub : tsupport (mollifiedValue g t - mollifiedValue g s) ⊆
      {x | ∀ i, lower i < x i ∧ x i < upper i} :=
    (tsupport_sub ..).trans (Set.union_subset
      ((mollifiedValue_support g hK hg t).trans hcontain)
      ((mollifiedValue_support g hK hg s).trans hcontain))
  have hb := hbound (mollifiedValue g t - mollifiedValue g s)
    ((mollifiedValue_smooth g t).sub (mollifiedValue_smooth g s)) hsm hsub α
  have hpoint := norm_le_integral_full_mixed_derivative hn (coordinateDerivative α
    (mollifiedValue g t - mollifiedValue g s))
    (smooth_list α.directions ((mollifiedValue_smooth g t).sub (mollifiedValue_smooth g s)))
    (by
      have h : HasCompactSupport (coordinateDerivativeList α.directions
          (mollifiedValue g t - mollifiedValue g s)) := by
        induction α.directions with
        | nil => exact hsm
        | cons i l ih => exact ih.fderiv_apply ℝ _
      exact h) x
  simp_rw [mollifiedValue_jet_difference g hK hg] at hb
  have hsqrt : Real.sqrt (∑ β : MultiIndex n (m + n),
      ‖regularizedJet g β t - regularizedJet g β s‖ ^ 2) < ε / C := by
    exact (Real.sqrt_lt' (div_pos hε hC)).mpr hts
  have hmul : C * Real.sqrt (∑ β : MultiIndex n (m + n),
      ‖regularizedJet g β t - regularizedJet g β s‖ ^ 2) < ε := by
    calc
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hsqrt hC
      _ = ε := mul_div_cancel₀ ε hC.ne'
  have htotal := hpoint.trans hb |>.trans_lt hmul
  simpa only [dist_eq_norm, coordinateDerivative,
    derivativeList_sub _ (mollifiedValue_smooth g t) (mollifiedValue_smooth g s), Pi.sub_apply] using htotal

theorem mollifiedValue_jets_uniformLimit {n : ℕ} (m : ℕ)
    (g : Interior.GlobalWeakSobolev n (m + n)) (hn : 0 < n)
    {K : Set (Space n)} (hK : IsCompact K)
    (hg : ∀ α : MultiIndex n (m + n), ∀ᵐ x ∂volume, x ∉ K → g.derivatives α x = 0) :
    ∃ J : MultiIndex n m → Space n → ℂ,
      ∀ α, TendstoUniformly (fun t => coordinateDerivative α (mollifiedValue g t)) (J α) atTop ∧
        Continuous (J α) := by
  have hc (α : MultiIndex n m) (x : Space n) :
      CauchySeq (fun t => coordinateDerivative α (mollifiedValue g t) x) :=
    (mollifiedValue_jets_uniformCauchy m g hn hK hg α).cauchySeq (Set.mem_univ x)
  choose J hJ using fun α x => cauchySeq_tendsto_of_complete (hc α x)
  refine ⟨J, ?_⟩
  intro α
  have hu : TendstoUniformly (fun t => coordinateDerivative α (mollifiedValue g t)) (J α) atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact (mollifiedValue_jets_uniformCauchy m g hn hK hg α).tendstoUniformlyOn_of_tendsto
      (fun x _ => hJ α x)
  refine ⟨hu, hu.continuous ?_⟩
  exact (Filter.Eventually.of_forall fun t => (smooth_list α.directions (mollifiedValue_smooth g t)).continuous).frequently

theorem mollifiedValue_uniformLimit_ae {n k : ℕ} (g : Interior.GlobalWeakSobolev n k)
    {K : Set (Space n)} (hK : IsCompact K)
    (hg : ∀ α : MultiIndex n k, ∀ᵐ x ∂volume, x ∉ K → g.derivatives α x = 0)
    (α : MultiIndex n k) (J : Space n → ℂ)
    (hJ : TendstoUniformly (fun t => coordinateDerivative α (mollifiedValue g t)) J atTop) :
    J =ᵐ[volume] (fun x => g.derivatives α x) := by
  have hm := tendstoInMeasure_of_tendsto_Lp (regularizedJet_tendsto g α)
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have he : ∀ᵐ x ∂volume, ∀ t : ℕ,
      regularizedJet g α t x = coordinateDerivative α (mollifiedValue g t) x := by
    exact ae_all_iff.mpr fun t => regularizedJet_ae g hK hg α t
  filter_upwards [hae, he] with x hx he
  have hj := (hJ.tendsto_at x).comp hns.tendsto_atTop
  apply tendsto_nhds_unique hj
  exact hx.congr (fun t => he (ns t))

open MeasureTheory KPContLocalNorm Filter Topology

theorem global_weak_sobolev_continuous_representative {n : ℕ} (m : ℕ)
    (g : Interior.GlobalWeakSobolev n (m + n)) (hn : 0 < n)
    {K : Set (Space n)} (hK : IsCompact K)
    (hg : ∀ α : MultiIndex n (m + n), ∀ᵐ x ∂volume, x ∉ K → g.derivatives α x = 0) :
    ∃ f : Space n → ℂ, Continuous f ∧
      f =ᵐ[volume] (fun x => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x) ∧
      TendstoUniformly (mollifiedValue g) f atTop := by
  obtain ⟨J, hJ⟩ := mollifiedValue_jets_uniformLimit m g hn hK hg
  let α : MultiIndex n m := ⟨fun _ => 0, by simp⟩
  have hz (k : ℕ) (f : Space n → ℂ) :
      coordinateDerivative (⟨fun _ => 0, by simp⟩ : MultiIndex n k) f = f := by
    have he : MultiIndex.directions (⟨fun _ => 0, by simp⟩ : MultiIndex n k) = [] := by
      simp only [MultiIndex.directions, Fin.val_zero, List.replicate_zero]
      induction List.finRange n with
      | nil => rfl
      | cons i l ih => simpa using ih
    rw [coordinateDerivative, he]
    rfl
  have hj : TendstoUniformly (mollifiedValue g) (J α) atTop := by
    simpa only [α, hz] using (hJ α).1
  refine ⟨J α, (hJ α).2, ?_, hj⟩
  apply mollifiedValue_uniformLimit_ae g hK hg (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) (J α)
  simpa only [hz] using hj

open KPContLocalNorm MeasureTheory Filter Topology

 def assemble {n : ℕ} (v : Fin n → ℂ) : Space n →L[ℝ] ℂ :=
  ∑ i, (EuclideanSpace.proj i).smulRight (v i)

private theorem fderiv_assemble {n : ℕ} {f : Space n → ℂ} (hf : Differentiable ℝ f) (x : Space n) :
    fderiv ℝ f x = assemble (fun i => coordinateDerivativeList [i] f x) := by
  apply ContinuousLinearMap.ext
  intro y
  have he := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr y
  rw [← he]
  simp [assemble, coordinateDerivativeList, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, map_sum]

private theorem uniform_sum {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (F : Fin n → ℕ → Space n → E) (G : Fin n → Space n → E)
    (h : ∀ i, TendstoUniformly (F i) (G i) atTop) :
    TendstoUniformly (fun t x => ∑ i, F i t x) (fun x => ∑ i, G i x) atTop := by
  have hs (s : Finset (Fin n)) : TendstoUniformly (fun t x => ∑ i ∈ s, F i t x)
      (fun x => ∑ i ∈ s, G i x) atTop := by
    induction s using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds (x := (0 : E))).tendstoUniformly_const
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i).add ih
  exact hs Finset.univ

private theorem assemble_uniform {n : ℕ} (F : Fin n → ℕ → Space n → ℂ)
    (G : Fin n → Space n → ℂ) (h : ∀ i, TendstoUniformly (F i) (G i) atTop) :
    TendstoUniformly (fun t x => assemble (fun i => F i t x))
      (fun x => assemble (fun i => G i x)) atTop := by
  apply uniform_sum
  intro i
  exact ((ContinuousLinearMap.smulRightL ℝ (Space n) ℂ (EuclideanSpace.proj i)).uniformContinuous).comp_tendstoUniformly (h i)

private theorem list_append {n : ℕ} (l l' : List (Fin n)) (f : Space n → ℂ) :
    coordinateDerivativeList (l ++ l') f = coordinateDerivativeList l (coordinateDerivativeList l' f) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, coordinateDerivativeList, ih]

private theorem list_smooth {n : ℕ} (l : List (Fin n)) {f : Space n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_of_uniform_coordinate_jets {n : ℕ} (m : ℕ)
    (F : ℕ → Space n → ℂ) (hF : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (F t))
    (hjet : ∀ l : List (Fin n), l.length ≤ m →
      ∃ J : Space n → ℂ, Continuous J ∧ TendstoUniformly (fun t => coordinateDerivativeList l (F t)) J atTop)
    (f : Space n → ℂ) (hf : TendstoUniformly F f atTop) : ContDiff ℝ m f := by
  induction m generalizing F f with
  | zero =>
    exact contDiff_zero.mpr (hf.continuous (Filter.Eventually.of_forall fun t => (hF t).continuous).frequently)
  | succ m ih =>
    have hfirst (i : Fin n) := hjet [i] (by simp)
    choose J hJ hj using hfirst
    have hji (i : Fin n) : ContDiff ℝ m (J i) := by
      apply ih (fun t => coordinateDerivativeList [i] (F t)) (fun t => list_smooth [i] (hF t))
        (fun l hl => ?_) (J i) (hj i)
      obtain ⟨g, hg, htg⟩ := hjet (l ++ [i]) (by simp; omega)
      exact ⟨g, hg, by simpa only [list_append] using htg⟩
    have hd : ContDiff ℝ m (fun x => assemble (fun i => J i x)) := by
      unfold assemble
      apply ContDiff.sum
      intro i _
      exact (ContinuousLinearMap.smulRightL ℝ (Space n) ℂ (EuclideanSpace.proj i)).contDiff.comp (hji i)
    have hu := assemble_uniform (fun i t x => coordinateDerivativeList [i] (F t) x) J hj
    have hdf : TendstoUniformly (fun t => fderiv ℝ (F t))
        (fun x => assemble (fun i => J i x)) atTop := by
      simpa only [← fderiv_assemble ((hF _).differentiable (by simp))] using hu
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by simp]
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨_, hd, fun x => ?_⟩
    exact hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      (hdf.tendstoUniformlyOn.tendstoLocallyUniformlyOn)
      (fun t x _ => ((hF t).differentiable (by simp) x).hasFDerivAt)
      (fun x _ => hf.tendsto_at x) (Set.mem_univ x)

private theorem list_perm {n : ℕ} {l k : List (Fin n)} (hp : l.Perm k)
    {f : Space n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    coordinateDerivativeList l f = coordinateDerivativeList k f := by
  induction hp with
  | nil => rfl
  | cons i hp ih => simp only [coordinateDerivativeList, ih]
  | swap i j l =>
    have hs := list_smooth l hf
    funext x
    simp only [coordinateDerivativeList]
    have hd : Differentiable ℝ (fderiv ℝ (coordinateDerivativeList l f)) :=
      (hs.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiable (by norm_num)
    simpa [fderiv_clm_apply (hd x) (differentiableAt_const _)] using
      (hs.contDiffAt (x := x) |>.isSymmSndFDerivAt (by simp)).eq
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  | trans hp hq ih ij => exact ih.trans ij

private theorem list_as_index {n m : ℕ} (l : List (Fin n)) (hl : l.length ≤ m) :
    ∃ α : MultiIndex n m, l.Perm α.directions := by
  classical
  have hsum : ∑ i : Fin n, l.count i = l.length := by
    rw [← List.sum_toFinset_count_eq_length l]
    symm
    apply Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => ?_)
    simpa using List.count_eq_zero.mpr (by simpa using hi)
  let α : MultiIndex n m := ⟨fun i => ⟨l.count i, by have := List.count_le_length (a := i) (l := l); omega⟩,
    by simpa only [hsum] using hl⟩
  refine ⟨α, List.perm_iff_count.mpr (fun i => ?_)⟩
  rw [MultiIndex.directions, List.count_flatMap, ← List.sum_toFinset _ (List.nodup_finRange n)]
  simp [α, Function.comp_def, List.count_replicate]

theorem global_weak_sobolev_finite_order_representative {n : ℕ} (m : ℕ)
    (g : Interior.GlobalWeakSobolev n (m + n)) (hn : 0 < n)
    {K : Set (Space n)} (hK : IsCompact K)
    (hg : ∀ α : MultiIndex n (m + n), ∀ᵐ x ∂volume, x ∉ K → g.derivatives α x = 0) :
    ∃ f : Space n → ℂ, ContDiff ℝ m f ∧
      f =ᵐ[volume] (fun x => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x) := by
  obtain ⟨f, hfc, hfae, hft⟩ := global_weak_sobolev_continuous_representative m g hn hK hg
  obtain ⟨J, hJ⟩ := mollifiedValue_jets_uniformLimit m g hn hK hg
  refine ⟨f, contDiff_of_uniform_coordinate_jets m (mollifiedValue g)
    (mollifiedValue_smooth g) ?_ f hft, hfae⟩
  intro l hl
  obtain ⟨α, hα⟩ := list_as_index l hl
  refine ⟨J α, (hJ α).2, ?_⟩
  have he (t : ℕ) := list_perm hα (mollifiedValue_smooth g t)
  simp_rw [he]
  exact (hJ α).1

private theorem inner_representative {n : ℕ} (A B : LocalBall n)
    (hAB : Metric.closedBall A.center A.radius ⊆ B.carrier) (m : ℕ)
    (u : IntegerSobolev B (m + n)) :
    ∃ f : Space n → ℂ, ContDiff ℝ m f ∧
      f =ᵐ[volume.restrict A.carrier]
        (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x) := by
  obtain ⟨χ, hχ, hχc, hχs, hχr, hχone⟩ := exists_smooth_interior_cutoff A B hAB
  obtain ⟨L, hL, hloc⟩ := Interior.cutoff_global_weak_sobolev B (m + n) χ hχ hχc hχs
  obtain ⟨g, hgae, hgs, hgn⟩ := hloc u
  obtain ⟨f, hf, hfae⟩ := global_weak_sobolev_finite_order_representative m g B.dimension_pos
    hχc (hgs)
  refine ⟨f, hf, ?_⟩
  have he := ae_restrict_of_ae (s := A.carrier) (hfae.trans hgae)
  filter_upwards [he, ae_restrict_mem (show MeasurableSet A.carrier from Metric.isOpen_ball.measurableSet)] with x hx hAx
  rw [hx, Set.indicator_of_mem (hAB (Metric.ball_subset_closedBall hAx)),
    (hχone x (Metric.ball_subset_closedBall hAx)).eq_of_nhds, one_smul]

 def innerBall {n : ℕ} (B : LocalBall n) (j : ℕ) : LocalBall n where
  dimension_pos := B.dimension_pos
  center := B.center
  radius := B.radius * (1 - 1 / (j + 2 : ℕ))
  radius_pos := by
    apply mul_pos B.radius_pos
    have h : (1 : ℝ) / (j + 2 : ℕ) < 1 := by
      apply (div_lt_one (by positivity)).mpr
      norm_cast; omega
    linarith

private theorem innerBall_nested {n : ℕ} (B : LocalBall n) (j : ℕ) :
    Metric.closedBall (innerBall B j).center (innerBall B j).radius ⊆ B.carrier := by
  intro x hx
  change dist x B.center < B.radius
  apply lt_of_le_of_lt hx
  change B.radius * (1 - 1 / (j + 2 : ℕ)) < B.radius
  have h : (0 : ℝ) < 1 / (j + 2 : ℕ) := by positivity
  nlinarith [B.radius_pos]

private theorem innerBall_cover {n : ℕ} (B : LocalBall n) :
    (⋃ j : ℕ, (innerBall B j).carrier) = B.carrier := by
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro j
    exact Metric.ball_subset_closedBall.trans (innerBall_nested B j)
  · intro x hx
    have ht : Tendsto (fun j : ℕ => B.radius * (1 - 1 / (j + 2 : ℕ))) atTop (𝓝 B.radius) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h' : Tendsto (fun j : ℕ => 1 / (j + 2 : ℕ) : ℕ → ℝ) atTop (𝓝 0) := by
        convert h.comp (tendsto_add_atTop_nat 1) using 1
        ext j
        simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        congr 1 <;> ring
      simpa using (tendsto_const_nhds (x := B.radius)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub h')
    obtain ⟨j, hj⟩ := (ht.eventually (eventually_gt_nhds hx)).exists
    exact Set.mem_iUnion.mpr ⟨j, hj⟩

theorem local_weak_sobolev_finite_order_representative {n : ℕ}
    (B : LocalBall n) (m : ℕ) (u : IntegerSobolev B (m + n)) :
    ∃ f : Space n → ℂ, ContDiffOn ℝ m f B.carrier ∧
      f =ᵐ[volume.restrict B.carrier]
        (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x) := by
  classical
  have hrep (j : ℕ) := inner_representative (innerBall B j) B (innerBall_nested B j) m u
  choose fs hs hae using hrep
  let U : ℕ → Set (Space n) := fun j => (innerBall B j).carrier
  have hU (j : ℕ) : IsOpen (U j) := Metric.isOpen_ball
  have hcover : (⋃ j, U j) = B.carrier := innerBall_cover B
  have hcompat (j k : ℕ) : Set.EqOn (fs j) (fs k) (U j ∩ U k) := by
    have hj : fs j =ᵐ[volume.restrict (U j ∩ U k)]
        (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x) :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hae j)
    have hk : fs k =ᵐ[volume.restrict (U j ∩ U k)]
        (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x) :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hae k)
    exact Measure.eqOn_open_of_ae_eq (hj.trans hk.symm) ((hU j).inter (hU k))
      (hs j).continuous.continuousOn (hs k).continuous.continuousOn
  have hindex (x : Space n) (hx : x ∈ B.carrier) : ∃ j, x ∈ U j := by
    rw [← hcover] at hx
    exact Set.mem_iUnion.mp hx
  let f : Space n → ℂ := fun x => if hx : x ∈ B.carrier then fs (hindex x hx).choose x else 0
  have heq (j : ℕ) : Set.EqOn f (fs j) (U j) := by
    intro x hx
    have hB : x ∈ B.carrier := hcover ▸ Set.mem_iUnion.mpr ⟨j, hx⟩
    dsimp only [f]
    rw [dif_pos hB]
    exact hcompat _ j ⟨(hindex x hB).choose_spec, hx⟩
  refine ⟨f, ?_, ?_⟩
  · rw [← hcover]
    exact ContDiffOn.iUnion_of_isOpen (fun j => (hs j).contDiffOn.congr (heq j)) hU
  · let v : Space n → ℂ := fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x
    change f =ᵐ[volume.restrict B.carrier] v
    rw [← hcover, ae_eq_restrict_iUnion_iff]
    intro j
    have he : f =ᵐ[volume.restrict (U j)] fs j := by
      filter_upwards [ae_restrict_mem (hU j).measurableSet] with x hx
      exact heq j hx
    exact he.trans (hae j)

end Regularization

theorem weak_sobolev_has_finite_order_representative {n : ℕ}
    (B : LocalBall n) (m : ℕ) (u : IntegerSobolev B (m + n)) :
    ∃ f : Space n → ℂ, ContDiffOn ℝ m f B.carrier ∧
      f =ᵐ[volume.restrict B.carrier]
        (fun x => u.derivatives
          (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x) := by
  exact Regularization.local_weak_sobolev_finite_order_representative B m u

end DedekindZetaZeroFree.KPLocalCubeSobolevJets

end
