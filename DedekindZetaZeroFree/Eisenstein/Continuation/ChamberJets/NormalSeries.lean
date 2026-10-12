module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.Defs
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.CasimirParameterJets

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff BigOperators
open Topology Filter

namespace DedekindZetaZeroFree.KPContActualChamberCasimirJets

theorem normalSeries_compact_holomorphic {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (O : Set ℂ) (hO : IsOpen O) (j : ℂ → C(X, ℂ))
    (hc : ContinuousOn (fun p : ℂ × X => j p.1 p.2) (O ×ˢ Set.univ))
    (hd : ∀ x : X, DifferentiableOn ℂ (fun z => j z x) O) :
    DifferentiableOn ℂ j O := by
  have hj : ContinuousOn j O := by
    apply continuousOn_iff_continuous_restrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    let a : O × X → ℂ × X := fun p => (p.1.val,p.2)
    have ha : Continuous a := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact hc.comp_continuous ha (fun p => ⟨p.1.property, Set.mem_univ _⟩)
  intro s hs
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hs)
  let R := r/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : Metric.closedBall s R ⊆ O :=
    (Metric.closedBall_subset_ball (by dsimp [R]; linarith)).trans hrO
  have hcircle : CircleIntegrable j s R :=
    (hj.mono (Metric.sphere_subset_closedBall.trans hclosed)).circleIntegrable hR.le
  let g : ℂ → C(X,ℂ) := fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    circleIntegral (fun z => (z-w)⁻¹ • j z) s R
  have heq : Set.EqOn g j (Metric.ball s R) := by
    intro w hw
    ext x
    let L : C(X,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
    have hw' : w ∉ Metric.sphere s |R| := by
      rw [abs_of_pos hR]
      intro hh
      exact (ne_of_lt (Metric.mem_ball.mp hw)) hh
    have hi := hcircle.sub_zpow_smul (-1) hw'
    have hL : L (circleIntegral (fun z => (z-w)⁻¹ • j z) s R) =
        circleIntegral (fun z => (z-w)⁻¹ • j z x) s R := by
      rw [circleIntegral, circleIntegral, ← L.intervalIntegral_comp_comm (by simpa using hi.out)]
      simp only [map_smul]
      rfl
    change L ((2 * Real.pi * Complex.I : ℂ)⁻¹ • _) = _
    rw [map_smul, hL]
    exact (((hd x).mono hclosed).mono Metric.closure_ball_subset_closedBall).diffContOnCl
      |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hg : DifferentiableAt ℂ g s := by
    change DifferentiableAt ℂ (fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      circleIntegral (fun z => (z-w)⁻¹ • j z) s R) s
    exact ((Complex.hasDerivAt_circleIntegral_sub_inv_smul (w := s) hcircle (by
      simpa [abs_of_pos hR] using (ne_of_gt hR).symm)).const_smul (2 * Real.pi * Complex.I : ℂ)⁻¹).differentiableAt
  have he : g =ᶠ[𝓝 s] j := Filter.eventually_of_mem (Metric.ball_mem_nhds s hR) (fun w hw => heq hw)
  exact (hg.congr_of_eventuallyEq he.symm).differentiableWithinAt

theorem normalSeries_compact_family_of_local {E : Type*} [TopologicalSpace E]
    (O : Set ℂ) (hO : IsOpen O) (U : Set E) (f : ℂ → E → ℂ)
    (hl : ∀ x ∈ U, ∃ (K : Set E) (hK : IsCompact K), x ∈ interior K ∧ K ⊆ U ∧
      (letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
       ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ y : K, j z y = f z y.val))
    (C : Set E) (hC : IsCompact C) (hCU : C ⊆ U) :
    letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    ∃ j : ℂ → C(C,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ x : C, j z x = f z x.val := by
  have hc : ContinuousOn (fun p : ℂ × E => f p.1 p.2) (O ×ˢ U) := by
    intro p hp
    obtain ⟨K,hK,hpK,hKU,j,hj,heq⟩ := hl p.2 hp.2
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hcont : ContinuousOn (fun q : ℂ × K => j q.1 q.2) (O ×ˢ Set.univ) :=
      continuous_eval.comp_continuousOn ((hj.continuousOn.comp continuous_fst.continuousOn
        (fun _ hq => hq.1)).prodMk continuous_snd.continuousOn)
    have hfK : ContinuousOn (fun q : ℂ × E => f q.1 q.2) (O ×ˢ K) := by
      apply continuousOn_iff_continuous_restrict.mpr
      let a : (O ×ˢ K) → ℂ × K := fun q => (q.val.1, ⟨q.val.2,q.property.2⟩)
      have ha : Continuous a := (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
      exact (hcont.comp_continuous ha (fun q => ⟨q.property.1, Set.mem_univ _⟩)).congr
        (fun q => heq q.val.1 q.property.1 ⟨q.val.2,q.property.2⟩)
    apply (hfK.continuousAt ?_).continuousWithinAt
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hO.mem_nhds hp.1) (mem_interior_iff_mem_nhds.mp hpK)
  have hd : ∀ x ∈ U, DifferentiableOn ℂ (fun z => f z x) O := by
    intro x hx
    obtain ⟨K,hK,hxK,hKU,j,hj,heq⟩ := hl x hx
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let L : C(K,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ ⟨x, interior_subset hxK⟩
    exact (L.differentiable.comp_differentiableOn hj).congr
      (fun z hz => (heq z hz ⟨x,interior_subset hxK⟩).symm)
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hcC : ContinuousOn (fun p : ℂ × C => f p.1 p.2.val) (O ×ˢ Set.univ) :=
    hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1,hCU p.2.property⟩)
  have hslice : ∀ z ∈ O, Continuous (fun x : C => f z x.val) := by
    intro z hz
    exact hcC.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hz,Set.mem_univ _⟩)
  let j : ℂ → C(C,ℂ) := fun z => if hz : z ∈ O then ⟨fun x => f z x.val, hslice z hz⟩ else 0
  have hjval : ∀ z ∈ O, ∀ x : C, j z x = f z x.val := by
    intro z hz x
    simp only [j, dif_pos hz]
    rfl
  refine ⟨j,normalSeries_compact_holomorphic O hO j ?_ ?_,hjval⟩
  · exact hcC.congr (fun p hp => hjval p.1 hp.1 p.2)
  · intro x
    exact (hd x.val (hCU x.property)).congr (fun z hz => hjval z hz x)

namespace ChartCalculus
open RightFrame.PullbackWords
variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype B]
private theorem cauchy_identify (O : Set ℂ) (hO : IsOpen O)
    (h : ℂ → E → ℂ) (s : ℂ) (hs : s ∈ O)
    (r : ℝ) (hr : 0 < r) (hdisk : Metric.closedBall s r ⊆ O)
    (x : E) (hx : DifferentiableOn ℂ (fun z => h z x) O) (k : ℕ) :
    iteratedDerivWithin k (fun z => h z x) O s =
      (k.factorial : ℂ) * RightFrame.CauchyCoefficient.cauchyCoefficient h s r k x := by
  rw [iteratedDerivWithin_of_isOpen hO hs]
  have hi := (hx.mono hdisk).circleIntegral_one_div_sub_center_pow_smul hr k
  have hkernel : (fun z => (z-s) ^ (-((k : ℤ)+1)) * h z x) =
      (fun z => (1 / (z-s) ^ (k+1)) • h z x) := by
    funext z
    rw [show -((k : ℤ)+1) = -((k+1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
    simp only [one_div, smul_eq_mul]
  unfold RightFrame.CauchyCoefficient.cauchyCoefficient
  rw [hkernel, hi, smul_eq_mul]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp

private theorem parameter_jet_smooth
    (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (O : Set ℂ) (hO : IsOpen O) (h : ℂ → E → ℂ)
    (hsp : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hj : ∀ w K, IsCompact K → K ⊆ U →
      ContinuousOn (fun p : ℂ × E => directionalWord fields w (h p.1) p.2) (O ×ˢ K))
    (hhol : ∀ w x, x ∈ U →
      DifferentiableOn ℂ (fun z => directionalWord fields w (h z) x) O)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => iteratedDerivWithin k (fun z => h z x) O s) U := by
  obtain ⟨ε,hε,hεO⟩ := Metric.isOpen_iff.mp hO s hs
  let r := ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hdisk : Metric.closedBall s r ⊆ O := fun z hz =>
    hεO (lt_of_le_of_lt hz (by change ε / 2 < ε; linarith))
  have hc := RightFrame.CauchyCoefficient.coefficient_smooth U hU fields hf hframe
    O hO h s r hr hdisk hsp
    (fun w K hK hKU => (hj w K hK hKU).mono (Set.prod_mono hdisk (Set.Subset.refl K)))
    (fun x hx => hhol [] x hx) k
  exact (contDiffOn_const.mul hc).congr
    (fun x hx => cauchy_identify O hO h s hs r hr hdisk x (hhol [] x hx) k)

private theorem word_smooth (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (w : List B) :
    ContDiffOn ℝ (⊤ : ℕ∞) (directionalWord fields w u) U := by
  induction w with
  | nil => exact hu
  | cons b w ih => exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply (hf b)
private theorem word_const_mul (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (c : ℂ) (w : List B) :
    ∀ x ∈ U, directionalWord fields w (fun y => c * u y) x =
      c * directionalWord fields w u x := by
  induction w with
  | nil => intro x hx; rfl
  | cons b w ih =>
    intro x hx
    change (fderiv ℝ (directionalWord fields w (fun y => c * u y)) x) (fields b x) = _
    have he : directionalWord fields w (fun y => c * u y) =ᶠ[𝓝 x]
        fun y => c * directionalWord fields w u y :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih y hy)
    rw [he.fderiv_eq]
    have hd := ((word_smooth U hU fields hf u hu w) x hx).contDiffAt (hU.mem_nhds hx)
    have he' : (fun y => c * directionalWord fields w u y) =
        fun y => c • directionalWord fields w u y := rfl
    rw [he', fderiv_fun_const_smul (hd.differentiableAt (by simp))]
    rfl
 theorem parameter_word_commute
    (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (O : Set ℂ) (hO : IsOpen O) (h : ℂ → E → ℂ)
    (hsp : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hj : ∀ w K, IsCompact K → K ⊆ U →
      ContinuousOn (fun p : ℂ × E => directionalWord fields w (h p.1) p.2) (O ×ˢ K))
    (hhol : ∀ w x, x ∈ U →
      DifferentiableOn ℂ (fun z => directionalWord fields w (h z) x) O)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) (w : List B) (x : E) (hx : x ∈ U) :
    directionalWord fields w (fun y => iteratedDerivWithin k (fun z => h z y) O s) x =
      iteratedDerivWithin k (fun z => directionalWord fields w (h z) x) O s := by
  obtain ⟨ε,hε,hεO⟩ := Metric.isOpen_iff.mp hO s hs
  let r := ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hdisk : Metric.closedBall s r ⊆ O := fun z hz =>
    hεO (lt_of_le_of_lt hz (by change ε / 2 < ε; linarith))
  have hj' := fun w K hK hKU => (hj w K hK hKU).mono (Set.prod_mono hdisk (Set.Subset.refl K))
  have hc := RightFrame.CauchyCoefficient.coefficient_smooth U hU fields hf hframe
    O hO h s r hr hdisk hsp hj' (fun x hx => hhol [] x hx) k
  have he : (fun y => iteratedDerivWithin k (fun z => h z y) O s) =ᶠ[𝓝 x]
      fun y => (k.factorial : ℂ) * RightFrame.CauchyCoefficient.cauchyCoefficient h s r k y :=
    Filter.eventually_of_mem (hU.mem_nhds hx)
      (fun y hy => cauchy_identify O hO h s hs r hr hdisk y (hhol [] y hy) k)
  have word_local {u v : E → ℂ} (heq : u =ᶠ[𝓝 x] v) :
      directionalWord fields w u x = directionalWord fields w v x := by
    have heq' : ∀ w, directionalWord fields w u =ᶠ[𝓝 x] directionalWord fields w v := by
      intro w
      induction w with
      | nil => exact heq
      | cons b w ih =>
        have hd := ih.fderiv (𝕜 := ℝ)
        filter_upwards [hd] with y hy
        change fderiv ℝ (directionalWord fields w u) y (fields b y) =
          fderiv ℝ (directionalWord fields w v) y (fields b y)
        rw [hy]
    exact (heq' w).self_of_nhds
  rw [word_local he, word_const_mul U hU fields hf _ hc _ w x hx,
    RightFrame.CauchyCoefficient.word_commute U hU fields hf hframe O hO h s r hr hdisk
      hsp hj' (fun y hy => hhol [] y hy) k w x hx]
  exact (cauchy_identify O hO (fun z => directionalWord fields w (h z)) s hs r hr hdisk
    x (hhol w x hx) k).symm

 theorem joint_of_compact_family
    (O : Set ℂ) (U : Set E) (h : ℂ → E → ℂ)
    (hh : ∀ (K : Set E) (hK : IsCompact K), K ⊆ U →
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧
        ∀ z ∈ O, ∀ x : K, j z x = h z x.val)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) :
    ContinuousOn (fun p : ℂ × E => h p.1 p.2) (O ×ˢ K) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j,hj,heq⟩ := hh K hK hKU
  have hc : ContinuousOn (fun p : ℂ × K => j p.1 p.2) (O ×ˢ Set.univ) :=
    continuous_eval.comp_continuousOn ((hj.continuousOn.comp continuous_fst.continuousOn
      (fun _ hp => hp.1)).prodMk continuous_snd.continuousOn)
  apply continuousOn_iff_continuous_restrict.mpr
  let a : (O ×ˢ K) → ℂ × K := fun p => (p.val.1, ⟨p.val.2,p.property.2⟩)
  have ha : Continuous a := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  exact (hc.comp_continuous ha (fun p => ⟨p.property.1, Set.mem_univ _⟩)).congr
    (fun p => heq p.val.1 p.property.1 ⟨p.val.2,p.property.2⟩)

 theorem point_of_compact_family
    (O : Set ℂ) (U : Set E) (h : ℂ → E → ℂ)
    (hh : ∀ (K : Set E) (hK : IsCompact K), K ⊆ U →
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧
        ∀ z ∈ O, ∀ x : K, j z x = h z x.val)
    (x : E) (hx : x ∈ U) : DifferentiableOn ℂ (fun z => h z x) O := by
  letI : CompactSpace ({x} : Set E) := isCompact_iff_compactSpace.mp isCompact_singleton
  obtain ⟨j,hj,heq⟩ := hh {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
  let L : C(({x} : Set E),ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ ⟨x,rfl⟩
  exact (L.differentiable.comp_differentiableOn hj).congr
    (fun z hz => (heq z hz ⟨x,rfl⟩).symm)

end ChartCalculus

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 theorem jet_constant_word (n : ℕ) (u : E → ℂ) (U : Set E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    iteratedFDerivWithin ℝ n u U x v =
      RightFrame.PullbackWords.constantDirectionWord (List.ofFn v) u x := by
  rw [iteratedFDerivWithin_of_isOpen n hU hx]
  induction n generalizing x with
  | zero => simp [RightFrame.PullbackWords.constantDirectionWord,
      RightFrame.PullbackWords.directionalWord, iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [((hu x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := n) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) |>.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℝ n u y (Fin.tail v)) =ᶠ[𝓝 x]
        RightFrame.PullbackWords.constantDirectionWord (List.ofFn (Fin.tail v)) u :=
      eventually_of_mem (hU.mem_nhds hx) fun y hy => ih y hy _
    rw [heq.fderiv_eq]
    simp only [List.ofFn_succ, RightFrame.PullbackWords.constantDirectionWord,
      RightFrame.PullbackWords.directionalWord]
    rfl

private theorem jet_germ_eq (n : ℕ) (f g : E → ℂ) (U W : Set E)
    (hU : IsOpen U) (hW : IsOpen W) (x : E) (hxU : x ∈ U) (hxW : x ∈ W)
    (heq : f =ᶠ[𝓝 x] g) :
    iteratedFDerivWithin ℝ n f U x = iteratedFDerivWithin ℝ n g W x := by
  rw [iteratedFDerivWithin_of_isOpen n hU hxU, iteratedFDerivWithin_of_isOpen n hW hxW]
  have he : f =ᶠ[𝓝[Set.univ] x] g := by simpa only [nhdsWithin_univ] using heq
  simpa only [iteratedFDerivWithin_univ] using he.iteratedFDerivWithin_eq heq.self_of_nhds n

theorem normalSeries_transported_compact_jet {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]
    {B : Type*} [Fintype B]
    (U : Set E) (hU : IsOpen U) (W : Set P) (hW : IsOpen W)
    (fields : B → E → E) (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (ψ : P → E) (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ W) (hψU : Set.MapsTo ψ W U)
    (O : Set ℂ) (h : ℂ → E → ℂ) (hs : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hw : ∀ (w : List B) (K : Set E) (hK : IsCompact K), K ⊆ U →
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧
        ∀ z ∈ O, ∀ x : K, j z x = RightFrame.PullbackWords.directionalWord fields w (h z) x.val)
    (K : Set P) (hK : IsCompact K) (hKW : K ⊆ W) (n : ℕ) (v : Fin n → P) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ x : K,
      j z x = iteratedFDerivWithin ℝ n (h z ∘ ψ) W x.val v := by
  let A := ψ '' K
  have hA : IsCompact A := hK.image_of_continuousOn (hψ.continuousOn.mono hKW)
  have hAU : A ⊆ U := by rintro _ ⟨x,hx,rfl⟩; exact hψU (hKW hx)
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let q : C(K,A) := ⟨fun x => ⟨ψ x.val, ⟨x.val,x.property,rfl⟩⟩,
    (continuousOn_iff_continuous_restrict.mp (hψ.continuousOn.mono hKW)).subtype_mk _⟩
  obtain ⟨N,c,w,hc,_,heq⟩ := RightFrame.PullbackWords.transport U W hU hW
    fields hfields hframe ψ hψ hψU (List.ofFn v)
  choose j hj hjval using fun i : Fin N => hw (w i) A hA hAU
  let a : Fin N → C(K,ℂ) := fun i => ⟨fun x => (c i x.val : ℂ),
    Complex.continuous_ofReal.comp (continuousOn_iff_continuous_restrict.mp ((hc i).continuousOn.mono hKW))⟩
  refine ⟨fun z => ∑ i : Fin N, a i * (j i z).comp q, ?_, ?_⟩
  · apply DifferentiableOn.fun_sum
    intro i _
    exact ((ContinuousMap.compCLM ℂ ℂ q).differentiable.comp_differentiableOn (hj i)).const_mul (a i)
  · intro z hz x
    rw [jet_constant_word n _ W hW ((hs z hz).comp hψ hψU) x.val (hKW x.property) v,
      heq _ (hs z hz) x.val (hKW x.property)]
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.comp_apply, a]
    apply Finset.sum_congr rfl
    intro i _
    rw [hjval i z hz]
    change (c i x.val : ℂ) * _ = c i x.val • _
    exact Complex.real_smul.symm

end

section Actual
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (f : ℂ → S)

private theorem compact_mixed_pullback (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    {X : Type*} [TopologicalSpace X] (O : Set X)
    (ℓ : X → KPContActualChamberNormalSeries.G F ζ hζ) (hℓ : ContinuousOn ℓ O)
    (K : Set X) (hK : IsCompact K) (hKO : K ⊆ O)
    (k : ℕ) (w : KPContActualChamberNormalSeries.Word F) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j V ∧ ∀ z ∈ V, ∀ x : K,
      j z x = KPContActualChamberNormalSeries.mixedJet F ζ hζ
        (KPContActualChamberNormalSeries.E F ζ hζ U ι f) k w z (ℓ x.val) := by
  let A := ℓ '' K
  have hA : IsCompact A := hK.image_of_continuousOn (hℓ.mono hKO)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let c : C(K,A) := ⟨fun x => ⟨ℓ x.val, ⟨x.val,x.property,rfl⟩⟩,
    (continuousOn_iff_continuous_restrict.mp (hℓ.mono hKO)).subtype_mk _⟩
  let g := KPContActualChamberNormalSeries.compactMixedJet F ζ hζ U ι f hι hf k w A
  refine ⟨fun z => (g z).comp c,
    (ContinuousMap.compCLM ℂ ℂ c).differentiable.comp_differentiableOn
      (KPContActualChamberNormalSeries.compactMixedJet_holomorphic F ζ hζ U ι f hι hf k w A hA), ?_⟩
  intro z hz x
  simp only [ContinuousMap.comp_apply, g, KPContActualChamberNormalSeries.compactMixedJet,
    dite_eq_ite, hz, ↓reduceDIte]
  rfl

private theorem iwasawa_compact_jet
    (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (O : Set (KPSmoothActualFlowData.B F → ℝ)) (hO : IsOpen O)
    (ℓ : (KPSmoothActualFlowData.B F → ℝ) → KPContActualChamberNormalSeries.G F ζ hζ)
    (hℓ : ContinuousOn ℓ O) (fields : KPSmoothActualFlowData.B F →
      (KPSmoothActualFlowData.B F → ℝ) → (KPSmoothActualFlowData.B F → ℝ))
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) O)
    (hframe : ∀ x ∈ O, ∃ e : Module.Basis (KPSmoothActualFlowData.B F) ℝ
      (KPSmoothActualFlowData.B F → ℝ), ∀ b, e b = fields b x)
    (hpull : ∀ u, KPMsGreenFlux.Smooth F ζ hζ u →
      ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ ℓ) O ∧ ∀ w x, x ∈ O →
        KPContActualChamberNormalSeries.rightWord F ζ hζ w u (ℓ x) =
          RightFrame.PullbackWords.directionalWord fields w (u ∘ ℓ) x)
    (W : Set X) (hW : IsOpen W) (ψ : X → (KPSmoothActualFlowData.B F → ℝ))
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ W) (hψO : Set.MapsTo ψ W O)
    (k : ℕ) (K : Set X) (hK : IsCompact K) (hKW : K ⊆ W) (n : ℕ) (v : Fin n → X) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j V ∧ ∀ z ∈ V, ∀ x : K,
      j z x = iteratedFDerivWithin ℝ n
        (fun y => jet F ζ hζ U ι f k z (ℓ (ψ y))) W x.val v := by
  let h := fun z x => KPContActualChamberNormalSeries.E F ζ hζ U ι f z (ℓ x)
  have hsp : ∀ z ∈ V, ContDiffOn ℝ (⊤ : ℕ∞) (h z) O := fun z hz =>
    (hpull _ (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf z hz)).1
  have hw : ∀ (w : List (KPSmoothActualFlowData.B F)) (K : Set (KPSmoothActualFlowData.B F → ℝ))
      (hK : IsCompact K), K ⊆ O →
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j V ∧ ∀ z ∈ V, ∀ x : K,
        j z x = RightFrame.PullbackWords.directionalWord fields w (h z) x.val := by
    intro w K hK hKO
    obtain ⟨j,hj,heq⟩ := compact_mixed_pullback F ζ hζ U ι f hι hf O ℓ hℓ K hK hKO 0 w
    refine ⟨j,hj,?_⟩
    intro z hz x
    rw [heq z hz]
    exact (hpull _ (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf z hz)).2 w x.val (hKO x.property)
  have hjoint := fun w K hK hKO => ChartCalculus.joint_of_compact_family V O
    (fun z x => RightFrame.PullbackWords.directionalWord fields w (h z) x) (hw w) K hK hKO
  have hpoint := fun w x hx => ChartCalculus.point_of_compact_family V O
    (fun z x => RightFrame.PullbackWords.directionalWord fields w (h z) x) (hw w) x hx
  let hk := fun z x => iteratedDerivWithin k (fun t => h t x) V z
  have hks : ∀ z ∈ V, ContDiffOn ℝ (⊤ : ℕ∞) (hk z) O := fun z hz =>
    ChartCalculus.parameter_jet_smooth O hO fields hfields hframe V
      KPChamberL2Defect.chamber_isOpen h hsp hjoint hpoint k z hz
  have hwk : ∀ (w : List (KPSmoothActualFlowData.B F)) (K : Set (KPSmoothActualFlowData.B F → ℝ))
      (hK : IsCompact K), K ⊆ O →
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j V ∧ ∀ z ∈ V, ∀ x : K,
        j z x = RightFrame.PullbackWords.directionalWord fields w (hk z) x.val := by
    intro w K hK hKO
    obtain ⟨j,hj,heq⟩ := compact_mixed_pullback F ζ hζ U ι f hι hf O ℓ hℓ K hK hKO k w
    refine ⟨j,hj,?_⟩
    intro z hz x
    rw [ChartCalculus.parameter_word_commute O hO fields hfields hframe V
      KPChamberL2Defect.chamber_isOpen h hsp hjoint hpoint k z hz w x.val (hKO x.property)]
    rw [heq z hz, ← KPContActualChamberNormalSeries.mixedJet_commute F ζ hζ U ι f hι hf k w z hz]
    exact iteratedDerivWithin_congr (fun t ht =>
      (hpull _ (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf t ht)).2 w x.val (hKO x.property)) hz
  exact normalSeries_transported_compact_jet O hO W hW fields hfields hframe ψ hψ hψO
    V hk hks hwk K hK hKW n v

private theorem component_value (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (z : KPContSectorCoveredQuotientVocabulary.SymmetricSpace F) :
    (lineJet F ζ hζ C R P H U ι f hι hf k s i).val z =
      jet F ζ hζ U ι f k s
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) *
          ((H.atlas (level F ζ hζ C R P H U)).representative i).val) := by
  rw [← coveredJet_projection F ζ hζ C R P H U ι f hι hf k s hs]
  rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap,
    KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
  exact KPContSectorScalarLineAlgebra.S_apply F ζ hζ (level F ζ hζ C R P H U) R P H _ i z

private theorem actual_compact_jet_local
    (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (a : KPContActualSectorSmoothTestModules.ActualChart
      (U := level F ζ hζ C R P H U) (H := H))
    (x : M F) (hx : x ∈ KPContCotangentOverlapRationalBranches.omega a)
    (n : ℕ) (v : Fin n → M F) :
    ∃ (K : Set (M F)) (hK : IsCompact K), x ∈ interior K ∧
      K ⊆ KPContCotangentOverlapRationalBranches.omega a ∧
      (letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
       ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j V ∧ ∀ z ∈ V, ∀ y : K,
         j z y = iteratedFDerivWithin ℝ n
           ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
             (lineJet F ζ hζ C R P H U ι f hι hf k z))
           (KPContCotangentOverlapRationalBranches.omega a) y.val v) := by
  let q := KPContCotangentActualGenuineTwistIsotropy.isotropyChart a
  let A := KPContCotangentActualOverlap.labeledA q.places
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by
    apply contDiff_pi.mpr
    intro i
    exact (contDiff_apply ℝ (ℂ × ℝ) (q.places.symm i)).comp (CotangentLogCoframe.A (d F)).contDiff
  obtain ⟨O,W,ℓ,ψ,fields,hO,hW,hxW,hℓ,hψ,hψO,hfields,hframe,hrec,hpull⟩ :=
    KPContinuation.ChamberJetGeometry.local_iwasawa_frame F ζ hζ
      ((H.atlas (level F ζ hζ C R P H U)).representative a.component) (A x)
  let D := A ⁻¹' W
  have hD : IsOpen D := hW.preimage hA.continuous
  have hxD : x ∈ D := hxW
  have hω : IsOpen (KPContCotangentOverlapRationalBranches.omega a) := by
    unfold KPContCotangentOverlapRationalBranches.omega
    exact a.domain_open.preimage (by
      apply continuous_pi
      intro i
      exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous)
  obtain ⟨K,hK,hxK,hKD⟩ := exists_compact_subset (hD.inter hω) ⟨hxD,hx⟩
  have hKW : K ⊆ D := fun y hy => (hKD hy).1
  have hKω : K ⊆ KPContCotangentOverlapRationalBranches.omega a := fun y hy => (hKD hy).2
  refine ⟨K,hK,hxK,hKω,?_⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hψA : ContDiffOn ℝ (⊤ : ℕ∞) (ψ ∘ A) D := hψ.comp hA.contDiffOn (fun y hy => hy)
  have hψAO : Set.MapsTo (ψ ∘ A) D O := fun y hy => hψO hy
  obtain ⟨j,hj,hjval⟩ := iwasawa_compact_jet F ζ hζ U ι f hι hf
    O hO ℓ hℓ fields hfields hframe hpull D hD (ψ ∘ A) hψA hψAO k K hK hKW n v
  refine ⟨j,hj,?_⟩
  intro z hz y
  rw [hjval z hz y]
  have heq : (fun t => jet F ζ hζ U ι f k z (ℓ ((ψ ∘ A) t))) =ᶠ[𝓝 y.val]
      q.coefficient (lineJet F ζ hζ C R P H U ι f hι hf k z) := by
    filter_upwards [hD.mem_nhds (hKW y.property)] with t ht
    dsimp only [Function.comp_apply]
    rw [hrec (A t) ht]
    dsimp only [q, KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
      KPContCotangentActualOverlap.LiftedChart.coefficient,
      KPContCotangentActualOverlap.ChartKind.representative]
    simp only [map_one, Units.val_one, one_mul, one_smul]
    exact (component_value F ζ hζ C R P H U ι f hι hf k z hz a.component (A t)).symm
  exact congrArg (fun t => t v) (jet_germ_eq n _ _ D _ hD hω y.val (hKW y.property) (hKω y.property) heq)

end Actual

theorem actual_normal_series_chart_holomorphic
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S) (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (a : KPContActualSectorSmoothTestModules.ActualChart
      (U := level F ζ hζ C R P H U) (H := H)) :
    KPContActualCompactSectionL2Jets.ChartHolomorphicOn a
      (lineJet F ζ hζ C R P H U ι f hι hf k) V := by
  intro K hK hKω n v
  apply normalSeries_compact_family_of_local V KPChamberL2Defect.chamber_isOpen
    (KPContCotangentOverlapRationalBranches.omega a)
    (fun z x => iteratedFDerivWithin ℝ n
      ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
        (lineJet F ζ hζ C R P H U ι f hι hf k z))
      (KPContCotangentOverlapRationalBranches.omega a) x v)
    (fun x hx => actual_compact_jet_local F ζ hζ C R P H U ι f hι hf k a x hx n v) K hK hKω

end DedekindZetaZeroFree.KPContActualChamberCasimirJets

end
