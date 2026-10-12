module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.LaplacianSmoothnessAndSupport
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.UniformL2Tails
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.CutoffGraphConvergence

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff BigOperators
open Topology Filter
set_option maxHeartbeats 2400000

namespace DedekindZetaZeroFree.KPContActualChamberGraphHolomorphy

section CoordinateConversion
open KPContLocalNorm
private theorem list_index {n : ℕ} (l : List (Fin n)) :
    ∃ m, ∃ α : MultiIndex n m, l.Perm α.directions := by
  classical
  let m := ∑ i : Fin n, l.count i
  let α : MultiIndex n m := ⟨fun i => ⟨l.count i, by
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (l.count j)) (Finset.mem_univ i)
    dsimp [m]; omega⟩, by simp [m]⟩
  refine ⟨m, α, List.perm_iff_count.mpr ?_⟩
  intro i
  rw [MultiIndex.directions, List.count_flatMap,
    ← List.sum_toFinset _ (List.nodup_finRange n)]
  simp [α, Function.comp_def, List.count_replicate]

private theorem flat_word (n : ℕ) (w : List (Fin n)) (u : Space n → ℂ) :
    RightFrame.PullbackWords.directionalWord (fun i _ => EuclideanSpace.single i (1:ℝ)) w u =
      coordinateDerivativeList w u := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [RightFrame.PullbackWords.directionalWord, coordinateDerivativeList, ih]

private theorem compact_coordinate_jets_transport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : ℕ} (B : LocalBall d) (O : Set ℂ)
    (g : ℂ → Space d → ℂ) (hg : KPCutoffSource.ChartSmoothHolomorphicOn B g O)
    (D : Set E) (hD : IsOpen D) (ψ : E → Space d)
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ D) (hψB : Set.MapsTo ψ D B.carrier)
    (K : Set E) (hK : IsCompact K) (hKD : K ⊆ D) (n : ℕ) (v : Fin n → E) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ x : K,
      j z x = iteratedFDerivWithin ℝ n (g z ∘ ψ) D x.val v := by
  apply KPContActualChamberCasimirJets.normalSeries_transported_compact_jet
    B.carrier Metric.isOpen_ball D hD
    (fun i _ => EuclideanSpace.single i (1:ℝ)) (fun _ => contDiffOn_const)
    (fun x _ => ⟨(EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
      fun i => EuclideanSpace.basisFun_apply (Fin d) ℝ i⟩)
    ψ hψ hψB O g hg.1 ?_ K hK hKD n v
  intro w C hC hCB
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  obtain ⟨m,α,hperm⟩ := list_index w
  obtain ⟨j,hj,hjval⟩ := hg.2 C hC hCB m
  let L : CompactJets C m →L[ℂ] C(C,ℂ) := ContinuousLinearMap.proj α
  refine ⟨fun z => L (j z), L.differentiable.comp_differentiableOn hj, ?_⟩
  intro z hz x
  rw [flat_word, WeakJets.Raw.coordinateDerivativeList_perm_on hperm (hg.1 z hz) (hCB x.property)]
  exact hjval z hz α x
end CoordinateConversion

namespace RawCalculus
open RightFrame.PullbackWords
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem jet_constant_word (n : ℕ) (u : E → ℂ) (U : Set E) (hU : IsOpen U)
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

private theorem word_smooth (u : E → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (w : List E) :
    ContDiff ℝ (⊤ : ℕ∞) (constantDirectionWord w u) := by
  induction w with
  | nil => exact hu
  | cons b w ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

 def expand (c : E → ℂ) : List E → List ((E → ℂ) × List E)
  | [] => [(c, [])]
  | b :: w => (expand c w).flatMap (fun t =>
      [(fun x => fderiv ℝ t.1 x b, t.2), (t.1, b :: t.2)])

private theorem expand_smooth (c : E → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (w : List E) :
    ∀ t ∈ expand c w, ContDiff ℝ (⊤ : ℕ∞) t.1 := by
  induction w with
  | nil => intro t ht; simp only [expand, List.mem_singleton] at ht; subst t; exact hc
  | cons b w ih =>
    intro t ht
    obtain ⟨q,hq,ht⟩ := List.mem_flatMap.mp ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ((ih q hq).fderiv_right (by simp)).clm_apply contDiff_const
    · exact ih q hq

private theorem list_derivative {α : Type*} (ts : List α) (f : α → E → ℂ) (x : E)
    (hf : ∀ t ∈ ts, DifferentiableAt ℝ (f t) x) :
    HasFDerivAt (fun y => (ts.map (fun t => f t y)).sum)
      (ts.map (fun t => fderiv ℝ (f t) x)).sum x := by
  induction ts with
  | nil => simpa using hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x
  | cons t ts ih =>
    exact (hf t (by simp)).hasFDerivAt.fun_add (ih (fun r hr => hf r (by simp [hr])))

private theorem expand_value (c : E → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (u : E → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (w : List E) :
    constantDirectionWord w (fun x => c x * u x) =
      fun x => ((expand c w).map (fun t => t.1 x * constantDirectionWord t.2 u x)).sum := by
  induction w with
  | nil => simp [expand, constantDirectionWord, directionalWord]
  | cons b w ih =>
    funext x
    change fderiv ℝ (constantDirectionWord w (fun x => c x * u x)) x b = _
    rw [ih]
    have hd : ∀ t ∈ expand c w, DifferentiableAt ℝ
        (fun y => t.1 y * constantDirectionWord t.2 u y) x := by
      intro t ht
      exact ((expand_smooth c hc w t ht).mul (word_smooth u hu t.2)).differentiable (by simp) x
    rw [(list_derivative (expand c w) (fun t y => t.1 y * constantDirectionWord t.2 u y) x hd).fderiv]
    rw [show (expand c (b :: w)).map (fun t => t.1 x * constantDirectionWord t.2 u x) =
        ((expand c w).map (fun t =>
          [(fderiv ℝ t.1 x b) * constantDirectionWord t.2 u x,
           t.1 x * constantDirectionWord (b :: t.2) u x])).flatten by
      simp [expand, List.flatMap, List.map_flatten, List.map_map, Function.comp_def]]
    rw [List.sum_flatten, List.map_map]
    rw [show (((expand c w).map (fun t => fderiv ℝ
        (fun y => t.1 y * constantDirectionWord t.2 u y) x)).sum) b =
        ((expand c w).map (fun t => fderiv ℝ
          (fun y => t.1 y * constantDirectionWord t.2 u y) x b)).sum by
      simpa only [List.map_map, Function.comp_def, ContinuousLinearMap.apply_apply] using
        map_list_sum (ContinuousLinearMap.apply ℝ ℂ b)
          ((expand c w).map (fun t => fderiv ℝ
            (fun y => t.1 y * constantDirectionWord t.2 u y) x))]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    rw [fderiv_fun_mul
      ((expand_smooth c hc w t ht).differentiable (by simp) x)
      ((word_smooth u hu t.2).differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp only [Function.comp_apply, List.sum_cons, List.sum_nil, add_zero, constantDirectionWord, directionalWord]
    ring
 def WordHolomorphic (W : Set E) (O : Set ℂ) (h : ℂ → E → ℂ) : Prop :=
  ∀ (w : List E) (K : Set E) (hK : IsCompact K), K ⊆ W →
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧
      ∀ s ∈ O, ∀ x : K, j s x = constantDirectionWord w (h s) x.val

private theorem word_holomorphic_of_jets (W : Set E) (hW : IsOpen W) (O : Set ℂ)
    (h : ℂ → E → ℂ) (hs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h s))
    (hh : ∀ (K : Set E) (hK : IsCompact K), K ⊆ W → ∀ n (v : Fin n → E),
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ s ∈ O, ∀ x : K,
        j s x = iteratedFDerivWithin ℝ n (h s) W x.val v) : WordHolomorphic W O h := by
  intro w K hK hKW
  obtain ⟨j,hj,hjval⟩ := hh K hK hKW w.length w.get
  refine ⟨j,hj,?_⟩
  intro s hz x
  rw [hjval s hz x, jet_constant_word _ _ W hW (hs s hz).contDiffOn _ (hKW x.property)]
  simp only [List.ofFn_get]

private theorem jets_of_word_holomorphic (W : Set E) (hW : IsOpen W) (O : Set ℂ)
    (h : ℂ → E → ℂ) (hs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h s))
    (hh : WordHolomorphic W O h)
    (K : Set E) (hK : IsCompact K) (hKW : K ⊆ W) (n : ℕ) (v : Fin n → E) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ s ∈ O, ∀ x : K,
      j s x = iteratedFDerivWithin ℝ n (h s) W x.val v := by
  obtain ⟨j,hj,hjval⟩ := hh (List.ofFn v) K hK hKW
  refine ⟨j,hj,?_⟩
  intro s hz x
  rw [jet_constant_word _ _ W hW (hs s hz).contDiffOn _ (hKW x.property), hjval s hz x]

private theorem list_holomorphic {α : Type*} {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (ts : List α) (j : α → ℂ → C(X,ℂ)) (O : Set ℂ)
    (hj : ∀ t ∈ ts, DifferentiableOn ℂ (j t) O) :
    DifferentiableOn ℂ (fun s => (ts.map (fun t => j t s)).sum) O := by
  induction ts with
  | nil => exact differentiableOn_const _
  | cons t ts ih => exact (hj t (by simp)).add (ih (fun r hr => hj r (by simp [hr])))

private theorem word_holomorphic_mul (W : Set E) (O : Set ℂ)
    (h : ℂ → E → ℂ) (hs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h s))
    (hh : WordHolomorphic W O h) (c : E → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    WordHolomorphic W O (fun s x => c x * h s x) := by
  intro w K hK hKW
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ts := expand c w
  choose j hj hjval using fun t : (E → ℂ) × List E => hh t.2 K hK hKW
  let a : {t // t ∈ ts} → C(K,ℂ) := fun t => ⟨fun x => t.val.1 x.val,
    (expand_smooth c hc w t.val t.property).continuous.comp continuous_subtype_val⟩
  let J : ((E → ℂ) × List E) → ℂ → C(K,ℂ) := fun t s =>
    if ht : t ∈ ts then a ⟨t,ht⟩ * j t s else 0
  have hJ : ∀ t ∈ ts, DifferentiableOn ℂ (J t) O := by
    intro t ht
    simp only [J, dif_pos ht]
    exact (hj t).const_mul _
  refine ⟨fun s => (ts.map (fun t => J t s)).sum, list_holomorphic ts J O hJ, ?_⟩
  intro s hz x
  have heval : ∀ l : List ((E → ℂ) × List E),
      ((l.map (fun t => J t s)).sum) x = (l.map (fun t => J t s x)).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons t l ih => simp only [List.map_cons, List.sum_cons, ContinuousMap.add_apply, ih]
  rw [heval]
  have he := congrFun (expand_value c hc (h s) (hs s hz) w) x.val
  rw [he]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp only [J, dif_pos ht, ContinuousMap.mul_apply, a, hjval t s hz x]
  rfl

private theorem word_append (u : E → ℂ) (v w : List E) :
    constantDirectionWord (v ++ w) u = constantDirectionWord v (constantDirectionWord w u) := by
  induction v with
  | nil => rfl
  | cons b v ih => simp only [List.cons_append, constantDirectionWord, directionalWord] at *; rw [ih]

private theorem word_holomorphic_derivative (W : Set E) (O : Set ℂ)
    (h : ℂ → E → ℂ) (hh : WordHolomorphic W O h) (w : List E) :
    WordHolomorphic W O (fun s => constantDirectionWord w (h s)) := by
  intro v K hK hKW
  obtain ⟨j,hj,hjval⟩ := hh (v ++ w) K hK hKW
  refine ⟨j,hj,?_⟩
  intro s hs x
  rw [hjval s hs x, word_append]

private theorem word_sum {α : Type*} (ts : List α) (f : α → E → ℂ)
    (hf : ∀ t ∈ ts, ContDiff ℝ (⊤ : ℕ∞) (f t)) (w : List E) :
    constantDirectionWord w (fun x => (ts.map (fun t => f t x)).sum) =
      fun x => (ts.map (fun t => constantDirectionWord w (f t) x)).sum := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    funext x
    change fderiv ℝ (constantDirectionWord w (fun x => (ts.map (fun t => f t x)).sum)) x b = _
    rw [ih, (list_derivative ts (fun t => constantDirectionWord w (f t)) x
      (fun t ht => (word_smooth _ (hf t ht) w).differentiable (by simp) x)).fderiv]
    simpa only [List.map_map, Function.comp_def, ContinuousLinearMap.apply_apply,
      constantDirectionWord, directionalWord] using
      map_list_sum (ContinuousLinearMap.apply ℝ ℂ b)
        (ts.map (fun t => fderiv ℝ (constantDirectionWord w (f t)) x))

private theorem word_holomorphic_sum {α : Type*} (ts : List α) (W : Set E) (O : Set ℂ)
    (h : α → ℂ → E → ℂ) (hs : ∀ t ∈ ts, ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h t s))
    (hh : ∀ t, WordHolomorphic W O (h t)) :
    WordHolomorphic W O (fun s x => (ts.map (fun t => h t s x)).sum) := by
  intro w K hK hKW
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose j hj hjval using fun t => hh t w K hK hKW
  refine ⟨fun s => (ts.map (fun t => j t s)).sum,
    list_holomorphic ts j O (fun t _ => hj t), ?_⟩
  intro s hz x
  rw [congrFun (word_sum ts (fun t => h t s) (fun t ht => hs t ht s hz) w) x.val]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, ContinuousMap.add_apply, hjval t s hz x]
    exact congrArg (_ + ·) (ih (fun t ht => hs t (by simp [ht])) )

private theorem word_holomorphic_add (W : Set E) (O : Set ℂ) (h g : ℂ → E → ℂ)
    (hs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h s))
    (gs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (g s))
    (hh : WordHolomorphic W O h) (gh : WordHolomorphic W O g) :
    WordHolomorphic W O (fun s x => h s x + g s x) := by
  let H : Bool → ℂ → E → ℂ := fun b => if b then h else g
  have HH := word_holomorphic_sum [true,false] W O H
    (fun b _ s hz => by cases b <;> [exact gs s hz; exact hs s hz])
    (fun b => by cases b <;> [exact gh; exact hh])
  simpa [H] using HH

private theorem word_holomorphic_neg (W : Set E) (O : Set ℂ) (h : ℂ → E → ℂ)
    (hs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h s)) (hh : WordHolomorphic W O h) :
    WordHolomorphic W O (fun s x => -h s x) := by
  simpa only [neg_one_mul] using word_holomorphic_mul W O h hs hh
    (fun _ => (-1 : ℂ)) contDiff_const

end RawCalculus

namespace RawCauchy
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
private theorem parameter_word_commute
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

private theorem joint_of_compact_family
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

private theorem point_of_compact_family
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

end RawCauchy

section RawTestGeometry
open KPContActualSectorSmoothTestModules KPContSectorSmoothFramesSupport
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem raw_test_representative (f : S_U F ζ hζ U R P H) :
    sectionFields (scalarSections f) = f.val := by
  exact (Classical.choose_spec (scalar_gluing f)).1.2.2

private theorem raw_test_smooth (f : S_U F ζ hζ U R P H) :
    IsSmoothSections F ζ hζ U R P H (scalarSections f) := by
  exact (Classical.choose_spec (scalar_gluing f)).1.1

private theorem raw_test_laplacian_coefficient (f : S_U F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    (isotropyChart a).coefficient
      (scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U f))) x.val =
      HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
        (KPContActualSectorTestDifferentialDescent.liftExtension a (f.val a)) x.val := by
  have h := congrFun (congrFun (raw_test_representative
    (KPContActualSectorTestDifferentialDescent.δ_U
      (KPContActualSectorTestDifferentialDescent.D_U f))) a) x
  change (isotropyChart a).coefficient _ x.val = _ at h
  rw [h]
  exact KPContActualSectorTestDifferentialDescentCalculus.coframe_calculus.2.2.2.2.1
    a (f.val a) (f.property.1 a) x

private theorem raw_coefficient_formula (a : ActualChart (U := U) (H := H))
    (s : Sections F ζ hζ U R P H) (x : KPContCotangentActualOverlap.M F) :
    (isotropyChart a).coefficient s x = (s a.component).val
      (KPContCotangentActualOverlap.labeledA
        (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x) := by
  simp [isotropyChart, KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContCotangentActualOverlap.ChartKind.representative,
    KPContSectorCoveredQuotientVocabulary.chi_coe]

private theorem raw_cutoffSection_support
    (r : KPContActualSectorCutoffGraphLimit.Cutoffs (U := U) (H := H)) (n : ℕ)
    (s : Sections F ζ hζ U R P H) :
    tsupport (sectionNorm F ζ hζ U R P H
      (KPCuspCutoffGraph.cutoffSection F ζ hζ H.totallyComplex U (H.atlas U) (r.rho n) s)) ⊆
      tsupport (r.rho n) := by
  apply closure_minimal _ isClosed_closure
  intro b hb
  obtain ⟨⟨i,z⟩, rfl⟩ := (H.atlas U).components.surjective b
  obtain ⟨x,rfl⟩ := Quotient.exists_rep z
  rw [Function.mem_support, sectionNorm_component] at hb
  by_contra hx
  have hbase : KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex U (H.atlas U) i x =
      (H.atlas U).components ⟨i, Quotient.mk _ x⟩ := by
    rw [(H.atlas U).components_formula]
    rfl
  have hz := image_eq_zero_of_notMem_tsupport (f := r.rho n) (hbase ▸ hx)
  apply hb
  change ‖(r.rho n (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex U
    (H.atlas U) i x) : ℂ) * (s i).val x‖ = 0
  rw [hz]
  simp

private theorem raw_cutoff_test_sections
    (r : KPContActualSectorCutoffGraphLimit.Cutoffs (U := U) (H := H)) (n : ℕ)
    (w : KPContActualSectorCutoffGraphLimit.SmoothSection (U := U) (H := H)) :
    scalarSections (KPContActualSectorCutoffGraphLimit.cutoffTest r n w) =
      KPCuspCutoffGraph.cutoffSection F ζ hζ H.totallyComplex U (H.atlas U) (r.rho n) w.val := by
  apply ((Classical.choose_spec
    (scalar_gluing (KPContActualSectorCutoffGraphLimit.cutoffTest r n w))).2 _ ?_).symm
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (Complex.ofRealCLM.contDiff.comp (r.smooth n i)).mul (w.property i)
  · exact (r.compact_support n).of_isClosed_subset isClosed_closure
      (raw_cutoffSection_support r n w.val)
  · funext a x
    change _ = KPContActualSectorTestDifferentialDescent.cutoffLift
      (KPContActualSectorCutoffGraphLimit.realCutoff r n) a x * sectionFields w.val a x
    simp only [sectionFields, raw_coefficient_formula]
    rfl

private theorem raw_cutoff_test_common_support
    (r : KPContActualSectorCutoffGraphLimit.Cutoffs (U := U) (H := H)) (n : ℕ)
    (w : KPContActualSectorCutoffGraphLimit.SmoothSection (U := U) (H := H)) (b : Bool) :
    let φ := KPContActualSectorCutoffGraphLimit.cutoffTest r n w
    let σ := scalarSections
      (if b then KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U φ) else φ)
    IsSmoothSections F ζ hζ U R P H σ ∧
      tsupport (sectionNorm F ζ hζ U R P H σ) ⊆ tsupport (r.rho n) := by
  let φ := KPContActualSectorCutoffGraphLimit.cutoffTest r n w
  have hsm := raw_test_smooth φ
  have hsup : tsupport (sectionNorm F ζ hζ U R P H (scalarSections φ)) ⊆
      tsupport (r.rho n) := by
    rw [raw_cutoff_test_sections r n w]
    exact raw_cutoffSection_support r n w.val
  cases b
  · exact ⟨hsm, hsup⟩
  · apply KPContActualCompactSectionL2Jets.local_laplacian_smooth_support_source
      Set.univ (tsupport (r.rho n)) (fun _ => scalarSections φ)
      (fun _ => scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U φ)))
      (fun _ _ => hsm) (fun _ _ => hsup) ?_ 0 (Set.mem_univ 0)
    intro s hs a x
    rw [raw_test_laplacian_coefficient]
    rw [raw_test_representative]

private theorem raw_omega_open (a : ActualChart (U := U) (H := H)) :
    IsOpen (omega a) :=
  a.domain_open.preimage KPContActualGlobalGreen.contDiff_labeledA.continuous

private theorem raw_coefficient_smooth (a : ActualChart (U := U) (H := H))
    (s : Sections F ζ hζ U R P H) (hs : IsSmoothSections F ζ hζ U R P H s) :
    ContDiff ℝ (⊤ : ℕ∞) ((isotropyChart a).coefficient s) := by
  have he : (isotropyChart a).coefficient s = fun x => (s a.component).val
      (KPContCotangentActualOverlap.labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x) :=
    funext (raw_coefficient_formula a s)
  rw [he]
  exact (hs a.component).comp KPContActualGlobalGreen.contDiff_labeledA

private theorem raw_chart_sub (a : ActualChart (U := U) (H := H))
    (O : Set ℂ) (f g : ℂ → Sections F ζ hζ U R P H)
    (hf : ∀ s ∈ O, IsSmoothSections F ζ hζ U R P H (f s))
    (hg : ∀ s ∈ O, IsSmoothSections F ζ hζ U R P H (g s))
    (hfhol : KPContActualCompactSectionL2Jets.ChartHolomorphicOn a f O)
    (hghol : KPContActualCompactSectionL2Jets.ChartHolomorphicOn a g O) :
    KPContActualCompactSectionL2Jets.ChartHolomorphicOn a (fun s => f s - g s) O := by
  intro K hK hKω n v
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j,hj,hjval⟩ := hfhol K hK hKω n v
  obtain ⟨l,hl,hlval⟩ := hghol K hK hKω n v
  refine ⟨fun s => j s - l s, hj.sub hl, ?_⟩
  intro s hs x
  simp only [Pi.sub_apply, ContinuousMap.sub_apply, hjval s hs x, hlval s hs x]
  have he : (isotropyChart a).coefficient (f s - g s) =
      (isotropyChart a).coefficient (f s) - (isotropyChart a).coefficient (g s) := by
    funext y
    simp only [Pi.sub_apply, raw_coefficient_formula]
    rfl
  rw [he, iteratedFDerivWithin_sub_apply
    ((raw_coefficient_smooth a (f s) (hf s hs)).of_le (by simp)).contDiffWithinAt
    ((raw_coefficient_smooth a (g s) (hg s hs)).of_le (by simp)).contDiffWithinAt
    (raw_omega_open a).uniqueDiffOn (hKω x.property)]
  rfl

private theorem raw_cutoff_chart_holomorphic
    (r : KPContActualSectorCutoffGraphLimit.Cutoffs (U := U) (H := H)) (n : ℕ)
    (w : ℂ → KPContActualSectorCutoffGraphLimit.SmoothSection (U := U) (H := H))
    (O : Set ℂ) (a : ActualChart (U := U) (H := H))
    (hh : KPContActualCompactSectionL2Jets.ChartHolomorphicOn a (fun s => (w s).val) O) :
    KPContActualCompactSectionL2Jets.ChartHolomorphicOn a
      (fun s => scalarSections (KPContActualSectorCutoffGraphLimit.cutoffTest r n (w s))) O := by
  let h := fun s => (isotropyChart a).coefficient (w s).val
  let c := fun x : KPContCotangentActualOverlap.M F =>
    (r.rho n (q a x) : ℂ)
  have hs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h s) :=
    fun s _ => raw_coefficient_smooth a (w s).val (w s).property
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := by
    exact (Complex.ofRealCLM.contDiff.comp (r.smooth n a.component)).comp
      KPContActualGlobalGreen.contDiff_labeledA
  have hw := RawCalculus.word_holomorphic_of_jets (omega a) (raw_omega_open a) O h hs hh
  have hm := RawCalculus.word_holomorphic_mul (omega a) O h hs hw c hc
  have he : ∀ s, (isotropyChart a).coefficient
      (scalarSections (KPContActualSectorCutoffGraphLimit.cutoffTest r n (w s))) =
        fun x => c x * h s x := by
    intro s
    rw [raw_cutoff_test_sections]
    funext x
    dsimp only [h]
    simp only [raw_coefficient_formula]
    rfl
  intro K hK hKω m v
  obtain ⟨j,hj,hjval⟩ := RawCalculus.jets_of_word_holomorphic (omega a) (raw_omega_open a)
    O (fun s x => c x * h s x) (fun s hz => hc.mul (hs s hz)) hm K hK hKω m v
  refine ⟨j,hj,?_⟩
  intro s hz x
  rw [he, hjval s hz x]

open KPContCotangentActualOverlap
private theorem contDiff_exp_height (i : Fin (d F)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : M F => (Real.exp (2 * p (i, 2)) : ℂ)) := by
  have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F => p (i, 2)) := by
    convert (EuclideanSpace.proj (i, 2) : M F →L[ℝ] ℝ).contDiff (n := (⊤ : ℕ∞)) using 1
    ext p
    simp [PiLp.proj_apply]
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F => 2 * p (i, 2)) :=
    (contDiff_const (c := (2 : ℝ))).mul hproj
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F => ((2 * p (i, 2) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h2
  simpa only [Complex.ofReal_exp] using h.cexp

private theorem contDiff_coordinateDerivative (f : M F → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin (d F)) (k : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => HyperbolicChart.coordinateDerivative (d F) i k f p) := by
  have h := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp))
  simpa only [HyperbolicChart.coordinateDerivative] using h.clm_apply contDiff_const

private theorem contDiff_laplacian (f : M F → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => HyperbolicChart.laplacian (d F) f x) := by
  have key : ∀ i : Fin (d F), ContDiff ℝ (⊤ : ℕ∞) (fun p : M F =>
      -HyperbolicChart.coordinateDerivative (d F) i 2
          (HyperbolicChart.coordinateDerivative (d F) i 2 f) p +
        2 * HyperbolicChart.coordinateDerivative (d F) i 2 f p -
      (Real.exp (2 * p (i, 2)) : ℂ) *
        (HyperbolicChart.coordinateDerivative (d F) i 0
            (HyperbolicChart.coordinateDerivative (d F) i 0 f) p +
          HyperbolicChart.coordinateDerivative (d F) i 1
            (HyperbolicChart.coordinateDerivative (d F) i 1 f) p)) := by
    intro i
    have h22 := contDiff_coordinateDerivative f hf i 2
    have h00 := contDiff_coordinateDerivative f hf i 0
    have h11 := contDiff_coordinateDerivative f hf i 1
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F =>
        HyperbolicChart.coordinateDerivative (d F) i 2
          (HyperbolicChart.coordinateDerivative (d F) i 2 f) p) :=
      contDiff_coordinateDerivative _ h22 i 2
    have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F =>
        HyperbolicChart.coordinateDerivative (d F) i 0
          (HyperbolicChart.coordinateDerivative (d F) i 0 f) p) :=
      contDiff_coordinateDerivative _ h00 i 0
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F =>
        HyperbolicChart.coordinateDerivative (d F) i 1
          (HyperbolicChart.coordinateDerivative (d F) i 1 f) p) :=
      contDiff_coordinateDerivative _ h11 i 1
    have he : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F => (Real.exp (2 * p (i, 2)) : ℂ)) :=
      contDiff_exp_height i
    have h22' : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F =>
        2 * HyperbolicChart.coordinateDerivative (d F) i 2 f p) :=
      (contDiff_const (c := (2 : ℂ))).mul h22
    exact (h2.neg.add h22').sub (he.mul (h0.add h1))
  simpa only [HyperbolicChart.laplacian] using ContDiff.sum (fun i _ => key i)

private theorem raw_laplacian_word_holomorphic (W : Set (M F)) (O : Set ℂ)
    (h : ℂ → M F → ℂ) (hs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h s))
    (hh : RawCalculus.WordHolomorphic W O h) :
    RawCalculus.WordHolomorphic W O (fun s x => HyperbolicChart.laplacian (d F) (h s) x) := by
  have hd (i : Fin (d F)) (k : Fin 3) : RawCalculus.WordHolomorphic W O
      (fun s x => HyperbolicChart.coordinateDerivative (d F) i k (h s) x) :=
    RawCalculus.word_holomorphic_derivative W O h hh [HyperbolicChart.coordinateVector (d F) i k]
  have hdd (i : Fin (d F)) (k : Fin 3) : RawCalculus.WordHolomorphic W O
      (fun s x => HyperbolicChart.coordinateDerivative (d F) i k
        (HyperbolicChart.coordinateDerivative (d F) i k (h s)) x) :=
    RawCalculus.word_holomorphic_derivative W O _ (hd i k)
      [HyperbolicChart.coordinateVector (d F) i k]
  have sd (i : Fin (d F)) (k : Fin 3) : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞)
      (fun x => HyperbolicChart.coordinateDerivative (d F) i k (h s) x) :=
    fun s hz => contDiff_coordinateDerivative _ (hs s hz) i k
  have sdd (i : Fin (d F)) (k : Fin 3) : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞)
      (fun x => HyperbolicChart.coordinateDerivative (d F) i k
        (HyperbolicChart.coordinateDerivative (d F) i k (h s)) x) :=
    fun s hz => contDiff_coordinateDerivative _ (sd i k s hz) i k
  let t := fun (i : Fin (d F)) s x =>
    -HyperbolicChart.coordinateDerivative (d F) i 2
        (HyperbolicChart.coordinateDerivative (d F) i 2 (h s)) x +
      2 * HyperbolicChart.coordinateDerivative (d F) i 2 (h s) x -
    (Real.exp (2 * x (i, 2)) : ℂ) *
      (HyperbolicChart.coordinateDerivative (d F) i 0
          (HyperbolicChart.coordinateDerivative (d F) i 0 (h s)) x +
        HyperbolicChart.coordinateDerivative (d F) i 1
          (HyperbolicChart.coordinateDerivative (d F) i 1 (h s)) x)
  have st : ∀ i s, s ∈ O → ContDiff ℝ (⊤ : ℕ∞) (t i s) := by
    intro i s hz
    exact ((sdd i 2 s hz).neg.add (contDiff_const.mul (sd i 2 s hz))).sub
      ((contDiff_exp_height i).mul ((sdd i 0 s hz).add (sdd i 1 s hz)))
  have ht : ∀ i, RawCalculus.WordHolomorphic W O (t i) := by
    intro i
    have H1 := RawCalculus.word_holomorphic_neg W O _ (sdd i 2) (hdd i 2)
    have H2 := RawCalculus.word_holomorphic_mul W O _ (sd i 2) (hd i 2)
      (fun _ => (2 : ℂ)) contDiff_const
    have H3 := RawCalculus.word_holomorphic_add W O _ _ (sdd i 0) (sdd i 1) (hdd i 0) (hdd i 1)
    have H4 := RawCalculus.word_holomorphic_mul W O _
      (fun s hz => (sdd i 0 s hz).add (sdd i 1 s hz)) H3
      (fun x => (Real.exp (2 * x (i,2)) : ℂ)) (contDiff_exp_height i)
    have H5 := RawCalculus.word_holomorphic_add W O _ _
      (fun s hz => (sdd i 2 s hz).neg)
      (fun s hz => contDiff_const.mul (sd i 2 s hz)) H1 H2
    have H6 := RawCalculus.word_holomorphic_neg W O _
      (fun s hz => (contDiff_exp_height i).mul ((sdd i 0 s hz).add (sdd i 1 s hz))) H4
    exact RawCalculus.word_holomorphic_add W O _ _
      (fun s hz => (sdd i 2 s hz).neg.add (contDiff_const.mul (sd i 2 s hz)))
      (fun s hz => ((contDiff_exp_height i).mul ((sdd i 0 s hz).add (sdd i 1 s hz))).neg) H5 H6
  have H := RawCalculus.word_holomorphic_sum (Finset.univ.toList : List (Fin (d F))) W O t
    (fun i _ s hz => st i s hz) ht
  have he : (fun s x => ((Finset.univ.toList : List (Fin (d F))).map
      (fun i => t i s x)).sum) =
      (fun s x => HyperbolicChart.laplacian (d F) (h s) x) := by
    funext s x
    rw [Finset.sum_map_toList]
    rfl
  rw [he] at H
  exact H

private theorem cd_congr (f g : M F → ℂ) (x : M F) (he : f =ᶠ[𝓝 x] g)
    (i : Fin (d F)) (k : Fin 3) :
    HyperbolicChart.coordinateDerivative (d F) i k f x =
      HyperbolicChart.coordinateDerivative (d F) i k g x := by
  simp only [HyperbolicChart.coordinateDerivative]
  rw [he.fderiv_eq]

private theorem cd_eventuallyEq (f g : M F → ℂ) (x : M F) (he : f =ᶠ[𝓝 x] g)
    (i : Fin (d F)) (k : Fin 3) :
    (fun y => HyperbolicChart.coordinateDerivative (d F) i k f y) =ᶠ[𝓝 x]
      (fun y => HyperbolicChart.coordinateDerivative (d F) i k g y) := by
  filter_upwards [he.eventuallyEq_nhds] with y hy using cd_congr f g y hy i k

private theorem laplacian_congr (f g : M F → ℂ) (x : M F) (he : f =ᶠ[𝓝 x] g) :
    HyperbolicChart.laplacian (d F) f x = HyperbolicChart.laplacian (d F) g x := by
  unfold HyperbolicChart.laplacian
  apply Finset.sum_congr rfl
  intro i _
  have h22 := cd_eventuallyEq f g x he i 2
  have h00 := cd_eventuallyEq f g x he i 0
  have h11 := cd_eventuallyEq f g x he i 1
  rw [cd_congr _ _ x h22 i 2, cd_congr f g x he i 2,
    cd_congr _ _ x h00 i 0, cd_congr _ _ x h11 i 1]

private theorem raw_test_laplacian_chart_holomorphic
    (φ : ℂ → S_U F ζ hζ U R P H) (O : Set ℂ)
    (a : ActualChart (U := U) (H := H))
    (hh : KPContActualCompactSectionL2Jets.ChartHolomorphicOn a
      (fun s => scalarSections (φ s)) O) :
    KPContActualCompactSectionL2Jets.ChartHolomorphicOn a
      (fun s => scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U (φ s)))) O := by
  let h := fun s => (isotropyChart a).coefficient (scalarSections (φ s))
  have hs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h s) :=
    fun s _ => raw_coefficient_smooth a _ (raw_test_smooth (φ s))
  have hw := RawCalculus.word_holomorphic_of_jets (omega a) (raw_omega_open a) O h hs hh
  have hl := raw_laplacian_word_holomorphic (omega a) O h hs hw
  have he : ∀ s y, y ∈ omega a → (isotropyChart a).coefficient
      (scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U (φ s)))) y =
        HyperbolicChart.laplacian (d F) (h s) y := by
    intro s y hy
    rw [raw_test_laplacian_coefficient (φ s) a ⟨y,hy⟩]
    apply laplacian_congr
    filter_upwards [(raw_omega_open a).mem_nhds hy] with z hz
    change (if hx : z ∈ omega a then (φ s).val a ⟨z,hx⟩ else 0) = h s z
    rw [dif_pos hz]
    exact (congrFun (congrFun (raw_test_representative (φ s)) a) ⟨z,hz⟩).symm
  intro K hK hKω n v
  obtain ⟨j,hj,hjval⟩ := RawCalculus.jets_of_word_holomorphic (omega a) (raw_omega_open a)
    O (fun s x => HyperbolicChart.laplacian (d F) (h s) x)
    (fun s hz => contDiff_laplacian _ (hs s hz)) hl K hK hKω n v
  refine ⟨j,hj,?_⟩
  intro s hz x
  rw [hjval s hz x]
  have hge : (fun y => HyperbolicChart.laplacian (d F) (h s) y) =ᶠ[𝓝 x.val]
      (isotropyChart a).coefficient
        (scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
          (KPContActualSectorTestDifferentialDescent.D_U (φ s)))) :=
    Filter.eventually_of_mem ((raw_omega_open a).mem_nhds (hKω x.property))
      (fun y hy => (he s y hy).symm)
  rw [iteratedFDerivWithin_of_isOpen n (raw_omega_open a) (hKω x.property),
    iteratedFDerivWithin_of_isOpen n (raw_omega_open a) (hKω x.property)]
  have hgew : _ := hge.filter_mono (nhdsWithin_le_nhds (s := Set.univ))
  simpa only [iteratedFDerivWithin_univ] using
    congrArg (fun L => L v) (hgew.iteratedFDerivWithin_eq (𝕜 := ℝ) hge.self_of_nhds n)

private theorem raw_coordinate_word (w : List (Fin (d F) × Fin 3)) (u : M F → ℂ) :
    RightFrame.PullbackWords.directionalWord
      (fun i _ => HyperbolicChart.coordinateVector (d F) i.1 i.2) w u =
    RightFrame.PullbackWords.constantDirectionWord
      (w.map (fun i => HyperbolicChart.coordinateVector (d F) i.1 i.2)) u := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, RightFrame.PullbackWords.constantDirectionWord,
      RightFrame.PullbackWords.directionalWord] at *; rw [ih]

private theorem raw_coordinate_parameter_commute (W : Set (M F)) (hW : IsOpen W)
    (O : Set ℂ) (hO : IsOpen O) (h : ℂ → M F → ℂ)
    (hs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h s))
    (hh : RawCalculus.WordHolomorphic W O h)
    (k : ℕ) (s : ℂ) (hz : s ∈ O) (w : List (Fin (d F) × Fin 3)) (x : M F) (hx : x ∈ W) :
    RightFrame.PullbackWords.directionalWord
      (fun i _ => HyperbolicChart.coordinateVector (d F) i.1 i.2) w
        (fun y => iteratedDerivWithin k (fun z => h z y) O s) x =
      iteratedDerivWithin k (fun z => RightFrame.PullbackWords.directionalWord
        (fun i _ => HyperbolicChart.coordinateVector (d F) i.1 i.2) w (h z) x) O s := by
  apply RawCauchy.parameter_word_commute W hW
    (fun i _ => HyperbolicChart.coordinateVector (d F) i.1 i.2)
    (fun _ => contDiffOn_const) ?_ O hO h (fun z hz => (hs z hz).contDiffOn) ?_ ?_ k s hz w x hx
  · intro y hy
    refine ⟨(EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℝ).toBasis, ?_⟩
    intro i
    change EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℝ i = _
    rw [EuclideanSpace.basisFun_apply]
    ext j
    simp [PiLp.single_apply, HyperbolicChart.coordinateVector]
  · intro w K hK hKW
    simp_rw [raw_coordinate_word]
    exact RawCauchy.joint_of_compact_family O W _
      (hh (w.map (fun i => HyperbolicChart.coordinateVector (d F) i.1 i.2))) K hK hKW
  · intro w y hy
    simp_rw [raw_coordinate_word]
    exact RawCauchy.point_of_compact_family O W _
      (hh (w.map (fun i => HyperbolicChart.coordinateVector (d F) i.1 i.2))) y hy

private theorem raw_coordinate_parameter_smooth (W : Set (M F)) (O : Set ℂ) (hO : IsOpen O)
    (h : ℂ → M F → ℂ) (hh : RawCalculus.WordHolomorphic W O h)
    (w : List (Fin (d F) × Fin 3)) (x : M F) (hx : x ∈ W) (k : ℕ) :
    ContDiffOn ℂ k (fun z => RightFrame.PullbackWords.directionalWord
      (fun i _ => HyperbolicChart.coordinateVector (d F) i.1 i.2) w (h z) x) O := by
  simp_rw [raw_coordinate_word]
  exact (RawCauchy.point_of_compact_family O W _
    (hh (w.map (fun i => HyperbolicChart.coordinateVector (d F) i.1 i.2))) x hx).contDiffOn hO

private theorem raw_laplacian_parameter_commute (W : Set (M F)) (hW : IsOpen W)
    (O : Set ℂ) (hO : IsOpen O) (h : ℂ → M F → ℂ)
    (hs : ∀ s ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h s))
    (hh : RawCalculus.WordHolomorphic W O h)
    (k : ℕ) (s : ℂ) (hz : s ∈ O) (x : M F) (hx : x ∈ W) :
    HyperbolicChart.laplacian (d F)
      (fun y => iteratedDerivWithin k (fun z => h z y) O s) x =
      iteratedDerivWithin k (fun z => HyperbolicChart.laplacian (d F) (h z) x) O s := by
  have hd (i : Fin (d F)) (j : Fin 3) :=
    raw_coordinate_parameter_commute W hW O hO h hs hh k s hz [(i,j)] x hx
  have hdd (i : Fin (d F)) (j : Fin 3) :=
    raw_coordinate_parameter_commute W hW O hO h hs hh k s hz [(i,j),(i,j)] x hx
  have sd (i : Fin (d F)) (j : Fin 3) : ContDiffOn ℂ k
      (fun z => HyperbolicChart.coordinateDerivative (d F) i j (h z) x) O :=
    raw_coordinate_parameter_smooth W O hO h hh [(i,j)] x hx k
  have sdd (i : Fin (d F)) (j : Fin 3) : ContDiffOn ℂ k
      (fun z => HyperbolicChart.coordinateDerivative (d F) i j
        (HyperbolicChart.coordinateDerivative (d F) i j (h z)) x) O :=
    raw_coordinate_parameter_smooth W O hO h hh [(i,j),(i,j)] x hx k
  simp only [RightFrame.PullbackWords.directionalWord] at hd hdd
  change (∀ i j, HyperbolicChart.coordinateDerivative (d F) i j
    (fun y => iteratedDerivWithin k (fun z => h z y) O s) x = _) at hd
  change (∀ i j, HyperbolicChart.coordinateDerivative (d F) i j
    (HyperbolicChart.coordinateDerivative (d F) i j
      (fun y => iteratedDerivWithin k (fun z => h z y) O s)) x = _) at hdd
  unfold HyperbolicChart.laplacian
  rw [iteratedDerivWithin_fun_sum hz hO.uniqueDiffOn
    (fun i _ => (((sdd i 2).neg.add (contDiffOn_const.mul (sd i 2))).sub
      (contDiffOn_const.mul ((sdd i 0).add (sdd i 1)))).contDiffWithinAt hz)]
  apply Finset.sum_congr rfl
  intro i hi
  conv_rhs =>
    change iteratedDerivWithin k
      ((fun z => -HyperbolicChart.coordinateDerivative (d F) i 2
        (HyperbolicChart.coordinateDerivative (d F) i 2 (h z)) x +
        2 * HyperbolicChart.coordinateDerivative (d F) i 2 (h z) x) -
       (fun z => (Real.exp (2 * x (i,2)) : ℂ) *
        (HyperbolicChart.coordinateDerivative (d F) i 0
          (HyperbolicChart.coordinateDerivative (d F) i 0 (h z)) x +
         HyperbolicChart.coordinateDerivative (d F) i 1
          (HyperbolicChart.coordinateDerivative (d F) i 1 (h z)) x))) O s
  rw [iteratedDerivWithin_sub hz hO.uniqueDiffOn
    (((sdd i 2).neg.add ((contDiffOn_const (c := (2:ℂ))).mul (sd i 2))).contDiffWithinAt hz)
    (((contDiffOn_const (c := (Real.exp (2 * x (i,2)) : ℂ))).mul ((sdd i 0).add (sdd i 1))).contDiffWithinAt hz),
    iteratedDerivWithin_fun_add hz hO.uniqueDiffOn ((sdd i 2).neg.contDiffWithinAt hz)
      (((contDiffOn_const (c := (2:ℂ))).mul (sd i 2)).contDiffWithinAt hz),
    iteratedDerivWithin_fun_neg,
    iteratedDerivWithin_const_mul_field, iteratedDerivWithin_const_mul_field,
    iteratedDerivWithin_fun_add hz hO.uniqueDiffOn
      ((sdd i 0).contDiffWithinAt hz) ((sdd i 1).contDiffWithinAt hz)]
  simp only [HyperbolicChart.coordinateDerivative] at *
  rw [hd i 2, hdd i 2, hdd i 0, hdd i 1]
  rfl

open KPContSectorCoveredQuotientVocabulary
private theorem shrink_at (i : Fin (H.atlas U).componentCount) (p : SymmetricSpace F) :
    ∃ C : ActualChart (U := U) (H := H), C.component = i ∧ C.center = p ∧ p ∈ C.domain := by
  let O := Classical.choice (KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ U R P H i p)
  letI : Finite (MulAction.stabilizer
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) p) :=
    KPContSectorPhaseComponentCharts.chart_stabilizer_finite F ζ hζ U R P H i p O
  letI := Fintype.ofFinite (MulAction.stabilizer
    (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) p)
  obtain ⟨W, hWo, hpW, hWsub, hWc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := p)) O.isOpen (Set.singleton_subset_iff.mpr O.center_mem)
  let V := ⋂ g : MulAction.stabilizer
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) p,
    (fun x : SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • x) ⁻¹' W
  have hopen : IsOpen V := isOpen_iInter_of_finite fun g =>
    hWo.preimage (KPCuspSiegel.continuous_action F g.val.val)
  have hsub : V ⊆ W := by
    intro x hx
    simpa using Set.mem_iInter.mp hx (1 : MulAction.stabilizer
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) p)
  have hp : p ∈ V := by
    apply Set.mem_iInter.mpr; intro g
    change g.val • p ∈ W
    rw [MulAction.mem_stabilizer_iff.mp g.property]
    exact hpW (Set.mem_singleton p)
  refine ⟨⟨i, p, O, V, hopen, hWc.of_isClosed_subset isClosed_closure (closure_mono hsub),
    (closure_mono hsub).trans hWsub, ?_⟩, rfl, rfl, hp⟩
  intro g
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using Set.mem_iInter.mp hy (h * g)
  · intro hx
    refine ⟨(g.val : KPCuspArithmetic.PGL2 F)⁻¹ • x, ?_, smul_inv_smul _ _⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul]
      using Set.mem_iInter.mp hx (h * g⁻¹)

private theorem raw_test_laplacian_parameter_jets
    (φ : ℕ → ℂ → S_U F ζ hζ U R P H) (O : Set ℂ) (hO : IsOpen O)
    (hj : ∀ k s, s ∈ O → ∀ i x,
      (scalarSections (φ k s) i).val x =
        iteratedDerivWithin k (fun t => (scalarSections (φ 0 t) i).val x) O s)
    (hh : ∀ a : ActualChart (U := U) (H := H),
      KPContActualCompactSectionL2Jets.ChartHolomorphicOn a (fun s => scalarSections (φ 0 s)) O)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) : ∀ i x,
      (scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U (φ k s))) i).val x =
        iteratedDerivWithin k (fun t =>
          (scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
            (KPContActualSectorTestDifferentialDescent.D_U (φ 0 t))) i).val x) O s := by
  intro i x
  obtain ⟨a,ha,hcenter,hx⟩ := shrink_at (F := F) (ζ := ζ) (hζ := hζ) i x
  let y := labeledAInv (placeEquiv F ζ hζ) x
  have hcoord : labeledA (placeEquiv F ζ hζ) y = x := by
    funext j
    simp only [y, labeledA, labeledAInv]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    simp
  have hy : y ∈ omega a := by change labeledA (placeEquiv F ζ hζ) y ∈ a.domain; rwa [hcoord]
  let h := fun t => (isotropyChart a).coefficient (scalarSections (φ 0 t))
  have hsm : ∀ t ∈ O, ContDiff ℝ (⊤ : ℕ∞) (h t) :=
    fun t _ => raw_coefficient_smooth a _ (raw_test_smooth (φ 0 t))
  have hw := RawCalculus.word_holomorphic_of_jets (omega a) (raw_omega_open a) O h hsm (hh a)
  have hk : (isotropyChart a).coefficient (scalarSections (φ k s)) =
      fun z => iteratedDerivWithin k (fun t => h t z) O s := by
    funext z
    dsimp only [h]
    simp only [raw_coefficient_formula]
    exact hj k s hs a.component _
  have hl : ∀ t m z, z ∈ omega a →
      (isotropyChart a).coefficient
        (scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
          (KPContActualSectorTestDifferentialDescent.D_U (φ m t)))) z =
        HyperbolicChart.laplacian (d F)
          ((isotropyChart a).coefficient (scalarSections (φ m t))) z := by
    intro t m z hz
    rw [raw_test_laplacian_coefficient (φ m t) a ⟨z,hz⟩]
    apply laplacian_congr
    filter_upwards [(raw_omega_open a).mem_nhds hz] with v hv
    change (if hx : v ∈ omega a then (φ m t).val a ⟨v,hx⟩ else 0) = _
    rw [dif_pos hv]
    exact (congrFun (congrFun (raw_test_representative (φ m t)) a) ⟨v,hv⟩).symm
  have he := hl s k y hy
  rw [hk, raw_laplacian_parameter_commute (omega a) (raw_omega_open a) O hO h hsm hw k s hs y hy] at he
  have he' : (isotropyChart a).coefficient
      (scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U (φ k s)))) y =
      iteratedDerivWithin k (fun t => (isotropyChart a).coefficient
        (scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
          (KPContActualSectorTestDifferentialDescent.D_U (φ 0 t)))) y) O s := by
    rw [he]
    apply iteratedDerivWithin_congr (s := O) ?_ hs
    intro t ht
    exact (hl t 0 y hy).symm
  simp only [raw_coefficient_formula, hcoord] at he'
  change (scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
      (KPContActualSectorTestDifferentialDescent.D_U (φ k s))) a.component).val x =
    iteratedDerivWithin k (fun t => (scalarSections (KPContActualSectorTestDifferentialDescent.δ_U
      (KPContActualSectorTestDifferentialDescent.D_U (φ 0 t))) a.component).val x) O s at he'
  rw [ha] at he'
  exact he'

end RawTestGeometry

section Actual
open KPContActualChamberThreeL2Tails
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)

private theorem incoming_cutoff_chart_holomorphic
    (a : KPContActualSectorSmoothTestModules.ActualChart
      (U := level F ζ hζ C R P H U) (H := H)) :
    KPContActualCompactSectionL2Jets.ChartHolomorphicOn a
      (fun t => (source.descent.cutoff t).val) V := by
  let ψ : KPContCotangentActualOverlap.M F → KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3) :=
    fun x => WithLp.toLp 2 (fun k =>
      x (finProdFinEquiv.symm k |>.1 |> (KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm,
        (finProdFinEquiv.symm k).2))
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi.mpr
    intro k
    exact (EuclideanSpace.proj (𝕜 := ℝ)
      ((KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm (finProdFinEquiv.symm k).1,
        (finProdFinEquiv.symm k).2)).contDiff
  have hcoords : ∀ x, KPContActualChartRestrictionDensity.coordinates F (ψ x) =
      KPContCotangentActualOverlap.labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x := by
    intro x
    have hp : ∀ i j, (finProdFinEquiv.symm (finProdFinEquiv (i,j)) :
        Fin (KPCuspLogShape.dimension F) × Fin 3) = (i,j) := fun _ _ => Equiv.symm_apply_apply _ _
    funext i
    apply Prod.ext
    · apply Complex.ext <;> change x ((KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm
        (finProdFinEquiv.symm (finProdFinEquiv (i,_))).1,
        (finProdFinEquiv.symm (finProdFinEquiv (i,_))).2) = _
      all_goals rw [hp]; simp [KPContCotangentActualOverlap.labeledA, CotangentLogCoframe.A]
    · change x ((KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm
        (finProdFinEquiv.symm (finProdFinEquiv (i,2))).1,
        (finProdFinEquiv.symm (finProdFinEquiv (i,2))).2) = _
      rw [hp]
      rfl
  let g := fun t => KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U
    (source.descent.cutoff t) a.component
    (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (level F ζ hζ C R P H U) 1)
  have hvalue : ∀ t x,
      g t (ψ x) = (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
        (source.descent.cutoff t).val x := by
    intro t x
    unfold g KPContActualAllCuspSource.chartCoefficient
    rw [KPContActualChartRestrictionDensity.frameCoefficient_class]
    simp only [map_one, Circle.coe_one, one_mul]
    rw [show KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
      (((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U) R P H).symm
        (source.descent.cutoff t)).val) = (source.descent.cutoff t).val from
        congrArg Subtype.val ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
          (level F ζ hζ C R P H U) R P H).apply_symm_apply _)]
    rw [hcoords]
    simp only [KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
      KPContCotangentActualOverlap.LiftedChart.coefficient,
      KPContCotangentActualOverlap.ChartKind.representative, map_one, Units.val_one, one_mul, one_smul]
  intro K hK hKω n v
  apply KPContActualChamberCasimirJets.normalSeries_compact_family_of_local V
    KPChamberL2Defect.chamber_isOpen (KPContCotangentOverlapRationalBranches.omega a)
    (fun t x => iteratedFDerivWithin ℝ n
      ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
        (source.descent.cutoff t).val) (KPContCotangentOverlapRationalBranches.omega a) x v)
    ?_ K hK hKω
  intro x hx
  have hd : IsOpen (KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (level F ζ hζ C R P H U) R P H a.component a.center a.larger) :=
    a.larger.isOpen.preimage (KPContActualChartRestrictionDensity.coordinates F).continuous
  have hxD : ψ x ∈ KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (level F ζ hζ C R P H U) R P H a.component a.center a.larger := by
    change KPContActualChartRestrictionDensity.coordinates F (ψ x) ∈ a.larger.neighborhood
    rw [hcoords]
    exact a.closure_subset (subset_closure hx)
  obtain ⟨r,hr,hrD⟩ := Metric.mem_nhds_iff.mp (hd.mem_nhds hxD)
  let B : KPContLocalNorm.LocalBall (KPCuspLogShape.dimension F * 3) :=
    ⟨by simpa [KPCuspLogShape.dimension] using
      mul_pos (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.2 (by norm_num : (0:ℕ)<3),
      ψ x, r/2, by positivity⟩
  have hBD : KPContLocalCubeEmbedding.closedCarrier B ⊆
      KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (level F ζ hζ C R P H U) R P H a.component a.center a.larger :=
    (Metric.closedBall_subset_ball (by dsimp [B]; linarith)).trans hrD
  have hVs : V ⊆ KPContinuation.spectralDomain := by
    intro t ht
    change -(1:ℝ)/6 < t.re
    change (1:ℝ)/3 < t.re at ht
    linarith
  have hg : KPCutoffSource.ChartSmoothHolomorphicOn B g V := by
    have hh := (source.local_holomorphy a.component a.center a.larger
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (level F ζ hζ C R P H U) 1) B hBD).1
    exact ⟨fun t hz => hh.1 t (hVs hz),
      fun C hC hCB m => by
        obtain ⟨j,hj,hjval⟩ := hh.2 C hC hCB m
        exact ⟨j,hj.mono hVs,
          fun t hz => hjval t (hVs hz)⟩⟩
  let D := ψ ⁻¹' B.carrier
  have hD : IsOpen D := Metric.isOpen_ball.preimage hψ.continuous
  have hxD' : x ∈ D := Metric.mem_ball_self B.radius_pos
  have hω : IsOpen (KPContCotangentOverlapRationalBranches.omega a) := by
    apply a.domain_open.preimage
    apply continuous_pi
    intro i
    exact (continuous_apply _).comp (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).continuous
  obtain ⟨C,hC,hxC,hCD⟩ := exists_compact_subset (hD.inter hω) ⟨hxD',hx⟩
  refine ⟨C,hC,hxC,fun y hy => (hCD hy).2,?_⟩
  obtain ⟨j,hj,hjval⟩ := compact_coordinate_jets_transport B V g hg D hD ψ hψ.contDiffOn
    (fun y hy => hy) C hC (fun y hy => (hCD hy).1) n v
  refine ⟨j,hj,?_⟩
  intro t hz y
  rw [hjval t hz y]
  have he : (g t ∘ ψ) = (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
      (source.descent.cutoff t).val := funext (fun x => hvalue t x)
  rw [he, iteratedFDerivWithin_of_isOpen n hD ((hCD y.property).1),
    iteratedFDerivWithin_of_isOpen n hω ((hCD y.property).2)]

private theorem raw_defect_line_parameter_jets (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    ∀ i x, (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val x =
      iteratedDerivWithin k
        (fun t => (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 t i).val x -
          ((source.descent.cutoff t).val i).val x) V s := by
  intro i x
  rw [lineG, KPContSectorScalarLineAlgebra.S_apply]
  simp only [coveredG, dif_pos hs]
  change iteratedDerivWithin k (fun t => KPContActualChamberNormalSeries.E F ζ hζ U ι f t
      (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
        (Quotient.mk _ (x,(H.atlas (level F ζ hζ C R P H U)).representative i))) -
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff t)
        (Quotient.mk _ (x,(H.atlas (level F ζ hζ C R P H U)).representative i))) V s = _
  apply iteratedDerivWithin_congr (s := V) ?_ hs
  intro t ht
  have hE : (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 t i).val x =
      KPContActualChamberNormalSeries.E F ζ hζ U ι f t
        (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
          (Quotient.mk _ (x,(H.atlas (level F ζ hζ C R P H U)).representative i))) := by
    simp only [KPContActualChamberCasimirJets.lineJet, KPContSectorScalarLineAlgebra.S_apply,
      KPContActualChamberCasimirJets.coveredJet, dif_pos ht,
      KPContActualChamberCasimirJets.jet, iteratedDerivWithin_zero]
  have hC : KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff t)
      (Quotient.mk _ (x,(H.atlas (level F ζ hζ C R P H U)).representative i)) =
      ((source.descent.cutoff t).val i).val x := by
    unfold KPContActualCutoffSmoothDescent.scalar
    rw [← KPContSectorScalarLineAlgebra.S_apply F ζ hζ (level F ζ hζ C R P H U) R P H]
    change (((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
      (level F ζ hζ C R P H U) R P H)
      ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
        (level F ζ hζ C R P H U) R P H).symm (source.descent.cutoff t))).val i).val x = _
    rw [LinearEquiv.apply_symm_apply]
  change _ = (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 t i).val x -
    ((source.descent.cutoff t).val i).val x
  dsimp only
  rw [hE,hC]

private theorem raw_lineG_parameter_jets (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    ∀ i x, (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val x =
      iteratedDerivWithin k
        (fun t => (lineG F ζ hζ C R P H U ι f buffer χ source hι hf 0 t i).val x) V s := by
  intro i x
  rw [raw_defect_line_parameter_jets F ζ hζ C R P H U ι hι f hf buffer χ source k s hs]
  apply iteratedDerivWithin_congr (s := V) ?_ hs
  intro t ht
  exact (raw_defect_line_parameter_jets F ζ hζ C R P H U ι hι f hf buffer χ source 0 t ht i x).symm

private theorem raw_cutoff_parameter_jets
    (r : KPContActualSectorCutoffGraphLimit.Cutoffs
      (U := level F ζ hζ C R P H U) (H := H)) (n k : ℕ) (s : ℂ) (hs : s ∈ V) :
    ∀ i x,
      (KPContActualSectorSmoothTestModules.scalarSections
        (KPContActualSectorCutoffGraphLimit.cutoffTest r n
          (smoothG F ζ hζ C R P H U ι f buffer χ source hι hf k s)) i).val x =
      iteratedDerivWithin k
        (fun t => (KPContActualSectorSmoothTestModules.scalarSections
          (KPContActualSectorCutoffGraphLimit.cutoffTest r n
            (smoothG F ζ hζ C R P H U ι f buffer χ source hι hf 0 t)) i).val x) V s := by
  intro i x
  simp_rw [raw_cutoff_test_sections]
  change (r.rho n (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex
      (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) i x) : ℂ) *
    (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val x = _
  rw [raw_lineG_parameter_jets F ζ hζ C R P H U ι hι f hf buffer χ source k s hs i x]
  exact (iteratedDerivWithin_const_mul_field _ _).symm

private theorem raw_defect_chart_holomorphic
    (a : KPContActualSectorSmoothTestModules.ActualChart
      (U := level F ζ hζ C R P H U) (H := H)) :
    KPContActualCompactSectionL2Jets.ChartHolomorphicOn a
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf 0) V := by
  have hhol := raw_chart_sub a V
    (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0)
    (fun s => (source.descent.cutoff s).val)
    (fun s hs => KPContActualChamberCasimirJets.lineJet_smooth
      F ζ hζ C R P H U ι f hι hf 0 s hs)
    (fun s _ => (source.descent.cutoff s).property)
    (KPContActualChamberCasimirJets.actual_normal_series_chart_holomorphic
      F ζ hζ C R P H U ι f hι hf 0 a)
    (incoming_cutoff_chart_holomorphic F ζ hζ C R P H U ι f buffer χ source a)
  intro K hK hKω n v
  obtain ⟨j,hj,hjval⟩ := hhol K hK hKω n v
  refine ⟨j,hj,?_⟩
  intro s hs x
  rw [hjval s hs x]
  have he : lineG F ζ hζ C R P H U ι f buffer χ source hι hf 0 s =
      KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 s -
        (source.descent.cutoff s).val := by
    funext i
    apply Subtype.ext
    funext y
    exact raw_defect_line_parameter_jets F ζ hζ C R P H U ι hι f hf buffer χ source
      0 s hs i y
  rw [he]

end Actual

theorem raw_actual_cutoff_test_section_jets
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
      KPContinuation.spectralDomain f χ)
    (r : KPContActualSectorCutoffGraphLimit.Cutoffs
      (U := KPContActualAllCuspSource.level F ζ hζ C R P H U) (H := H)) (n : ℕ) :
    let φ := fun k s => KPContActualSectorCutoffGraphLimit.cutoffTest r n
      (KPContActualChamberThreeL2Tails.smoothG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
    let σ := fun (b : Bool) k s => KPContActualSectorSmoothTestModules.scalarSections
      (if b then KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U (φ k s)) else φ k s)
    ∃ K : Set (KPContActualAllCuspSource.Base F ζ hζ C R P H U), IsCompact K ∧
      (∀ (b : Bool) s, s ∈ KPContActualChamberThreeL2Tails.V →
        KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H (σ b 0 s) ∧
        tsupport (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H (σ b 0 s)) ⊆ K) ∧
      (∀ (b : Bool) (a : KPContActualSectorSmoothTestModules.ActualChart
          (U := KPContActualAllCuspSource.level F ζ hζ C R P H U) (H := H)),
        KPContActualCompactSectionL2Jets.ChartHolomorphicOn a (σ b 0)
          KPContActualChamberThreeL2Tails.V) ∧
      (∀ (b : Bool) (k : ℕ) (s : ℂ), s ∈ KPContActualChamberThreeL2Tails.V → ∀ i x,
        (σ b k s i).val x = iteratedDerivWithin k (fun t => (σ b 0 t i).val x)
          KPContActualChamberThreeL2Tails.V s) := by
  intro φ σ
  have hh : ∀ a : KPContActualSectorSmoothTestModules.ActualChart
      (U := KPContActualAllCuspSource.level F ζ hζ C R P H U) (H := H),
      KPContActualCompactSectionL2Jets.ChartHolomorphicOn a
        (fun s => KPContActualSectorSmoothTestModules.scalarSections (φ 0 s))
        KPContActualChamberThreeL2Tails.V := by
    intro a
    exact raw_cutoff_chart_holomorphic r n
      (KPContActualChamberThreeL2Tails.smoothG F ζ hζ C R P H U ι f buffer χ source hι hf 0)
      KPContActualChamberThreeL2Tails.V a
      (raw_defect_chart_holomorphic F ζ hζ C R P H U ι hι f hf buffer χ source a)
  refine ⟨tsupport (r.rho n), r.compact_support n, ?_, ?_, ?_⟩
  · intro b s hs
    exact raw_cutoff_test_common_support r n
      (KPContActualChamberThreeL2Tails.smoothG F ζ hζ C R P H U ι f buffer χ source hι hf 0 s) b
  · intro b a
    cases b
    · exact hh a
    · exact raw_test_laplacian_chart_holomorphic (φ 0) KPContActualChamberThreeL2Tails.V a (hh a)
  · intro b k s hs
    cases b
    · exact raw_cutoff_parameter_jets F ζ hζ C R P H U ι hι f hf buffer χ source r n k s hs
    · exact raw_test_laplacian_parameter_jets φ KPContActualChamberThreeL2Tails.V
        KPChamberL2Defect.chamber_isOpen
        (fun k s hs => raw_cutoff_parameter_jets F ζ hζ C R P H U ι hι f hf buffer χ source r n k s hs)
        hh k s hs

end DedekindZetaZeroFree.KPContActualChamberGraphHolomorphy

end
