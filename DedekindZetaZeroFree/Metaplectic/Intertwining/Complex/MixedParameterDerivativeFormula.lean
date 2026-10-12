module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Complex.ScalarWeightJetBounds
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Conformal

@[expose] public section

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant.MatrixWeighted

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

namespace ParameterJets

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem joints_spatial_jets_at (F : ℂ × E → V) (U : Set E) (hU : IsOpen U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.univ ×ˢ U)) (n : ℕ)
    (p : ℂ × E) (hp : p.2 ∈ U) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℂ × E =>
      iteratedFDeriv ℝ n (fun x => F (p.1, x)) p.2) p := by
  induction n generalizing p with
  | zero =>
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p
        (hF.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ _, hp⟩))
  | succ n ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℂ × E =>
        fderiv ℝ (iteratedFDeriv ℝ n (fun x => F (p.1, x))) p.2) p := by
      exact ((ih (p.1,p.2) hp).comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).fderiv
        (m := (⊤ : ℕ∞)) contDiffAt_snd (by simp)
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p hd

private lemma direction_commute (F : E → V) (x : E) (hF : ContDiffAt ℝ (⊤ : ℕ∞) F x)
    (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ F y a) x b =
      fderiv ℝ (fun y => fderiv ℝ F y b) x a := by
  have hd := (hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const a),
    fderiv_clm_apply hd (differentiableAt_const b)]
  simpa using hF.isSymmSndFDerivAt (by simp [minSmoothness]) b a

private lemma jet_succ (F : ℂ × E → V) (U : Set E) (hU : IsOpen U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.univ ×ˢ U)) (n : ℕ)
    (p : ℂ × E) (hp : p.2 ∈ U) (m : Fin (n+1) → E) :
    iteratedFDeriv ℝ (n+1) (fun y => F (p.1,y)) p.2 m =
      fderiv ℝ (fun q : ℂ × E => iteratedFDeriv ℝ n (fun y => F (q.1,y)) q.2)
        p (0,m 0) (Fin.tail m) := by
  rw [iteratedFDeriv_succ_apply_left]
  have hh : HasFDerivAt (fun y => iteratedFDeriv ℝ n (fun z => F (p.1,z)) y)
      ((fderiv ℝ (fun q : ℂ × E => iteratedFDeriv ℝ n (fun y => F (q.1,y)) q.2) p).comp
        (ContinuousLinearMap.inr ℝ ℂ E)) p.2 := by
    convert ((joints_spatial_jets_at F U hU hF n p hp).differentiableAt (by simp)).hasFDerivAt.comp p.2
      ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2)) using 1 <;> ext <;> rfl
  rw [hh.fderiv]
  rfl

theorem jet_parameter_direction_commute (F : ℂ × E → V) (U : Set E) (hU : IsOpen U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.univ ×ˢ U)) (n : ℕ)
    (p : ℂ × E) (hp : p.2 ∈ U) (z : ℂ) :
    fderiv ℝ (fun q : ℂ × E => iteratedFDeriv ℝ n (fun y => F (q.1,y)) q.2)
      p (z,0) =
      iteratedFDeriv ℝ n (fun y => fderiv ℝ F (p.1,y) (z,0)) p.2 := by
  induction n generalizing p with
  | zero =>
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((joints_spatial_jets_at F U hU hF 0 p hp).differentiableAt (by simp))]
    simp only [iteratedFDeriv_zero_apply]
  | succ n ih =>
    let J := fun q : ℂ × E => iteratedFDeriv ℝ n (fun y => F (q.1,y)) q.2
    have hJ := joints_spatial_jets_at F U hU hF n p hp
    let P := fun q : ℂ × E => fderiv ℝ F q (z,0)
    have hP : ContDiffOn ℝ (⊤ : ℕ∞) P (Set.univ ×ˢ U) := by
      exact (hF.fderiv_of_isOpen (isOpen_univ.prod hU) (by simp)).clm_apply contDiffOn_const
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((joints_spatial_jets_at F U hU hF (n+1) p hp).differentiableAt (by simp))]
    have heq : (fun q : ℂ × E => iteratedFDeriv ℝ (n+1) (fun y => F (q.1,y)) q.2 m) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ J q (0,m 0) (Fin.tail m)) := by
      filter_upwards [(isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ p.1, hp⟩] with q hq
      exact jet_succ F U hU hF n q hq.2 m
    rw [heq.fderiv_eq]
    rw [fderiv_continuousMultilinear_apply_const_apply
      (((hJ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp))]
    rw [direction_commute J p hJ (0,m 0) (z,0)]
    rw [← fderiv_continuousMultilinear_apply_const_apply
      (((hJ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp))]
    have heq' : (fun q : ℂ × E => fderiv ℝ J q (z,0) (Fin.tail m)) =ᶠ[𝓝 p]
        (fun q => iteratedFDeriv ℝ n (fun y => P (q.1,y)) q.2 (Fin.tail m)) := by
      filter_upwards [(isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ p.1, hp⟩] with q hq
      exact congrArg (fun c => c (Fin.tail m)) (ih q hq.2)
    rw [heq'.fderiv_eq]
    rw [fderiv_continuousMultilinear_apply_const_apply
      ((joints_spatial_jets_at P U hU hP n p hp).differentiableAt (by simp))]
    exact (jet_succ P U hU hP n p hp m).symm

theorem spatial_jet_hasDerivAt (F P : ℂ × E → ℂ) (U : Set E) (hU : IsOpen U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.univ ×ˢ U))
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) P (Set.univ ×ˢ U))
    (hd : ∀ t v, v ∈ U → HasDerivAt (fun s => F (s,v)) (P (t,v)) t)
    (n : ℕ) (t : ℂ) (u : E) (hu : u ∈ U) (a : Fin n → E) :
    HasDerivAt (fun s => iteratedFDeriv ℝ n (fun v => F (s,v)) u a)
      (iteratedFDeriv ℝ n (fun v => P (t,v)) u a) t := by
  let J := fun q : ℂ × E => iteratedFDeriv ℝ n (fun v => F (q.1,v)) q.2
  have hJ := joints_spatial_jets_at F U hU hF n (t,u) hu
  have hslice : HasFDerivAt (fun s => J (s,u))
      ((fderiv ℝ J (t,u)).comp (ContinuousLinearMap.inl ℝ ℂ E)) t := by
    convert (hJ.differentiableAt (by simp)).hasFDerivAt.comp t
      ((hasFDerivAt_id (𝕜 := ℝ) t).prodMk (hasFDerivAt_const (𝕜 := ℝ) u t)) using 1 <;> ext <;> rfl
  have heval : HasFDerivAt (fun s => J (s,u) a)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℂ a).comp
        ((fderiv ℝ J (t,u)).comp (ContinuousLinearMap.inl ℝ ℂ E))) t := by
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℂ a).hasFDerivAt.comp t hslice
  have hdir (z : ℂ) : fderiv ℝ (fun s => J (s,u) a) t z =
      z * iteratedFDeriv ℝ n (fun v => P (t,v)) u a := by
    rw [heval.fderiv]
    change fderiv ℝ J (t,u) (z,0) a = _
    rw [jet_parameter_direction_commute F U hU hF n (t,u) hu z]
    have he : (fun v => fderiv ℝ F (t,v) (z,0)) =ᶠ[𝓝 u] (fun v => z * P (t,v)) := by
      filter_upwards [hU.mem_nhds hu] with v hv
      have hs : HasFDerivAt (fun s => F (s,v))
          ((fderiv ℝ F (t,v)).comp (ContinuousLinearMap.inl ℝ ℂ E)) t := by
        convert ((hF.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ t,hv⟩)).differentiableAt (by simp)).hasFDerivAt.comp t
          ((hasFDerivAt_id (𝕜 := ℝ) t).prodMk (hasFDerivAt_const (𝕜 := ℝ) v t)) using 1 <;> ext <;> rfl
      have hh := congrArg (fun L : ℂ →L[ℝ] ℂ => L z)
        (hs.unique ((hd t v hv).hasFDerivAt.restrictScalars ℝ))
      simpa [ContinuousLinearMap.comp_apply, mul_comm] using hh
    rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
    let L : ℂ →L[ℝ] ℂ := (z • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ
    have hps : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => P (t,v)) u :=
      (hP.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ t, hu⟩)).comp u
        (contDiffAt_const.prodMk contDiffAt_id)
    exact congrArg (fun M => M a) (L.iteratedFDeriv_comp_left hps (by simp))
  have hcr : fderiv ℝ (fun s => J (s,u) a) t Complex.I =
      Complex.I • fderiv ℝ (fun s => J (s,u) a) t 1 := by
    rw [hdir, hdir]
    simp [smul_eq_mul]
  convert complexOfReal_hasDerivAt heval.differentiableAt hcr using 1
  change iteratedFDeriv ℝ n (fun v => P (t,v)) u a = fderiv ℝ (fun s => J (s,u) a) t 1
  rw [hdir, one_mul]

theorem operator_iteratedDeriv_of_family {n j : ℕ}
    (c : (q : Fin (j+1)) → (Fin q.val → Fin n) → (Fin n → ℝ) → ℂ)
    (F : ℕ → ℂ × (Fin n → ℝ) → ℂ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hF : ∀ m, ContDiffOn ℝ (⊤ : ℕ∞) (F m) (Set.univ ×ˢ U))
    (hd : ∀ m t v, v ∈ U → HasDerivAt (fun s => F m (s,v)) (F (m+1) (t,v)) t)
    (m : ℕ) (t : ℂ) (u : Fin n → ℝ) (hu : u ∈ U) :
    iteratedDeriv m (fun s => operatorApply c (fun v => F 0 (s,v)) u) t =
      operatorApply c (fun v => F m (t,v)) u := by
  have hdop (k : ℕ) (s : ℂ) : HasDerivAt
      (fun s => operatorApply c (fun v => F k (s,v)) u)
      (operatorApply c (fun v => F (k+1) (s,v)) u) s := by
    unfold operatorApply
    apply HasDerivAt.fun_sum
    intro q hq
    apply HasDerivAt.fun_sum
    intro a ha
    exact (spatial_jet_hasDerivAt (F k) (F (k+1)) U hU (hF k) (hF (k+1)) (hd k)
      q.val s u hu (fun i => Pi.single (a i) (1 : ℝ))).const_mul (c q a u)
  have hh (k : ℕ) : iteratedDeriv k (fun s => operatorApply c (fun v => F 0 (s,v)) u) =
      (fun s => operatorApply c (fun v => F k (s,v)) u) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      exact (hdop k s).deriv
  exact congrFun (hh m) t

end ParameterJets

theorem parameter_weighted_section_hasDerivAt (k : ℕ) (φ : ComplexProjectiveLine → ℂ)
    (g : ComplexGL2) (s : ℂ) :
    HasDerivAt (fun t : ℂ =>
      (2 * (Real.log (ratio g) : ℂ)) ^ k * reconstructedSection t φ g)
      ((2 * (Real.log (ratio g) : ℂ)) ^ (k+1) * reconstructedSection s φ g) s := by
  have hd : HasDerivAt (fun t : ℂ => ((4 / 3 : ℂ) + 2 * t) *
      (Real.log (ratio g) : ℂ)) (2 * (Real.log (ratio g) : ℂ)) s := by
    simpa using (((hasDerivAt_id s).const_mul (2 : ℂ)).const_add (4 / 3 : ℂ)).mul_const
      (Real.log (ratio g) : ℂ)
  convert (hd.cexp.mul_const (φ (line g))).const_mul
      ((2 * (Real.log (ratio g) : ℂ)) ^ k) using 1
  · rfl
  change (2 * (Real.log (ratio g) : ℂ)) ^ (k+1) *
    (Complex.exp (((4 / 3 : ℂ) + 2 * s) * (Real.log (ratio g) : ℂ)) * φ (line g)) = _
  ring

theorem parameter_derivative_operator_formula (n j : ℕ)
    (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (g : (Fin n → ℝ) → ComplexGL2)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v => (g v : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (c : (q : Fin (j + 1)) → (Fin q.val → Fin n) → (Fin n → ℝ) → ℂ)
    (φ : ComplexProjectiveLine → ℂ)
    (hop : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen))
    (hinf : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity))
    (m : ℕ) (x s : ℂ) (u : Fin n → ℝ) (hu : u ∈ U) :
    iteratedDeriv m (fun t : ℂ => operatorApply c (fun v =>
      reconstructedSection t φ (weyl * upperUnipotent x * g v)) u) s =
    operatorApply c (fun v =>
      (2 * (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ)) ^ m *
        reconstructedSection s φ (weyl * upperUnipotent x * g v)) u := by
  have hprod : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v => (weyl * upperUnipotent x * g v : Matrix (Fin 2) (Fin 2) ℂ)) U := by
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun v =>
      (weyl * upperUnipotent x : Matrix (Fin 2) (Fin 2) ℂ) *
        (g v : Matrix (Fin 2) (Fin 2) ℂ)) U
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    simp only [Matrix.mul_apply]
    apply ContDiffOn.sum
    intro k _
    have he : ContDiff ℝ (⊤ : ℕ∞)
        (fun M : Matrix (Fin 2) (Fin 2) ℂ => M k j) := by fun_prop
    exact contDiffOn_const.mul (he.comp_contDiffOn hg)
  obtain ⟨B, hB, hsources⟩ := compact_projective_source_jets n 0 U ∅ hU
    isCompact_empty (Set.empty_subset U) g hg
  have hsource := (hsources φ hop hinf x).1
  have hlog := scalar_log_ratio_contDiffOn
    (g := fun v => weyl * upperUnipotent x * g v) hprod
  have hl : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℂ × (Fin n → ℝ) =>
      (Real.log (ratio (weyl * upperUnipotent x * g p.2)) : ℂ)) (Set.univ ×ˢ U) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hlog).comp
      contDiff_snd.contDiffOn (fun _ hp => hp.2)
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℂ × (Fin n → ℝ) =>
      φ (line (weyl * upperUnipotent x * g p.2))) (Set.univ ×ˢ U) :=
    hsource.comp contDiff_snd.contDiffOn (fun _ hp => hp.2)
  let F : ℕ → ℂ × (Fin n → ℝ) → ℂ := fun k p =>
    (2 * (Real.log (ratio (weyl * upperUnipotent x * g p.2)) : ℂ)) ^ k *
      reconstructedSection p.1 φ (weyl * upperUnipotent x * g p.2)
  have hF (k : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (F k) (Set.univ ×ˢ U) := by
    dsimp [F, reconstructedSection]
    exact ((contDiffOn_const.mul hl).pow k).mul
      ((((contDiffOn_const.add (contDiffOn_const.mul contDiff_fst.contDiffOn)).mul hl).cexp).mul hφ)
  have hd (k : ℕ) (t : ℂ) (v : Fin n → ℝ) (_hv : v ∈ U) :
      HasDerivAt (fun s => F k (s,v)) (F (k+1) (t,v)) t :=
    parameter_weighted_section_hasDerivAt k φ (weyl * upperUnipotent x * g v) t
  simpa only [F, pow_zero, one_mul] using
    ParameterJets.operator_iteratedDeriv_of_family c F U hU hF hd m s u hu

end DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant.MatrixWeighted

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant.MatrixWeighted

private lemma log_absorb (m : ℕ) {ε : ℝ} (hε : 0 < ε) (y : ℝ) (hy : 1 ≤ y) :
    (1 + Real.log y) ^ m ≤ (1 + m / ε) ^ m * y ^ ε := by
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  have hypos : 0 < y := lt_of_lt_of_le one_pos hy
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, Nat.cast_zero, zero_div, add_zero, one_mul]
    exact Real.one_le_rpow hy hε.le
  · have hδpos : 0 < ε / m := div_pos hε (by exact_mod_cast hm)
    have hlog : 1 + Real.log y ≤ (1 + m / ε) * y ^ (ε / m) := by
      have h1 : Real.log y ≤ y ^ (ε / m) / (ε / m) := Real.log_le_rpow_div hy0 hδpos
      have h2 : y ^ (ε / m) / (ε / m) = (m / ε) * y ^ (ε / m) := by
        rw [div_eq_mul_inv, inv_div, mul_comm]
      rw [h2] at h1
      have h3 : (1 : ℝ) ≤ y ^ (ε / m) := Real.one_le_rpow hy hδpos.le
      nlinarith [h1, h3, Real.rpow_nonneg hy0 (ε / m)]
    have hL : 0 ≤ 1 + Real.log y := by
      have := Real.log_nonneg hy; linarith
    calc (1 + Real.log y) ^ m
        ≤ ((1 + m / ε) * y ^ (ε / m)) ^ m := pow_le_pow_left₀ hL hlog m
      _ = (1 + m / ε) ^ m * (y ^ (ε / m)) ^ m := by rw [mul_pow]
      _ = (1 + m / ε) ^ m * y ^ ε := by
            congr 1
            rw [← Real.rpow_natCast (y ^ (ε / m)) m, ← Real.rpow_mul hy0 (ε / m) m]
            congr 1
            field_simp

theorem logarithmic_envelope_absorption (m : ℕ) (a p : ℝ) (hp : p < a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (t : ℝ) (x : ℂ), a ≤ t →
      (1 + Real.log (1 + ‖x‖ ^ 2)) ^ m * envelope t x ≤ D * envelope p x := by
  have hε : 0 < a - p := sub_pos.mpr hp
  refine ⟨(1 + m / (a - p)) ^ m, by positivity, ?_⟩
  intro t x hat
  set y : ℝ := 1 + ‖x‖ ^ 2 with hy
  have hy1 : 1 ≤ y := by
    rw [hy]; linarith [sq_nonneg (‖x‖ : ℝ)]
  have hypos : 0 < y := lt_of_lt_of_le one_pos hy1
  have hy0 : 0 ≤ y := hypos.le
  have hLnn : 0 ≤ (1 + Real.log y) ^ m := by
    apply pow_nonneg
    have := Real.log_nonneg hy1; linarith
  have hmain := log_absorb m hε y hy1
  rw [envelope, envelope, ← hy]
  calc (1 + Real.log y) ^ m * y ^ (-t)
      ≤ (1 + Real.log y) ^ m * y ^ (-a) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)) hLnn
    _ ≤ ((1 + m / (a - p)) ^ m * y ^ (a - p)) * y ^ (-a) :=
        mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg hy0 (-a))
    _ = (1 + m / (a - p)) ^ m * y ^ (-p) := by
        have hexp : a - p + -a = -p := by ring
        rw [mul_assoc, ← Real.rpow_add hypos (a - p) (-a), hexp]

end DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant.MatrixWeighted

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant.MatrixWeighted

open scoped ContDiff

theorem finite_order_product_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (U : Set E) (hU : IsOpen U) (u : E) (hu : u ∈ U)
    (f h : E → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h U)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfj : ∀ q ≤ j, ‖iteratedFDeriv ℝ q f u‖ ≤ A)
    (hhj : ∀ q ≤ j, ‖iteratedFDeriv ℝ q h u‖ ≤ B) :
    ∀ q ≤ j, ‖iteratedFDeriv ℝ q (fun v => f v * h v) u‖ ≤
      (2 : ℝ) ^ j * A * B := by
  intro q hq
  have hW := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := U) (N := (⊤ : ℕ∞))
    hf hh hU.uniqueDiffOn hu (n := q)
    (by exact_mod_cast (le_top : (q : ℕ∞) ≤ ⊤))
  rw [iteratedFDerivWithin_of_isOpen q hU hu] at hW
  refine hW.trans ?_
  have hbinom : (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ)) = (2 : ℝ) ^ q := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have hfactor :
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * A * B
        = (2 : ℝ) ^ q * A * B := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hbinom]
  have hstep :
      ∑ i ∈ Finset.range (q + 1),
          (q.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f U u‖ *
            ‖iteratedFDerivWithin ℝ (q - i) h U u‖ ≤ (2 : ℝ) ^ q * A * B := by
    rw [← hfactor]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hiq : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hqi : q - i ≤ q := Nat.sub_le _ _
    rw [iteratedFDerivWithin_of_isOpen i hU hu, iteratedFDerivWithin_of_isOpen (q - i) hU hu]
    have hc : (0 : ℝ) ≤ (q.choose i : ℝ) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hfj i (hiq.trans hq)) hc)
      (hhj (q - i) (hqi.trans hq))
      (norm_nonneg _) (mul_nonneg hc hA)
  refine hstep.trans ?_
  have hpow : (2 : ℝ) ^ q ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hq
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hA) hB

end DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant.MatrixWeighted

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open scoped ContDiff Matrix.Norms.Elementwise

namespace ReconstructionEstimates

open Set

theorem seminorm_bddAbove (j : ℕ) (φ : ComplexProjectiveLine → ℂ)
    (hφ₀ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen))
    (hφInf : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity)) :
    BddAbove ({0} ∪ {r : ℝ | ∃ q : ℕ, q ≤ j ∧ ∃ z : ℂ,
      z ∈ Metric.closedBall (0 : ℂ) 1 ∧
        (r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ∨
         r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖)}) := by
  let S : ℕ → Set ℝ := fun q =>
    (fun z : ℂ => ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖) '' Metric.closedBall 0 1 ∪
    (fun z : ℂ => ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖) '' Metric.closedBall 0 1
  have hS : ∀ q, BddAbove (S q) := by
    intro q
    exact bddAbove_union.mpr ⟨
      (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
        ((hφ₀.continuous_iteratedFDeriv (by simp)).norm.continuousOn),
      (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
        ((hφInf.continuous_iteratedFDeriv (by simp)).norm.continuousOn)⟩
  have hB : BddAbove (⋃ q ∈ Set.Iic j, S q) :=
    (Set.finite_Iic j).bddAbove_biUnion.mpr (fun q _ => hS q)
  have hB' : BddAbove ({(0 : ℝ)} ∪ ⋃ q ∈ Set.Iic j, S q) :=
    bddAbove_union.mpr ⟨bddAbove_singleton, hB⟩
  refine hB'.mono ?_
  intro r hr
  rcases hr with hr | ⟨q, hq, z, hz, hr | hr⟩
  · exact Or.inl hr
  · right
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, Or.inl ⟨z, hz, hr.symm⟩⟩⟩
  · right
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, Or.inr ⟨z, hz, hr.symm⟩⟩⟩

theorem seminorm_nonneg (j : ℕ) (φ : ComplexProjectiveLine → ℂ)
    (hφ₀ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen))
    (hφInf : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity)) :
    0 ≤ seminorm j φ := by
  exact le_csSup (seminorm_bddAbove j φ hφ₀ hφInf) (Or.inl (Set.mem_singleton 0))

end ReconstructionEstimates

theorem compact_matrix_weighted_bound (n j : ℕ)
    (U K : Set (Fin n → ℝ)) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (g : (Fin n → ℝ) → ComplexGL2)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u => (g u : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (c : (q : Fin (j + 1)) → (Fin q.val → Fin n) → (Fin n → ℝ) → ℂ)
    (hc : ∀ q a, ContDiffOn ℝ (⊤ : ℕ∞) (c q a) U)
    (m : ℕ) (R b p : ℝ) (hR : 0 ≤ R) (hp : p < 4 / 3 + 2 * b) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (s : ℂ) (φ : ComplexProjectiveLine → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen) →
      ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity) →
      ∀ (x : ℂ) (u : Fin n → ℝ), ‖s‖ ≤ R → b ≤ s.re → u ∈ K →
        ‖iteratedDeriv m (fun t : ℂ => operatorApply c (fun v =>
          reconstructedSection t φ (weyl * upperUnipotent x * g v)) u) s‖ ≤
            C * seminorm N φ * envelope p x := by
  classical
  obtain ⟨L, hL, hcoeff⟩ := compact_coefficient_sum_bound U K hK hKU c hc
  obtain ⟨A, hA, hscalar⟩ := MatrixWeighted.compact_scalar_weight_jets
    n j m U K hU hK hKU g hg R hR
  obtain ⟨B, hB, hsource⟩ := MatrixWeighted.compact_projective_source_jets
    n j U K hU hK hKU g hg
  obtain ⟨D, hD, habsorb⟩ := MatrixWeighted.logarithmic_envelope_absorption
    m (4 / 3 + 2 * b) p hp
  refine ⟨L * (2 : ℝ) ^ j * A * B * D, j, by positivity, ?_⟩
  intro s φ hop hinf x u hs hbs hu
  have huU : u ∈ U := hKU hu
  have hsem : 0 ≤ seminorm j φ := seminorm_nonneg j φ hop hinf
  have henv (t : ℝ) : 0 ≤ envelope t x := by
    unfold envelope
    exact Real.rpow_nonneg (by positivity) _
  have henvs := henv (4 / 3 + 2 * s.re)
  have henvp := henv p
  have hlog : 0 ≤ (1 + Real.log (1 + ‖x‖ ^ 2)) ^ m := by
    apply pow_nonneg
    have : 0 ≤ Real.log (1 + ‖x‖ ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg ‖x‖])
    linarith
  let f : (Fin n → ℝ) → ℂ := fun v =>
    (2 * (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ)) ^ m *
      Complex.exp (((4 / 3 : ℂ) + 2 * s) *
        (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ))
  let h : (Fin n → ℝ) → ℂ := fun v => φ (line (weyl * upperUnipotent x * g v))
  obtain ⟨hf, hfj⟩ := hscalar s x hs
  obtain ⟨hh, hhj⟩ := hsource φ hop hinf x
  have hprod := MatrixWeighted.finite_order_product_bound j U hU u huU f h hf hh
    (A * (1 + Real.log (1 + ‖x‖ ^ 2)) ^ m * envelope (4 / 3 + 2 * s.re) x)
    (B * seminorm j φ) (by positivity) (by positivity)
    (fun q hq => hfj q hq u hu) (fun q hq => hhj q hq u hu)
  have hdecay := habsorb (4 / 3 + 2 * s.re) x (by linarith)
  have hjets : ∀ q : Fin (j + 1),
      ‖iteratedFDeriv ℝ q.val (fun v => f v * h v) u‖ ≤
        ((2 : ℝ) ^ j * A * B * D) * seminorm j φ * envelope p x := by
    intro q
    calc
      _ ≤ (2 : ℝ) ^ j *
          (A * (1 + Real.log (1 + ‖x‖ ^ 2)) ^ m * envelope (4 / 3 + 2 * s.re) x) *
          (B * seminorm j φ) := hprod q.val (by omega)
      _ = ((2 : ℝ) ^ j * A * B * seminorm j φ) *
          ((1 + Real.log (1 + ‖x‖ ^ 2)) ^ m * envelope (4 / 3 + 2 * s.re) x) := by ring
      _ ≤ ((2 : ℝ) ^ j * A * B * seminorm j φ) * (D * envelope p x) :=
        mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = _ := by ring
  rw [MatrixWeighted.parameter_derivative_operator_formula n j U hU g hg c φ hop hinf m x s u huU]
  have heq : (fun v =>
      (2 * (Real.log (ratio (weyl * upperUnipotent x * g v)) : ℂ)) ^ m *
        reconstructedSection s φ (weyl * upperUnipotent x * g v)) =
      (fun v => f v * h v) := by
    funext v
    simp only [f, h, reconstructedSection, mul_assoc]
  rw [heq]
  calc
    _ ≤ (∑ q : Fin (j + 1), ∑ a : Fin q.val → Fin n, ‖c q a u‖) *
        (((2 : ℝ) ^ j * A * B * D) * seminorm j φ * envelope p x) :=
      norm_operatorApply_le c _ u _ hjets
    _ ≤ L * (((2 : ℝ) ^ j * A * B * D) * seminorm j φ * envelope p x) :=
      mul_le_mul_of_nonneg_right (hcoeff u hu) (by positivity)
    _ = _ := by ring

end DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant

end
