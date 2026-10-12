module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexIntertwinerImageAndHarmonicExtraction

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxUpperRootSeminormDifferentiation

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open Filter Topology
open scoped Matrix.Norms.Elementwise

theorem upperRoot_open_joint_contDiff (β : ℂˣ) (e : Theta β) (v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℂ =>
      orbitOpenCoordinate negativeParameter (e : PrincipalSeries negativeParameter)
        ((upperUnipotent ((p.1 : ℂ) * v) : Matrix (Fin 2) (Fin 2) ℂ), p.2)) := by
  apply contDiffOn_univ.mp
  apply (image_smooth β e).1.comp _ _
  · apply ContDiff.contDiffOn
    apply ContDiff.prodMk _ contDiff_snd
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ × ℂ => (fun i j => (upperUnipotent ((x.1 : ℂ) * v) : Matrix (Fin 2) (Fin 2) ℂ) i j))
    rw [contDiff_pi]; intro i; rw [contDiff_pi]; intro j
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent]
    all_goals try exact contDiff_const
    exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const
  · intro p hp
    exact Matrix.GeneralLinearGroup.det_ne_zero _

theorem upperRoot_infinity_joint_contDiff (β : ℂˣ) (e : Theta β) (v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℂ =>
      orbitInfinityCoordinate negativeParameter (e : PrincipalSeries negativeParameter)
        ((upperUnipotent ((p.1 : ℂ) * v) : Matrix (Fin 2) (Fin 2) ℂ), p.2)) := by
  apply contDiffOn_univ.mp
  apply (image_smooth β e).2.comp _ _
  · apply ContDiff.contDiffOn
    apply ContDiff.prodMk _ contDiff_snd
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ × ℂ => (fun i j => (upperUnipotent ((x.1 : ℂ) * v) : Matrix (Fin 2) (Fin 2) ℂ) i j))
    rw [contDiff_pi]; intro i; rw [contDiff_pi]; intro j
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent]
    all_goals try exact contDiff_const
    exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const
  · intro p hp
    exact Matrix.GeneralLinearGroup.det_ne_zero _

theorem joint_spatial_jets {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
      iteratedFDeriv ℝ n (fun x => F (p.1, x)) p.2) := by
  induction n with
  | zero =>
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hF
  | succ n ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
        fderiv ℝ (iteratedFDeriv ℝ n (fun x => F (p.1, x))) p.2) := by
      exact (ih.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv
        contDiff_snd (by simp)
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hd

namespace SmoothQuotient
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
noncomputable def partialT (F : ℝ × E → V) (p : ℝ × E) : V :=
  fderiv ℝ (fun t => F (t,p.2)) p.1 1
lemma partialT_smooth (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (partialT F) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
      fderiv ℝ (fun t => F (t,p.2)) p.1) :=
    (hF.comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv contDiff_fst (by simp)
  exact h.clm_apply contDiff_const
lemma partialT_deriv (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) (x : E) :
    HasDerivAt (fun s => F (s,x)) (partialT F (t,x)) t := by
  exact ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt
noncomputable def extSlope (F : ℝ × E → V) (p : ℝ × E) : V :=
  ∫ s : ℝ in 0..1, partialT F (s * p.1, p.2)
lemma extSlope_continuous (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (extSlope F) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (partialT_smooth F hF).continuous.comp
    ((continuous_snd.mul continuous_fst.fst).prodMk continuous_fst.snd)
lemma extSlope_zero (F : ℝ × E → V) (x : E) :
    extSlope F (0,x) = partialT F (0,x) := by
  simp [extSlope, intervalIntegral.integral_const]
lemma extSlope_ne (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (ht : t ≠ 0) (x : E) :
    extSlope F (t,x) = t⁻¹ • (F (t,x) - F (0,x)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (f := fun s : ℝ => F (s*t,x))
    (f' := fun s : ℝ => t • partialT F (s*t,x))
    (fun s _ => by simpa [Function.comp_def] using
      (partialT_deriv F hF (s*t) x).scomp s ((hasDerivAt_id s).mul_const t))
    (((partialT_smooth F hF).continuous.comp
      ((continuous_id.mul continuous_const).prodMk continuous_const)).const_smul t |>.intervalIntegrable 0 1)
  simp only [one_mul, zero_mul, intervalIntegral.integral_smul_const] at h
  change extSlope F (t,x) = _
  rw [← h, intervalIntegral.integral_smul, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rfl
lemma slope_locally_uniform (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [WeaklyLocallyCompactSpace E] :
    TendstoLocallyUniformlyOn (fun t x => t⁻¹ • (F (t,x) - F (0,x)))
      (fun x => partialT F (0,x)) (𝓝[≠] (0:ℝ)) Set.univ := by
  let G : ℝ → C(E,V) := fun t => ⟨fun x => extSlope F (t,x),
    (extSlope_continuous F hF).comp (continuous_const.prodMk continuous_id)⟩
  have hG : Continuous G := ContinuousMap.continuous_of_continuous_uncurry G
    (extSlope_continuous F hF)
  have h : TendstoLocallyUniformlyOn (fun t x => (G t) x) (G 0) (𝓝[≠] (0:ℝ)) Set.univ :=
    (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
      ((hG.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)).tendstoLocallyUniformlyOn
  have heq : (fun t x => (G t) x) =ᶠ[𝓝[≠] (0:ℝ)]
      (fun t x => t⁻¹ • (F (t,x) - F (0,x))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    funext x
    exact extSlope_ne F hF t ht x
  have h' := h.congr_inseparable (heq.mono (fun t ht x _ => Inseparable.of_eq (congrFun ht x)))
  simpa only [G, ContinuousMap.coe_mk, extSlope_zero] using h'
lemma slice_smooth (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => F (t,x)) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

lemma jets_partialT (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [WeaklyLocallyCompactSpace E] (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => partialT F (0,x)) =
      (fun x => partialT (fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2) (0,x)) := by
  induction n with
  | zero =>
    funext x
    let L := (continuousMultilinearCurryFin0 ℝ E V).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hd := L.hasFDerivAt.comp_hasDerivAt 0 (partialT_deriv F hF 0 x)
    simpa [L, partialT, iteratedFDeriv_zero_eq_comp, Function.comp_def] using hd.deriv.symm
  | succ n ih =>
    let J : ℝ × E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) V :=
      fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2
    have hJ : ContDiff ℝ (⊤ : ℕ∞) J := joint_spatial_jets F hF n
    let K : ℝ × E → E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => E) V :=
      fun p => fderiv ℝ (fun x => J (p.1,x)) p.2
    have hK : ContDiff ℝ (⊤ : ℕ∞) K :=
      (hJ.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv contDiff_snd (by simp)
    have hlimK := slope_locally_uniform K hK
    have hlimJ := slope_locally_uniform J hJ
    have hd (x : E) : HasFDerivAt (fun x => partialT J (0,x)) (partialT K (0,x)) x := by
      apply hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hlimK
        (fun t x _ => ?_) (fun x _ => hlimJ.tendsto_at (Set.mem_univ x)) (Set.mem_univ x)
      exact (((slice_smooth J hJ t).differentiable (by simp) x).hasFDerivAt.sub
        ((slice_smooth J hJ 0).differentiable (by simp) x).hasFDerivAt).const_smul t⁻¹
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih]
    change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) V).symm
      (fderiv ℝ (fun x => partialT J (0,x)) x) = _
    rw [(hd x).fderiv]
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) V).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have ht := L.hasFDerivAt.comp_hasDerivAt 0 (partialT_deriv K hK 0 x)
    change L (partialT K (0,x)) = deriv (fun t => L (K (t,x))) 0
    exact ht.deriv.symm
lemma quotient_jets_uniform (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [WeaklyLocallyCompactSpace E] (n : ℕ) (S : Set E) (hS : IsCompact S) :
    TendstoUniformlyOn (fun t x => iteratedFDeriv ℝ n
      (fun x => t⁻¹ • (F (t,x) - F (0,x))) x)
      (iteratedFDeriv ℝ n (fun x => partialT F (0,x))) (𝓝[≠] (0:ℝ)) S := by
  have h := slope_locally_uniform (fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2)
    (joint_spatial_jets F hF n)
  rw [jets_partialT F hF n]
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS).mp
  apply (h.mono (Set.subset_univ S)).congr
  intro t x _
  dsimp only
  symm
  rw [iteratedFDeriv_const_smul_apply' (((slice_smooth F hF t).sub
    (slice_smooth F hF 0)).of_le (by simp)).contDiffAt,
    fun_iteratedFDeriv_sub_apply ((slice_smooth F hF t).of_le (by simp)).contDiffAt
      ((slice_smooth F hF 0).of_le (by simp)).contDiffAt]

lemma sup_jet_error_tendsto (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [WeaklyLocallyCompactSpace E] (n : ℕ) (S : Set E) (hS : IsCompact S) (hne : S.Nonempty) :
    Tendsto (fun t => sSup ((fun x => ‖iteratedFDeriv ℝ n
      (fun x => t⁻¹ • (F (t,x) - F (0,x)) - partialT F (0,x)) x‖) '' S))
      (𝓝[≠] (0:ℝ)) (𝓝 (0:ℝ)) := by
  let Q := fun t x => t⁻¹ • (F (t,x) - F (0,x))
  let P := fun x => partialT F (0,x)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := slice_smooth (partialT F) (partialT_smooth F hF) 0
  have hQ (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Q t) :=
    ((slice_smooth F hF t).sub (slice_smooth F hF 0)).const_smul _
  have hj := quotient_jets_uniform F hF n S hS
  have heq (t : ℝ) (x : E) : iteratedFDeriv ℝ n (fun x => Q t x - P x) x =
      iteratedFDeriv ℝ n (Q t) x - iteratedFDeriv ℝ n P x :=
    iteratedFDeriv_sub_apply ((hQ t).of_le (by simp)).contDiffAt
      (hP.of_le (by simp)).contDiffAt
  have hb (t : ℝ) : BddAbove ((fun x => ‖iteratedFDeriv ℝ n (fun x => Q t x - P x) x‖) '' S) :=
    (hS.image (((hQ t).sub hP).continuous_iteratedFDeriv (by simp)).norm).bddAbove
  apply tendsto_order.2
  constructor
  · intro a ha
    apply Filter.Eventually.of_forall
    intro t
    apply lt_of_lt_of_le ha
    obtain ⟨x,hx⟩ := hne
    exact le_trans (norm_nonneg _) (le_csSup (hb t) ⟨x,hx,rfl⟩)
  · intro b hb'
    have hε : 0 < b / 2 := by linarith
    have hu := (Metric.tendstoUniformlyOn_iff.mp hj) (b / 2) hε
    filter_upwards [hu] with t ht
    apply lt_of_le_of_lt (csSup_le (hne.image _) ?_) (by linarith : b/2 < b)
    rintro _ ⟨x,hx,rfl⟩
    change ‖iteratedFDeriv ℝ n (fun x => Q t x - P x) x‖ ≤ b / 2
    rw [heq]
    exact le_of_lt (by simpa [dist_eq_norm, norm_sub_rev, Q, P] using ht x hx)
end SmoothQuotient

private lemma matrixFunction_gl (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f (g : Matrix (Fin 2) (Fin 2) ℂ) = f g := by
  unfold matrixFunction
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  apply Units.ext
  rfl
private lemma upper_zero : upperUnipotent 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent]
private lemma orbit_open_eq (s : ℝ) (f : PrincipalSeries s) (v : ℂ) (t : ℝ) (x : ℂ) :
    orbitOpenCoordinate s f ((upperUnipotent ((t:ℂ)*v) : Matrix (Fin 2) (Fin 2) ℂ),x) =
    f ((weyl * upperUnipotent x) * upperUnipotent ((t:ℂ)*v)) := by
  unfold orbitOpenCoordinate
  change matrixFunction f (((weyl * upperUnipotent x) * upperUnipotent ((t:ℂ)*v) : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) = _
  exact matrixFunction_gl _ _
private lemma orbit_infinity_eq (s : ℝ) (f : PrincipalSeries s) (v : ℂ) (t : ℝ) (x : ℂ) :
    orbitInfinityCoordinate s f ((upperUnipotent ((t:ℂ)*v) : Matrix (Fin 2) (Fin 2) ℂ),x) =
    f (lowerUnipotent x * upperUnipotent ((t:ℂ)*v)) := by
  unfold orbitInfinityCoordinate
  change matrixFunction f ((lowerUnipotent x * upperUnipotent ((t:ℂ)*v) : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) = _
  exact matrixFunction_gl _ _

theorem upperRoot_differenceQuotient_chartSeminorm_of_pointwise
    (β : ℂˣ) (e : Theta β) (v : ℂ)
    (D : PrincipalSeries negativeParameter)
    (hD : ∀ g : ComplexGL2,
      HasDerivAt (fun t : ℝ => (e : PrincipalSeries negativeParameter)
        (g * upperUnipotent ((t : ℂ) * v))) (D g) 0)
    (n : ℕ) :
    Tendsto (fun t : ℝ => chartSeminorm negativeParameter n
      ((((t⁻¹ : ℂ) •
        (imageAction β (Matrix.ProjGenLinGroup.mk
          (upperUnipotent ((t : ℂ) * v))) e - e) : Theta β) :
          PrincipalSeries negativeParameter) - D))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let F : ℝ × ℂ → ℂ := fun p => orbitOpenCoordinate negativeParameter
    (e : PrincipalSeries negativeParameter) ((upperUnipotent ((p.1:ℂ)*v) : Matrix (Fin 2) (Fin 2) ℂ),p.2)
  let H : ℝ × ℂ → ℂ := fun p => orbitInfinityCoordinate negativeParameter
    (e : PrincipalSeries negativeParameter) ((upperUnipotent ((p.1:ℂ)*v) : Matrix (Fin 2) (Fin 2) ℂ),p.2)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := upperRoot_open_joint_contDiff β e v
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := upperRoot_infinity_joint_contDiff β e v
  have hFD (x : ℂ) : SmoothQuotient.partialT F (0,x) = openCoordinate D x := by
    have hd := hD (weyl * upperUnipotent x)
    have heq : (fun t : ℝ => F (t,x)) = (fun t : ℝ =>
      (e : PrincipalSeries negativeParameter) ((weyl * upperUnipotent x) * upperUnipotent ((t:ℂ)*v))) := by
      funext t; exact orbit_open_eq _ _ _ _ _
    rw [← heq] at hd
    exact hd.deriv
  have hHD (x : ℂ) : SmoothQuotient.partialT H (0,x) = infinityCoordinate D x := by
    have hd := hD (lowerUnipotent x)
    have heq : (fun t : ℝ => H (t,x)) = (fun t : ℝ =>
      (e : PrincipalSeries negativeParameter) (lowerUnipotent x * upperUnipotent ((t:ℂ)*v))) := by
      funext t; exact orbit_infinity_eq _ _ _ _ _
    rw [← heq] at hd
    exact hd.deriv
  let S := Metric.closedBall (0:ℂ) 1
  have hS : IsCompact S := isCompact_closedBall _ _
  have hne : S.Nonempty := ⟨0, Metric.mem_closedBall_self (by norm_num)⟩
  have hf := SmoothQuotient.sup_jet_error_tendsto F hF n S hS hne
  have hh := SmoothQuotient.sup_jet_error_tendsto H hH n S hS hne
  have hmax := hf.max hh
  simp only [max_self] at hmax
  convert hmax using 1
  funext t
  change chartSeminormValue negativeParameter n _ = _
  unfold chartSeminormValue
  congr 2
  · congr 1
    funext x
    congr 2
    funext y
    rw [hFD]
    change (t⁻¹:ℂ) * ((e : PrincipalSeries negativeParameter)
      ((weyl * upperUnipotent y) * upperUnipotent ((t:ℂ)*v)) - (e : PrincipalSeries negativeParameter) (weyl * upperUnipotent y)) - D (weyl * upperUnipotent y) = _
    simp [openCoordinate, F, orbit_open_eq, upper_zero, Complex.real_smul]
  · congr 1
    funext x
    congr 2
    funext y
    rw [hHD]
    change (t⁻¹:ℂ) * ((e : PrincipalSeries negativeParameter)
      (lowerUnipotent y * upperUnipotent ((t:ℂ)*v)) - (e : PrincipalSeries negativeParameter) (lowerUnipotent y)) - D (lowerUnipotent y) = _
    simp [infinityCoordinate, H, orbit_infinity_eq, upper_zero, Complex.real_smul]

end DedekindZetaZeroFree.KPCplxUpperRootSeminormDifferentiation
