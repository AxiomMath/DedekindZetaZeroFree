module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexHarmonicEigenvaluesAndSmoothness

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicPropagation

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace RaisingTopology
private theorem joint_spatial_jets {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
end RaisingTopology

namespace RaisingCalculation
open MvPolynomial
open scoped Matrix Matrix.Norms.Elementwise

noncomputable def transverse : MvPolynomial (Fin 3) ℂ := X 0 + C Complex.I * X 1
theorem transverse_homogeneous (ℓ : ℕ) :
    (transverse ^ ℓ).IsHomogeneous ℓ := by
  simpa [transverse] using ((isHomogeneous_X ℂ (0 : Fin 3)).add
    ((isHomogeneous_X ℂ (1 : Fin 3)).C_mul Complex.I)).pow ℓ
theorem lap_mul_transverse (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (transverse * p) = transverse * polynomialLaplacian p +
      2 * (pderiv 0 p + C Complex.I * pderiv 1 p) := by
  simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    Fin.sum_univ_succ, transverse, pderiv_mul, pderiv_C_mul]
  ring
theorem transverse_direction (ℓ : ℕ) :
    pderiv 0 (transverse ^ ℓ) + C Complex.I * pderiv 1 (transverse ^ ℓ) = 0 := by
  simp only [pderiv_pow]
  simp [transverse, pderiv_C_mul, Pi.single_apply]
  have hI : (C Complex.I : MvPolynomial (Fin 3) ℂ) ^ 2 = -1 := by
    rw [← map_pow]; norm_num
  linear_combination (ℓ : MvPolynomial (Fin 3) ℂ) *
    (X 0 + C Complex.I * X 1) ^ (ℓ - 1) * hI
theorem transverse_harmonic (ℓ : ℕ) : transverse ^ ℓ ∈ harmonicPolynomials ℓ := by
  refine ⟨transverse_homogeneous ℓ, ?_⟩
  change polynomialLaplacian (transverse ^ ℓ) = 0
  induction ℓ with
  | zero => simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply]
  | succ n ih =>
    rw [pow_succ', lap_mul_transverse, ih, transverse_direction]
    simp
theorem lap_mul_height (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (X 2 * p) = X 2 * polynomialLaplacian p + 2 * pderiv 2 p := by
  simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    Fin.sum_univ_succ, pderiv_mul]
  ring
theorem height_transverse_harmonic (ℓ : ℕ) :
    X 2 * transverse ^ ℓ ∈ harmonicPolynomials (ℓ + 1) := by
  constructor
  · simpa [Nat.add_comm] using (isHomogeneous_X ℂ (2 : Fin 3)).mul (transverse_homogeneous ℓ)
  · change polynomialLaplacian (X 2 * transverse ^ ℓ) = 0
    rw [lap_mul_height, (transverse_harmonic ℓ).2]
    simp [pderiv_pow, transverse, pderiv_C_mul, Pi.single_apply]

noncomputable def rowB (m : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2
noncomputable def rowW (m : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 2 * m 1 0 * star (m 1 1) / (rowB m : ℂ)
theorem rowB_pos (g : ComplexGL2) : 0 < rowB g :=
  KPCplxRotatedKernelEstimates.bottomRowNormSq_pos g
theorem rowW_smooth : ContDiffOn ℝ (⊤ : ℕ∞) rowW {m | m.det ≠ 0} := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 1 0) := by fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 1 1) := by fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) rowB := (h0.norm_sq (𝕜 := ℂ)).add (h1.norm_sq (𝕜 := ℂ))
  unfold rowW
  simp only [div_eq_mul_inv]
  apply ContDiffOn.mul
  · exact ((contDiff_const.mul h0).mul (Complex.conjCLE.contDiff.comp h1)).contDiffOn
  · apply ContDiffOn.inv (Complex.ofRealCLM.contDiff.comp hb |>.contDiffOn)
    intro m hm
    exact Complex.ofReal_ne_zero.mpr (rowB_pos (Matrix.GeneralLinearGroup.mkOfDetNeZero m hm)).ne'
theorem rowW_left (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    rowW (upperTriangular a d b * g) = rowW g := by
  have hup : (upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) = !![(a : ℂ), b; 0, (d : ℂ)] := rfl
  have he : rowB (upperTriangular a d b * g) = ‖(d : ℂ)‖ ^ 2 * rowB g := by
    change rowB ((upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)) = _
    rw [hup]
    simp [rowB, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow, mul_add]
  unfold rowW
  rw [he]
  change 2 * ((!![(a : ℂ), b; 0, (d : ℂ)] * (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 0) *
    star ((!![(a : ℂ), b; 0, (d : ℂ)] * (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 1) /
    (‖(d : ℂ)‖ ^ 2 * rowB g : ℝ) = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  change 2 * ((0 : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (d : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) *
    star ((0 : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + (d : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) / _ = _
  simp only [zero_mul, zero_add, star_mul]
  rw [show 2 * ((d : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * (star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * star (d : ℂ)) =
    ((d : ℂ) * star (d : ℂ)) * (2 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) by ring]
  simp only [Complex.star_def, Complex.mul_conj']
  push_cast
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr d.ne_zero)))
noncomputable def harmonicFunction (s : ℝ) (ℓ : ℕ) (g : ComplexGL2) : ℂ :=
  sphericalSection s g * rowW g ^ ℓ
theorem harmonicFunction_mem (s : ℝ) (ℓ : ℕ) :
    harmonicFunction s ℓ ∈ principalSeriesSubmodule s := by
  apply (principalSeries_mem_iff s _).mpr
  constructor
  · intro a d b g
    have hc := (sphericalSection s).property.1 a d b g
    unfold harmonicFunction
    rw [hc]
    change _ * _ * rowW ((upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)) ^ ℓ = _
    rw [rowW_left]
    ring
  · have hs := ((principalSeries_mem_iff s _).mp (sphericalSection s).property).2
    have hh := hs.mul (rowW_smooth.pow ℓ)
    apply hh.congr
    intro m hm
    change m.det ≠ 0 at hm
    simp only [matrixFunction, dif_pos hm, harmonicFunction]
    rfl
noncomputable def harmonicSection (s : ℝ) (ℓ : ℕ) : PrincipalSeries s :=
  ⟨harmonicFunction s ℓ, harmonicFunction_mem s ℓ⟩

noncomputable def rowZ (m : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ((‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2 : ℝ) : ℂ) / (rowB m : ℂ)
theorem rowB_compact (k : ComplexSU2) : rowB k = 1 := by
  have hrow := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => (B 1 1).re)
    (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply_eq] at hrow
  change (((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (starRingEnd ℂ) ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) +
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (starRingEnd ℂ) ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1))).re = 1 at hrow
  simpa only [rowB, Complex.mul_conj', Complex.add_re, ← Complex.ofReal_pow,
    Complex.ofReal_re] using hrow
theorem spherical_compact (s : ℝ) (k : ComplexSU2) :
    sphericalSection s (complexSU2Embedding k) = 1 := by
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  change (Real.rpow (‖(k : Matrix (Fin 2) (Fin 2) ℂ).det‖ / rowB k) (1 + 2 * s) : ℂ) = 1
  rw [hd, rowB_compact]; simp
theorem rowW_compact (k : ComplexSU2) :
    rowW k = compactSphereCoordinate k 0 + Complex.I * compactSphereCoordinate k 1 := by
  simp only [rowW, rowB_compact, Complex.ofReal_one, div_one, compactSphereCoordinate,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hr := Complex.re_add_im ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1))
  push_cast
  linear_combination 2 * hr.symm
theorem rowZ_compact (k : ComplexSU2) : rowZ k = compactSphereCoordinate k 2 := by
  simp [rowZ, rowB_compact, compactSphereCoordinate]

theorem harmonicSection_compact (s : ℝ) (ℓ : ℕ) :
    compactRestriction s (harmonicSection s ℓ) = polynomialCompactRestriction (transverse ^ ℓ) := by
  ext k
  change sphericalSection s (complexSU2Embedding k) * rowW k ^ ℓ =
    MvPolynomial.eval (compactSphereCoordinate k) (transverse ^ ℓ)
  rw [spherical_compact, rowW_compact]
  simp [transverse]

theorem harmonicSection_harmonic (s : ℝ) (ℓ : ℕ) :
    harmonicSection s ℓ ∈ harmonicKType s ℓ := by
  exact ⟨transverse ^ ℓ, transverse_harmonic ℓ, (harmonicSection_compact s ℓ).symm⟩

theorem height_harmonic_of_formula (s : ℝ) (ℓ : ℕ) (c : ℂ)
    (v : PrincipalSeries s)
    (hv : ∀ g, v g = c * rowZ g * harmonicSection s ℓ g) :
    v ∈ harmonicKType s (ℓ + 1) := by
  refine ⟨c • (X 2 * transverse ^ ℓ),
    (harmonicPolynomials (ℓ + 1)).smul_mem c (height_transverse_harmonic ℓ), ?_⟩
  ext k
  change MvPolynomial.eval (compactSphereCoordinate k) (c • (X 2 * transverse ^ ℓ)) =
    v (complexSU2Embedding k)
  rw [hv]
  change _ = c * rowZ k * (sphericalSection s (complexSU2Embedding k) * rowW k ^ ℓ)
  rw [spherical_compact, rowZ_compact, rowW_compact]
  simp [transverse, mul_assoc]

theorem height_ne_zero_of_formula (s : ℝ) (ℓ : ℕ) (c : ℂ) (hc : c ≠ 0)
    (v : PrincipalSeries s)
    (hv : ∀ g, v g = c * rowZ g * harmonicSection s ℓ g) : v ≠ 0 := by
  let g : ComplexGL2 := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 2] (by
    norm_num [Matrix.det_fin_two])
  have hZ : rowZ g = -(3 / 5 : ℂ) := by
    norm_num [rowZ, rowB, g]
  have hW : rowW g = (4 / 5 : ℂ) := by
    norm_num [rowW, rowB, g]
  have hS : sphericalSection s g ≠ 0 := by
    change (Real.rpow _ (1 + 2 * s) : ℂ) ≠ 0
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    apply Real.rpow_pos_of_pos
    apply div_pos
    · exact norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
    · exact rowB_pos g
  intro he
  have hz := congrArg (fun f : PrincipalSeries s => f g) he
  change v g = 0 at hz
  rw [hv] at hz
  change c * rowZ g * (sphericalSection s g * rowW g ^ ℓ) = 0 at hz
  rw [hZ, hW] at hz
  exact (mul_ne_zero (mul_ne_zero hc (by norm_num))
    (mul_ne_zero hS (pow_ne_zero ℓ (by norm_num)))) hz

noncomputable def boostUnit (t : ℝ) : ℂˣ := Units.mk0 (Real.exp t : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t))
noncomputable def boost (t : ℝ) : ComplexGL2 := diagonal (boostUnit t)

theorem boost_zero : boost 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boost, diagonal, boostUnit, Matrix.one_apply]
theorem boost_bottom (g : ComplexGL2) (t : ℝ) :
    rowB (g * boost t) = ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 * Real.exp t ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
  have hb : (boost t : Matrix (Fin 2) (Fin 2) ℂ) = !![(Real.exp t : ℂ), 0; 0, 1] := rfl
  change rowB ((g : Matrix (Fin 2) (Fin 2) ℂ) * (boost t : Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [hb]
  simp [rowB, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow, le_of_lt (Real.exp_pos t)]
theorem boost_transverse (g : ComplexGL2) (t : ℝ) :
    rowW (g * boost t) =
      (2 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) * (Real.exp t : ℂ) / (rowB (g * boost t) : ℂ) := by
  have hb : (boost t : Matrix (Fin 2) (Fin 2) ℂ) = !![(Real.exp t : ℂ), 0; 0, 1] := rfl
  unfold rowW
  change 2 * (((g : Matrix (Fin 2) (Fin 2) ℂ) * (boost t : Matrix (Fin 2) (Fin 2) ℂ)) 1 0) *
    star (((g : Matrix (Fin 2) (Fin 2) ℂ) * (boost t : Matrix (Fin 2) (Fin 2) ℂ)) 1 1) / _ = _
  rw [hb]
  simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, mul_comm, mul_left_comm]
theorem boost_det_norm (g : ComplexGL2) (t : ℝ) :
    ‖((Matrix.GeneralLinearGroup.det (g * boost t) : ℂˣ) : ℂ)‖ =
      ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ * Real.exp t := by
  simp [map_mul, boost, diagonal, boostUnit, Matrix.det_fin_two, norm_mul, le_of_lt (Real.exp_pos t)]
theorem boost_bottom_hasDerivAt (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => rowB (g * boost t)) (2 * ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2) 0 := by
  simp_rw [boost_bottom]
  convert ((Real.hasDerivAt_exp (0 : ℝ)).pow 2).const_mul (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2) |>.add_const
    (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) using 1 <;> simp <;> ring
theorem boost_transverse_hasDerivAt (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => rowW (g * boost t)) (-rowZ g * rowW g) 0 := by
  let A := ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2
  let B := rowB g
  let W := 2 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
  have hB : B ≠ 0 := (rowB_pos g).ne'
  have hh := ((Real.hasDerivAt_exp (0 : ℝ)).ofReal_comp.const_mul W).div
    (boost_bottom_hasDerivAt g).ofReal_comp (by simpa [boost_zero] using Complex.ofReal_ne_zero.mpr hB)
  simp only [Real.exp_zero, Complex.ofReal_one, mul_one, boost_zero, mul_one] at hh
  simp_rw [boost_transverse]
  convert hh using 1
  dsimp [rowZ, rowW, W, B, A, rowB]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hB]
  ring

theorem boost_spherical_hasDerivAt (s : ℝ) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => sphericalSection s (g * boost t))
      (-((1 + 2 * s : ℝ) : ℂ) * rowZ g * sphericalSection s g) 0 := by
  let a := ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖
  let B := rowB g
  let A := ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2
  let e := 1 + 2 * s
  have ha : 0 < a := norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
  have hB : 0 < B := rowB_pos g
  have hz : rowB (g * boost 0) = B := by simp [boost_zero, B]
  have hq := ((Real.hasDerivAt_exp (0 : ℝ)).const_mul a).div
    (boost_bottom_hasDerivAt g) (by rw [hz]; exact hB.ne')
  have hp := hq.rpow_const (p := e) (Or.inl (by change a * Real.exp 0 / rowB (g * boost 0) ≠ 0; rw [hz]; positivity))
  have hh := hp.ofReal_comp
  have he : (fun t : ℝ => sphericalSection s (g * boost t)) =
      fun t : ℝ => (((a * Real.exp t / rowB (g * boost t)) ^ e : ℝ) : ℂ) := by
    funext t
    change (Real.rpow _ _ : ℂ) = _
    rw [boost_det_norm]
    rfl
  rw [he]
  convert hh using 1
  simp only [Real.exp_zero, mul_one, hz, Pi.div_apply]
  change -((e : ℝ) : ℂ) * rowZ g * ((a / B) ^ e : ℝ) = _
  have hepow : (a / B) ^ e = (a / B) ^ (e - 1) * (a / B) := by
    conv_rhs => rhs; rw [← Real.rpow_one (a / B)]
    rw [← Real.rpow_add (div_pos ha hB)]
    congr 1; ring
  rw [hepow]
  dsimp [rowZ, B, A, rowB]
  push_cast
  field_simp
  ring

theorem harmonic_boost_hasDerivAt (s : ℝ) (ℓ : ℕ) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => harmonicSection s ℓ (g * boost t))
      (-(((ℓ : ℝ) + 1 + 2 * s : ℝ) : ℂ) * rowZ g * harmonicSection s ℓ g) 0 := by
  have hh := (boost_spherical_hasDerivAt s g).mul ((boost_transverse_hasDerivAt g).pow ℓ)
  simp only [boost_zero, mul_one] at hh
  change HasDerivAt (fun t : ℝ => sphericalSection s (g * boost t) * rowW (g * boost t) ^ ℓ) _ 0
  convert hh using 1
  change -(((ℓ : ℝ) + 1 + 2 * s : ℝ) : ℂ) * rowZ g *
    (sphericalSection s g * rowW g ^ ℓ) = _
  push_cast
  cases ℓ with
  | zero => simp
  | succ n =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.pow_apply,
      boost_zero, Units.val_one, Matrix.mul_one, pow_succ]
    ring
theorem rowZ_smooth : ContDiffOn ℝ (⊤ : ℕ∞) rowZ {m | m.det ≠ 0} := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 1 0) := by fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 1 1) := by fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) rowB := (h0.norm_sq (𝕜 := ℂ)).add (h1.norm_sq (𝕜 := ℂ))
  unfold rowZ
  simp only [div_eq_mul_inv]
  apply ContDiffOn.mul
  · exact (Complex.ofRealCLM.contDiff.comp ((h0.norm_sq (𝕜 := ℂ)).sub (h1.norm_sq (𝕜 := ℂ)))).contDiffOn
  · apply ContDiffOn.inv (Complex.ofRealCLM.contDiff.comp hb).contDiffOn
    intro m hm
    exact Complex.ofReal_ne_zero.mpr (rowB_pos (Matrix.GeneralLinearGroup.mkOfDetNeZero m hm)).ne'

theorem rowZ_left (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    rowZ (upperTriangular a d b * g) = rowZ g := by
  have hup : (upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) = !![(a : ℂ), b; 0, (d : ℂ)] := rfl
  change rowZ ((upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [hup]
  simp [rowZ, rowB, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow]
  push_cast
  have hd : (‖(d : ℂ)‖ ^ 2 : ℂ) ≠ 0 := by
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr d.ne_zero))
  rw [← mul_sub, ← mul_add, mul_div_mul_left _ _ hd]

noncomputable def raisedSection (s : ℝ) (ℓ : ℕ) : PrincipalSeries s :=
  ⟨fun g => -(((ℓ : ℂ) + 1 + 2 * (s : ℂ))) * rowZ g * harmonicSection s ℓ g, by
    apply (principalSeries_mem_iff s _).mpr
    constructor
    · intro a d b g
      dsimp only
      rw [Matrix.GeneralLinearGroup.coe_mul, rowZ_left,
        (harmonicSection s ℓ).property.1]
      ring
    · have hs := ((principalSeries_mem_iff s _).mp (harmonicSection s ℓ).property).2
      have hh := ((contDiffOn_const (c := -((ℓ : ℂ) + 1 + 2 * (s : ℂ)))).mul rowZ_smooth).mul hs
      apply hh.congr
      intro m hm
      change m.det ≠ 0 at hm
      simp only [matrixFunction, dif_pos hm]
      rfl⟩

end RaisingCalculation

private theorem matrixFunction_gl (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f (g : Matrix (Fin 2) (Fin 2) ℂ) = f g := by
  unfold matrixFunction
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  apply Units.ext
  rfl

set_option maxHeartbeats 1500000 in
private theorem boost_quotient_tendsto (s : ℝ) (u D : PrincipalSeries s)
    (hd : ∀ g : ComplexGL2, HasDerivAt (fun t : ℝ => u (g * RaisingCalculation.boost t)) (D g) 0) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (rightTranslate s (RaisingCalculation.boost t) u - u))
      (𝓝[≠] (0 : ℝ)) (𝓝 D) := by
  let F : ℝ × ℂ → ℂ := fun p => u (weyl * upperUnipotent p.2 * RaisingCalculation.boost p.1)
  let H : ℝ × ℂ → ℂ := fun p => u (lowerUnipotent p.2 * RaisingCalculation.boost p.1)
  have hs := ((principalSeries_mem_iff s (u : ComplexGL2 → ℂ)).mp u.property).2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    let M : ℝ × ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun p =>
      (weyl * upperUnipotent p.2 * RaisingCalculation.boost p.1 : ComplexGL2)
    have he : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℂ => (Real.exp p.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_fst)
    have hM : ContDiff ℝ (⊤ : ℕ∞) M := by
      apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro j
      fin_cases i <;> fin_cases j <;>
        simp [-Complex.ofReal_exp, M, RaisingCalculation.boost, RaisingCalculation.boostUnit, diagonal,
          weyl, upperUnipotent, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop (disch := assumption)
    have h := hs.comp_contDiff hM (fun p => Matrix.GeneralLinearGroup.det_ne_zero _)
    convert h using 1
    funext p
    exact (matrixFunction_gl u _).symm
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := by
    let M : ℝ × ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun p =>
      (lowerUnipotent p.2 * RaisingCalculation.boost p.1 : ComplexGL2)
    have he : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℂ => (Real.exp p.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_fst)
    have hM : ContDiff ℝ (⊤ : ℕ∞) M := by
      apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro j
      fin_cases i <;> fin_cases j <;>
        simp [-Complex.ofReal_exp, M, RaisingCalculation.boost, RaisingCalculation.boostUnit, diagonal,
          lowerUnipotent, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop (disch := assumption)
    have h := hs.comp_contDiff hM (fun p => Matrix.GeneralLinearGroup.det_ne_zero _)
    convert h using 1
    funext p
    exact (matrixFunction_gl u _).symm
  have hPF : (fun x => RaisingTopology.SmoothQuotient.partialT F (0,x)) = openCoordinate D := by
    funext x
    exact (RaisingTopology.SmoothQuotient.partialT_deriv F hF 0 x).unique (hd (weyl * upperUnipotent x))
  have hPH : (fun x => RaisingTopology.SmoothQuotient.partialT H (0,x)) = infinityCoordinate D := by
    funext x
    exact (RaisingTopology.SmoothQuotient.partialT_deriv H hH 0 x).unique (hd (lowerUnipotent x))
  have hzero : ∀ x, F (0,x) = openCoordinate u x ∧ H (0,x) = infinityCoordinate u x := by
    intro x
    simp [F, H, RaisingCalculation.boost_zero, openCoordinate, infinityCoordinate]
  have ht : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  rw [ht.tendsto_nhds]
  intro n ε hε
  have hS : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : ℂ) 1).Nonempty := ⟨0, by simp⟩
  have hf := RaisingTopology.SmoothQuotient.sup_jet_error_tendsto F hF n _ hS hne
  have hh := RaisingTopology.SmoothQuotient.sup_jet_error_tendsto H hH n _ hS hne
  simp only [show ∀ x, RaisingTopology.SmoothQuotient.partialT F (0,x) = openCoordinate D x
    from fun x => congrFun hPF x] at hf
  simp only [show ∀ x, RaisingTopology.SmoothQuotient.partialT H (0,x) = infinityCoordinate D x
    from fun x => congrFun hPH x] at hh
  have heF (t : ℝ) : openCoordinate ((t⁻¹ : ℂ) • (rightTranslate s (RaisingCalculation.boost t) u - u) - D) =
      fun x => t⁻¹ • (F (t,x) - F (0,x)) - openCoordinate D x := by
    funext x
    simp only [openCoordinate, Submodule.coe_sub, Submodule.coe_smul_of_tower, Pi.sub_apply, Pi.smul_apply]
    rw [(hzero x).1]
    simp [F, rightTranslate, openCoordinate, Complex.real_smul, Complex.ofReal_inv]
  have heH (t : ℝ) : infinityCoordinate ((t⁻¹ : ℂ) • (rightTranslate s (RaisingCalculation.boost t) u - u) - D) =
      fun x => t⁻¹ • (H (t,x) - H (0,x)) - infinityCoordinate D x := by
    funext x
    simp only [infinityCoordinate, Submodule.coe_sub, Submodule.coe_smul_of_tower, Pi.sub_apply, Pi.smul_apply]
    rw [(hzero x).2]
    simp [H, rightTranslate, infinityCoordinate, Complex.real_smul, Complex.ofReal_inv]
  have hlim : Tendsto (fun t : ℝ => chartSeminorm s n
      ((t⁻¹ : ℂ) • (rightTranslate s (RaisingCalculation.boost t) u - u) - D))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    change Tendsto (fun t => max (sSup ((fun x => ‖iteratedFDeriv ℝ n (openCoordinate _) x‖)
      '' Metric.closedBall (0 : ℂ) 1)) (sSup ((fun x => ‖iteratedFDeriv ℝ n (infinityCoordinate _) x‖)
      '' Metric.closedBall (0 : ℂ) 1))) _ _
    simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, heF, heH]
    convert hf.max hh using 1 <;> simp
  exact (tendsto_order.mp hlim).2 ε hε

theorem nonzero_adjacent_raising (s : ℝ) (n : ℕ)
    (hcoeff : ((n : ℂ) + 1 + 2 * (s : ℂ)) ≠ 0)
    (U : Submodule ℂ (PrincipalSeries s))
    (hclosed : IsClosed (U : Set (PrincipalSeries s)))
    (hinv : ∀ (g : ComplexPGL2) (f : PrincipalSeries s), f ∈ U → pi s g f ∈ U)
    (hn : harmonicKType s n ≤ U) :
    ∃ v : PrincipalSeries s, v ∈ U ∧ v ∈ harmonicKType s (n + 1) ∧ v ≠ 0 := by
  let u := RaisingCalculation.harmonicSection s n
  let v := RaisingCalculation.raisedSection s n
  have hv (g : ComplexGL2) : v g = -((n : ℂ) + 1 + 2 * (s : ℂ)) *
      RaisingCalculation.rowZ g * RaisingCalculation.harmonicSection s n g := rfl
  have hder (g : ComplexGL2) : HasDerivAt (fun t : ℝ => u (g * RaisingCalculation.boost t)) (v g) 0 := by
    convert RaisingCalculation.harmonic_boost_hasDerivAt s n g using 1 <;> push_cast
    rfl
  have hu : u ∈ U := hn (RaisingCalculation.harmonicSection_harmonic s n)
  have hlim := boost_quotient_tendsto s u v hder
  have hmem : ∀ t : ℝ, (t⁻¹ : ℂ) • (rightTranslate s (RaisingCalculation.boost t) u - u) ∈ U := by
    intro t
    apply U.smul_mem
    apply U.sub_mem _ hu
    simpa only [pi_mk] using hinv (Matrix.ProjGenLinGroup.mk (RaisingCalculation.boost t)) u hu
  have hvU : v ∈ U := hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  exact ⟨v, hvU, RaisingCalculation.height_harmonic_of_formula s n _ v hv,
    RaisingCalculation.height_ne_zero_of_formula s n _ (neg_ne_zero.mpr hcoeff) v hv⟩

end DedekindZetaZeroFree.KPCplxHarmonicPropagation
