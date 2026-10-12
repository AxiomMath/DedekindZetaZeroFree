module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormOneFourierSheetEstimates

@[expose] public section

namespace DedekindZetaZeroFree.ProbeLogarithmicRowCoefficients
noncomputable section
open scoped Classical
set_option maxHeartbeats 1000000
open scoped NumberField
open NumberField IsDedekindDomain

def logRow {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (u : ℝ) (y : SLocalProduct F A.Sf) : ℂ :=
  ((Real.exp u) ^ (-(1 / 2 : ℝ)) : ℝ) * (W1 (Real.exp u) : ℂ) *
    W0 (y * (ProbeSheet.ell A (Real.exp u))⁻¹.val)

private lemma uniform_slices {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ × E → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) H) (hc : HasCompactSupport H) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u z,
      ‖H (u,z)‖ + ‖iteratedDeriv 2 (fun t => H (t,z)) u‖ ≤ B := by
  let v : ℝ × E := (1,0)
  let g : ℝ × E → ℂ := fun p => fderiv ℝ H p v
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g :=
    (hs.fderiv_right (by simp)).clm_apply contDiff_const
  have hgc : HasCompactSupport g := (hc.fderiv ℝ).comp_left (g := fun L : (ℝ × E) →L[ℝ] ℂ => L v) (by simp)
  let d : ℝ × E → ℂ := fun p => fderiv ℝ g p v
  have hds : ContDiff ℝ (⊤ : ℕ∞) d :=
    (hgs.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc : HasCompactSupport d := (hgc.fderiv ℝ).comp_left (g := fun L : (ℝ × E) →L[ℝ] ℂ => L v) (by simp)
  have hder (z : E) : deriv (fun t => H (t,z)) = fun t => g (t,z) := by
    funext t
    have hv : HasDerivAt (fun t : ℝ => (t,z)) v t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
    exact ((hs.differentiable (by simp) (t,z)).hasFDerivAt.comp_hasDerivAt t hv).deriv
  have hdder (z : E) : deriv (fun t => g (t,z)) = fun t => d (t,z) := by
    funext t
    have hv : HasDerivAt (fun t : ℝ => (t,z)) v t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
    exact ((hgs.differentiable (by simp) (t,z)).hasFDerivAt.comp_hasDerivAt t hv).deriv
  obtain ⟨B, hB⟩ := hs.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  obtain ⟨D, hD⟩ := hds.continuous.norm.bddAbove_range_of_hasCompactSupport hdc.norm
  refine ⟨max B 0 + max D 0, by positivity, ?_⟩
  intro u z
  simp only [show (2 : ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero, hder, hdder]
  exact add_le_add ((hB (Set.mem_range_self _)).trans (le_max_left _ _))
    ((hD (Set.mem_range_self _)).trans (le_max_left _ _))

 def archRow {I : Type*} [Fintype I] (W : ProbeRealAnnularWeight)
    (f : I → ℂ → ℂ) (c : ℝ) (p : ℝ × (I → ℂ)) : ℂ :=
  (Real.exp (-p.1 / 2) : ℂ) * (W (Real.exp p.1) : ℂ) *
    ∏ i, f i (p.2 i * (Real.exp (-p.1 / c) : ℂ))

private lemma arch_smooth {I : Type*} [Fintype I] (W : ProbeRealAnnularWeight)
    (f : I → ℂ → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (archRow W f c) := by
  apply ContDiff.mul
  · exact (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_fst.neg.div_const 2))).mul
      (Complex.ofRealCLM.contDiff.comp (W.smooth.comp (Real.contDiff_exp.comp contDiff_fst)))
  · apply contDiff_prod
    intro i hi
    exact (hf i).comp (((contDiff_pi.mp contDiff_id i).comp contDiff_snd).mul
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_fst.neg.div_const c))))

private lemma arch_compact {I : Type*} [Fintype I] (W : ProbeRealAnnularWeight)
    (f : I → ℂ → ℂ) (hf : ∀ i, HasCompactSupport (f i)) (c : ℝ) :
    HasCompactSupport (archRow W f c) := by
  let K : Set ℝ := Real.log '' tsupport W
  have hK : IsCompact K := W.compactSupport.image_of_continuousOn
    (Real.continuousOn_log.mono (fun x hx => (W.support_positive hx).ne'))
  let Z : Set (I → ℂ) := Set.pi Set.univ (fun i => tsupport (f i))
  have hZ : IsCompact Z := isCompact_univ_pi hf
  let T : ℝ × (I → ℂ) → ℝ × (I → ℂ) :=
    fun p => (p.1, fun i => p.2 i * (Real.exp (p.1 / c) : ℂ))
  have hT : Continuous T := by fun_prop
  have hC : IsCompact (T '' (K ×ˢ Z)) := (hK.prod hZ).image hT
  apply hC.of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ hC.isClosed)
  intro p hp
  have hn : archRow W f c p ≠ 0 := hp
  have hw : W (Real.exp p.1) ≠ 0 := by
    intro hw
    apply hn
    simp [archRow, hw]
  have hz : ∀ i, f i (p.2 i * (Real.exp (-p.1 / c) : ℂ)) ≠ 0 := by
    have hp' : (∏ i, f i (p.2 i * (Real.exp (-p.1 / c) : ℂ))) ≠ 0 := by
      intro he
      exact hn (by unfold archRow; rw [he, mul_zero])
    exact fun i => (Finset.prod_ne_zero_iff.mp hp') i (Finset.mem_univ i)
  refine ⟨(p.1, fun i => p.2 i * (Real.exp (-p.1 / c) : ℂ)), ?_, ?_⟩
  · exact ⟨⟨Real.exp p.1, subset_tsupport _ hw, Real.log_exp _⟩,
      fun i hi => subset_tsupport _ (hz i)⟩
  · dsimp [T]
    congr 1
    funext i
    rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp [show -p.1 / c + p.1 / c = 0 by ring]

private theorem row_coordinate {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
    (u : ℝ) (y : SLocalProduct F A.Sf) (w : {v : InfinitePlace F // v.IsComplex}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (y * (ProbeSheet.ell A (Real.exp u))⁻¹.val).1).2 w =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F y.1).2 w *
        (Real.exp (-u / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℂ) := by
  simp only [ProbeSheet.ell, dif_pos (Real.exp_pos u)]
  change InfinitePlace.Completion.extensionEmbedding w.1
    (y.1 w.1 * (((A.radialSection (Real.exp u) (Real.exp_pos u)).1 w.1)⁻¹).val) = _
  rw [map_mul]
  congr 1
  have hh : (A.radialSection (Real.exp u) (Real.exp_pos u)).1 w.1 =
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2).symm.toMonoidHom
        (Units.mk0 ((Real.exp u ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℝ) : ℂ)
          (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Real.exp_pos u) _).ne')) := by rfl
  rw [hh]
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2)
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2).symm
      (((Real.exp u ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℝ) : ℂ)⁻¹)) = _
  rw [RingEquiv.apply_symm_apply, ← Complex.ofReal_inv, ← Real.exp_mul, ← Real.exp_neg]
  congr 2
  ring

theorem uniform_log_derivatives {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x}) :
    (∀ y, ContDiff ℝ (2 : ℕ∞) (fun u => logRow A W0 W1 u y)) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u y,
      ‖logRow A W0 W1 u y‖ +
        ‖iteratedDeriv 2 (fun t => logRow A W0 W1 t y) u‖ ≤ B := by
  obtain ⟨fr, fc, ff, hr, hc, hf, heq⟩ := hW0
  have hreal : IsEmpty {v : InfinitePlace F // v.IsReal} := by
    refine ⟨fun v => ?_⟩
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place v.1)) v.2
  letI := hreal
  let c : ℝ := 2 * (InfinitePlace.nrComplexPlaces F : ℝ)
  let z : SLocalProduct F A.Sf → ({v : InfinitePlace F // v.IsComplex} → ℂ) :=
    fun y => (InfiniteAdeleRing.ringEquiv_mixedSpace F y.1).2
  let fin : SLocalProduct F A.Sf → ℂ := fun y => ∏ v : ↥A.Sf, ff v (y.2 v)
  have hformula (y : SLocalProduct F A.Sf) : (fun u => logRow A W0 W1 u y) =
      fun u => archRow W1 fc c (u, z y) * fin y := by
    funext u
    rw [logRow, heq]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, row_coordinate]
    have hfinite : (y * (ProbeSheet.ell A (Real.exp u))⁻¹.val).2 = y.2 := by
      funext v
      simp only [ProbeSheet.ell, dif_pos (Real.exp_pos u)]
      change y.2 v * (((A.radialSection (Real.exp u) (Real.exp_pos u)).2 v)⁻¹).val = y.2 v
      simp [SArithmeticData.radialSection]
    rw [hfinite, ← Real.exp_mul]
    rw [show u * (-(1 / 2 : ℝ)) = -u / 2 by ring]
    dsimp [archRow, c, z, fin]
    ring
  have has : ContDiff ℝ (⊤ : ℕ∞) (archRow W1 fc c) :=
    arch_smooth W1 fc (fun i => (hc i).1) c
  have hs (y : SLocalProduct F A.Sf) :
      ContDiff ℝ (⊤ : ℕ∞) (fun u => archRow W1 fc c (u,z y)) :=
    has.comp (contDiff_id.prodMk contDiff_const)
  refine ⟨fun y => ?_, ?_⟩
  · rw [hformula y]
    exact ((hs y).mul contDiff_const).of_le (by simp)
  · obtain ⟨B, hB, hb⟩ := uniform_slices (archRow W1 fc c) has
      (arch_compact W1 fc (fun i => (hc i).2.1) c)
    have hfb (v : ↥A.Sf) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖ff v x‖ ≤ D := by
      obtain ⟨D, hD⟩ := (hf v).1.continuous.norm.bddAbove_range_of_hasCompactSupport
        (hf v).2.1.norm
      exact ⟨max D 0, le_max_right _ _,
        fun x => (hD (Set.mem_range_self x)).trans (le_max_left _ _)⟩
    choose D hD hd using hfb
    let M : ℝ := ∏ v : ↥A.Sf, D v
    have hM : 0 ≤ M := Finset.prod_nonneg (fun v hv => hD v)
    have hm (y : SLocalProduct F A.Sf) : ‖fin y‖ ≤ M := by
      dsimp [fin, M]
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun v hv => norm_nonneg _) (fun v hv => hd v _)
    refine ⟨B * M, mul_nonneg hB hM, ?_⟩
    intro u y
    rw [hformula y, congrFun (hformula y) u, iteratedDeriv_mul_const_field]
    rw [norm_mul, norm_mul, ← add_mul]
    exact mul_le_mul (hb u (z y)) (hm y) (norm_nonneg _) hB

end
end DedekindZetaZeroFree.ProbeLogarithmicRowCoefficients
