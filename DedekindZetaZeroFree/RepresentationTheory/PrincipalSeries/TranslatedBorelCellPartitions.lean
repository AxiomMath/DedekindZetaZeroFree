module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.ArithmeticInducingData

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPActualResidueSources

open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneOpenCellKernel
open KPActualScalarBinding

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable (S : ActualKPBinding F ζ hζ q)

open KPJacquetBruhatCharts KPLocalSmoothRepresentation

 abbrev K := LocalField F q
 abbrev G := Cover F ζ hζ q
 abbrev O : Set (K F q) := {s | valuation (K F q) s ≤ 1}
 abbrev M : Set (K F q) := {s | valuation (K F q) s < 1}
 def E0 : Set (G F ζ hζ q) :=
  {x | ∃ h : x ∈ omega F ζ hζ q, omegaCoordinate F ζ hζ q ⟨x,h⟩ ∈ O F q}
 def E1 : Set (G F ζ hζ q) :=
  {x | ∃ h : x ∈ delta F ζ hζ q, deltaCoordinate F ζ hζ q ⟨x,h⟩ ∈ M F q}

private theorem M_clopen : IsClopen (M F q) := by
  have hM : IsOpen (M F q) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨1, ?_⟩
    rintro y ⟨t,ht,rfl⟩
    change valuation (K F q) (x + t) < 1
    exact (valuation (K F q)).map_add x t |>.trans_lt (max_lt hx ht)
  exact ⟨AddSubgroup.isClosed_of_isOpen
    (Valuation.ltAddSubgroup (valuation (K F q)) 1) hM, hM⟩
private theorem O_clopen : IsClopen (O F q) := by
  have hO : IsOpen (O F q) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨1, ?_⟩
    rintro y ⟨t,ht,rfl⟩
    change valuation (K F q) (x + t) ≤ 1
    exact (valuation (K F q)).map_add x t |>.trans (max_le hx ht.le)
  exact ⟨AddSubgroup.isClosed_of_isOpen
    ((valuation (K F q)).leAddSubgroup 1) hO, hO⟩
private theorem O_compact : IsCompact (O F q) :=
  IsNonarchimedeanLocalField.isCompact_closedBall (K F q) 1
private theorem M_compact : IsCompact (M F q) :=
  (O_compact F q).of_isClosed_subset (M_clopen F q).isClosed (fun x h => show valuation (K F q) x ≤ 1 from le_of_lt h)
private theorem E0_open : IsOpen (E0 F ζ hζ q) := by
  let h := omegaHomeomorph F ζ hζ q (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)
  have hc : Continuous (omegaCoordinate F ζ hζ q) := by
    have he : Prod.snd ∘ h.symm = omegaCoordinate F ζ hζ q := rfl
    rw [← he]
    exact continuous_snd.comp h.symm.continuous
  have he : E0 F ζ hζ q = Subtype.val ''
      ((omegaCoordinate F ζ hζ q) ⁻¹' O F q) := by ext; simp [E0]
  rw [he]
  exact ((charts_open_and_borel_closed F ζ hζ q _
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).1.isOpenMap_subtype_val)
      _ ((O_clopen F q).isOpen.preimage hc)
private theorem E1_open : IsOpen (E1 F ζ hζ q) := by
  let h := deltaHomeomorph F ζ hζ q (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)
  have hc : Continuous (deltaCoordinate F ζ hζ q) := by
    have he : Prod.snd ∘ h.symm = deltaCoordinate F ζ hζ q := rfl
    rw [← he]
    exact continuous_snd.comp h.symm.continuous
  have he : E1 F ζ hζ q = Subtype.val ''
      ((deltaCoordinate F ζ hζ q) ⁻¹' M F q) := by ext; simp [E1]
  rw [he]
  exact ((charts_open_and_borel_closed F ζ hζ q _
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.1.isOpenMap_subtype_val)
      _ ((M_clopen F q).isOpen.preimage hc)

private theorem E_cover : E0 F ζ hζ q ∪ E1 F ζ hζ q = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ omega F ζ hζ q
  · let s := omegaCoordinate F ζ hζ q ⟨x,hx⟩
    by_cases hs : s ∈ O F q
    · exact Or.inl ⟨hx,hs⟩
    · obtain ⟨A,hA,hc⟩ := hx
      have hx : x ∈ omega F ζ hζ q := ⟨A,hA,hc⟩
      have hd : A 1 1 ≠ 0 := by
        intro hd
        have h0 : s = 0 := by simp [s, omegaCoordinate_eq F ζ hζ q ⟨x,hx⟩ A hA, hd]
        exact hs (by simp [h0, O])
      have hδ : x ∈ delta F ζ hζ q := ⟨A,hA,hd⟩
      refine Or.inr ⟨hδ, ?_⟩
      have ho := overlap_coordinates F ζ hζ q x hx hδ
      change valuation (K F q) (deltaCoordinate F ζ hζ q ⟨x,hδ⟩) < 1
      rw [← inv_eq_iff_eq_inv.mpr ho.1]
      exact (Valuation.val_le_one_or_val_inv_lt_one (valuation (K F q)) s).resolve_left hs
  · have hd : x ∈ delta F ζ hζ q := by
      have hc := charts_cover F ζ hζ q
      exact (show x ∈ omega F ζ hζ q ∪ delta F ζ hζ q by rw [hc]; trivial).resolve_left hx
    obtain ⟨A,hA,hd'⟩ := hd
    have hd : x ∈ delta F ζ hζ q := ⟨A,hA,hd'⟩
    have hc : A 1 0 = 0 := by
      by_contra hc
      exact hx ⟨A,hA,hc⟩
    refine Or.inr ⟨hd, ?_⟩
    simp [M, deltaCoordinate_eq F ζ hζ q ⟨x,hd⟩ A hA, hc]

private theorem E_disjoint : Disjoint (E0 F ζ hζ q) (E1 F ζ hζ q) := by
  rw [Set.disjoint_left]
  rintro x ⟨hx,h0⟩ ⟨hδ,h1⟩
  have ho := overlap_coordinates F ζ hζ q x hx hδ
  change valuation (K F q) (omegaCoordinate F ζ hζ q ⟨x,hx⟩) ≤ 1 at h0
  change valuation (K F q) (deltaCoordinate F ζ hζ q ⟨x,hδ⟩) < 1 at h1
  have hn := ho.2.1
  have hv : valuation (K F q) (omegaCoordinate F ζ hζ q ⟨x,hx⟩) ≠ 0 := by simpa
  have he : deltaCoordinate F ζ hζ q ⟨x,hδ⟩ =
      (omegaCoordinate F ζ hζ q ⟨x,hx⟩)⁻¹ := by rw [ho.1, inv_inv]
  rw [he, map_inv₀] at h1
  exact not_lt_of_ge (by simpa using (inv_le_inv₀ (show (0 : ValueGroupWithZero (K F q)) < 1 by simp) (zero_lt_iff.mpr hv)).mpr h0) h1
private theorem E0_rep (x : G F ζ hζ q) (A : KPRankOneInduction.GL2 F q)
    (ha : Matrix.ProjGenLinGroup.mk A = projection F ζ hζ q x) :
    x ∈ E0 F ζ hζ q ↔ A 1 0 ≠ 0 ∧ valuation (K F q) (A 1 1 / A 1 0) ≤ 1 := by
  constructor
  · rintro ⟨hx,hv⟩
    have hc : A 1 0 ≠ 0 := (mem_ordinaryOmega_iff F q A).mp (ha.symm ▸ hx)
    exact ⟨hc, by simpa [omegaCoordinate_eq F ζ hζ q ⟨x,hx⟩ A ha] using hv⟩
  · rintro ⟨hc,hv⟩
    have hx : x ∈ omega F ζ hζ q := ⟨A,ha,hc⟩
    exact ⟨hx, by simpa [omegaCoordinate_eq F ζ hζ q ⟨x,hx⟩ A ha] using hv⟩
private theorem E1_rep (x : G F ζ hζ q) (A : KPRankOneInduction.GL2 F q)
    (ha : Matrix.ProjGenLinGroup.mk A = projection F ζ hζ q x) :
    x ∈ E1 F ζ hζ q ↔ A 1 1 ≠ 0 ∧ valuation (K F q) (A 1 0 / A 1 1) < 1 := by
  constructor
  · rintro ⟨hx,hv⟩
    have hc : A 1 1 ≠ 0 := (mem_ordinaryDelta_iff F q A).mp (ha.symm ▸ hx)
    exact ⟨hc, by simpa [deltaCoordinate_eq F ζ hζ q ⟨x,hx⟩ A ha] using hv⟩
  · rintro ⟨hc,hv⟩
    have hx : x ∈ delta F ζ hζ q := ⟨A,ha,hc⟩
    exact ⟨hx, by simpa [deltaCoordinate_eq F ζ hζ q ⟨x,hx⟩ A ha] using hv⟩

private theorem bottom_mul (B A : KPRankOneInduction.GL2 F q) (hb : B 1 0 = 0)
    (j : Fin 2) : (B * A : KPRankOneInduction.GL2 F q) 1 j = B 1 1 * A 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb]
private theorem E0_left (b : Borel F ζ hζ q) (x : G F ζ hζ q) :
    b.val * x ∈ E0 F ζ hζ q ↔ x ∈ E0 F ζ hζ q := by
  obtain ⟨B,hB,hb⟩ := b.property
  obtain ⟨A,hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (projection F ζ hζ q x)
  have hBA : Matrix.ProjGenLinGroup.mk (B*A) = projection F ζ hζ q (b.val*x) := by
    rw [map_mul, map_mul, hB, hA]
  rw [E0_rep F ζ hζ q _ (B*A) hBA, E0_rep F ζ hζ q _ A hA,
    bottom_mul F q B A hb 0, bottom_mul F q B A hb 1]
  have hn : B 1 1 ≠ 0 := by
    intro hn
    exact B.det_ne_zero (by simp [Matrix.det_fin_two, hb, hn])
  simp [hn, mul_div_mul_left]
private theorem E1_left (b : Borel F ζ hζ q) (x : G F ζ hζ q) :
    b.val * x ∈ E1 F ζ hζ q ↔ x ∈ E1 F ζ hζ q := by
  obtain ⟨B,hB,hb⟩ := b.property
  obtain ⟨A,hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (projection F ζ hζ q x)
  have hBA : Matrix.ProjGenLinGroup.mk (B*A) = projection F ζ hζ q (b.val*x) := by
    rw [map_mul, map_mul, hB, hA]
  rw [E1_rep F ζ hζ q _ (B*A) hBA, E1_rep F ζ hζ q _ A hA,
    bottom_mul F q B A hb 0, bottom_mul F q B A hb 1]
  have hn : B 1 1 ≠ 0 := by
    intro hn
    exact B.det_ne_zero (by simp [Matrix.det_fin_two, hb, hn])
  simp [hn, mul_div_mul_left]

 def mu (s : K F q) : KPRankOneInduction.GL2 F q :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0,1;-1,-s] (by simp [Matrix.det_fin_two])
private theorem proj_mu (s : K F q) :
    projection F ζ hζ q (openCoordinate F ζ hζ q s) = Matrix.ProjGenLinGroup.mk (mu F q s) := by
  have hp : projection F ζ hζ q (signedWeyl F ζ hζ q) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w (K F q)) := by
    change Matrix.ProjGenLinGroup.mk (signedWeylRaw F ζ hζ q).g = _
    rw [signedWeyl_matrix]
  have hn : projection F ζ hζ q (nLift F ζ hζ q s) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (K F q) s) := rfl
  have hm : (KubotaRankTwo.w (K F q))⁻¹ * KubotaRankTwo.n (K F q) s = mu F q s := by
    apply inv_mul_eq_of_eq_mul
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.coe_w, KubotaRankTwo.coe_n, mu, Matrix.mul_apply]
  rw [openCoordinate, map_mul, map_inv, hp, hn, ← map_inv, ← map_mul, hm]
private theorem proj_W : projection F ζ hζ q (KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
    Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap (K F q)) := rfl
private theorem swap_inv : (KPStandardLocalRootLifts.weylSwap (K F q))⁻¹ =
    KPStandardLocalRootLifts.weylSwap (K F q) := by
  apply inv_eq_of_mul_eq_one_right
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply]
private theorem E0_pullback : {s : K F q | openCoordinate F ζ hζ q s ∈ E0 F ζ hζ q} = O F q := by
  ext s
  rw [Set.mem_ofPred_eq, E0_rep F ζ hζ q _ (mu F q s) (proj_mu F ζ hζ q s).symm]
  simp [mu, O]
private theorem E1_pullback : {s : K F q | openCoordinate F ζ hζ q s *
    (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ ∈ E1 F ζ hζ q} = M F q := by
  ext s
  have hp : Matrix.ProjGenLinGroup.mk
      (mu F q s * KPStandardLocalRootLifts.weylSwap (K F q)) =
      projection F ζ hζ q (openCoordinate F ζ hζ q s *
        (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹) := by
    simp only [map_mul, map_inv, proj_mu, proj_W]
    rw [← map_inv, swap_inv]
  rw [Set.mem_ofPred_eq, E1_rep F ζ hζ q _ _ hp]
  simp [mu, KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply, Fin.sum_univ_two, M]

private theorem omega_signed_factor (x : G F ζ hζ q) (hx : x ∈ omega F ζ hζ q) :
    ∃ b : Borel F ζ hζ q, x = b.val * openCoordinate F ζ hζ q
      (omegaCoordinate F ζ hζ q ⟨x,hx⟩) := by
  let s := omegaCoordinate F ζ hζ q ⟨x,hx⟩
  have hb : x * (openCoordinate F ζ hζ q s)⁻¹ ∈ Borel F ζ hζ q := by
    obtain ⟨A,hA,hc⟩ := hx
    have hs : s = A 1 1 / A 1 0 := omegaCoordinate_eq F ζ hζ q ⟨x,⟨A,hA,hc⟩⟩ A hA
    refine ⟨A * (mu F q s)⁻¹, ?_, ?_⟩
    · simp only [map_mul, map_inv, proj_mu, hA]
    · have hi : (mu F q s)⁻¹ = Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![-s,-1;1,0] (by simp [Matrix.det_fin_two]) := by
        apply inv_eq_of_mul_eq_one_right
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mu, Matrix.mul_apply]
      rw [hi]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
      field_simp
      ring
  exact ⟨⟨_,hb⟩, by simp [s, mul_assoc]⟩
private theorem delta_right_W_omega (x : G F ζ hζ q) (hx : x ∈ delta F ζ hζ q) :
    x * KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ omega F ζ hζ q := by
  obtain ⟨A,hA,hd⟩ := hx
  refine ⟨A * KPStandardLocalRootLifts.weylSwap (K F q), ?_, ?_⟩
  · rw [map_mul, map_mul, proj_W, hA]
  · simpa [KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply, Fin.sum_univ_two] using hd

private theorem E_compl : (E0 F ζ hζ q)ᶜ = E1 F ζ hζ q := by
  ext x
  have hc : x ∈ E0 F ζ hζ q ∨ x ∈ E1 F ζ hζ q := by
    have hc := E_cover F ζ hζ q
    exact show x ∈ E0 F ζ hζ q ∪ E1 F ζ hζ q by rw [hc]; trivial
  have hd := Set.disjoint_left.mp (E_disjoint F ζ hζ q)
  exact ⟨fun h => hc.resolve_left h, fun h h0 => hd h0 h⟩
private theorem E0_clopen : IsClopen (E0 F ζ hζ q) := by
  refine ⟨?_, E0_open F ζ hζ q⟩
  rw [← isOpen_compl_iff, E_compl]
  exact E1_open F ζ hζ q
private theorem E1_clopen : IsClopen (E1 F ζ hζ q) := by
  rw [← E_compl]
  exact (E0_clopen F ζ hζ q).compl

theorem actual_translated_cell_clopen_partition :
    ∃ (N : ℕ) (g : Fin N → Cover F ζ hζ q)
      (E : Fin N → Set (Cover F ζ hζ q)),
      (∀ i, IsClopen (E i)) ∧
      (∀ i (b : S.borel.B) (x : Cover F ζ hζ q),
        ((b : Cover F ζ hζ q) * x ∈ E i ↔ x ∈ E i)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      (⋃ i, E i) = Set.univ ∧
      (∀ i (x : Cover F ζ hζ q), x ∈ E i →
        ∃ (b : S.borel.B) (s : LocalField F q),
          x = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q s * (g i)⁻¹) ∧
      (∀ i, IsCompact {s : LocalField F q |
        openCoordinate F ζ hζ q s * (g i)⁻¹ ∈ E i}) := by
  classical
  let g : Fin 2 → G F ζ hζ q := ![1, KPPGLLocalCover.W F ζ hζ (Sum.inr q)]
  let E : Fin 2 → Set (G F ζ hζ q) := ![E0 F ζ hζ q, E1 F ζ hζ q]
  refine ⟨2,g,E,?_,?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact E0_clopen F ζ hζ q
    · exact E1_clopen F ζ hζ q
  · intro i b x
    let b' : Borel F ζ hζ q := ⟨b.val, by change b.val ∈ KPExceptionalRaw.actualBorel F ζ hζ q; rw [← S.borel_eq]; exact b.property⟩
    fin_cases i
    · exact E0_left F ζ hζ q b' x
    · exact E1_left F ζ hζ q b' x
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact E_disjoint F ζ hζ q
    · exact (E_disjoint F ζ hζ q).symm
    · exact (hij rfl).elim
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ E0 F ζ hζ q ∪ E1 F ζ hζ q := by rw [E_cover]; trivial
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨0,hx⟩
    · exact Set.mem_iUnion.mpr ⟨1,hx⟩
  · intro i x hx
    fin_cases i
    · obtain ⟨hΩ,hv⟩ := hx
      obtain ⟨b,hb⟩ := omega_signed_factor F ζ hζ q x hΩ
      refine ⟨⟨b.val, by rw [S.borel_eq]; exact b.property⟩,
        omegaCoordinate F ζ hζ q ⟨x,hΩ⟩, ?_⟩
      simpa [g] using hb
    · obtain ⟨hΔ,hv⟩ := hx
      obtain ⟨b,hb⟩ := omega_signed_factor F ζ hζ q
        (x * KPPGLLocalCover.W F ζ hζ (Sum.inr q))
        (delta_right_W_omega F ζ hζ q x hΔ)
      refine ⟨⟨b.val, by rw [S.borel_eq]; exact b.property⟩,
        omegaCoordinate F ζ hζ q ⟨x * KPPGLLocalCover.W F ζ hζ (Sum.inr q),
          delta_right_W_omega F ζ hζ q x hΔ⟩, ?_⟩
      have he := congrArg (fun a : G F ζ hζ q =>
        a * (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹) hb
      simpa [g, mul_assoc] using he
  · intro i
    fin_cases i
    · simpa [g,E] using (E0_pullback F ζ hζ q ▸ O_compact F q)
    · simpa [g,E] using (E1_pullback F ζ hζ q ▸ M_compact F q)

end
end DedekindZetaZeroFree.KPActualResidueSources
