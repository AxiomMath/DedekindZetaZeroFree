module

public import DedekindZetaZeroFree.Adeles.Lattices.MinkowskiShortRowsAndIwasawaHeight
public import DedekindZetaZeroFree.Adeles.Quotients.NormalizedCuspHeightsAndHoroballSeparation

@[expose] public section

noncomputable section

open scoped nonZeroDivisors Classical

open NumberField

namespace DedekindZetaZeroFree.CuspHeightProof

variable (F : Type*) [Field F] [NumberField F]

def coordEquiv (hF : InfinitePlace.nrRealPlaces F = 0) :
    CuspShortRows.Space (InfinitePlace.nrComplexPlaces F) ≃ₗ[ℝ]
      (Fin 2 → mixedEmbedding.mixedSpace F) where
  toFun r j := (0, fun w => r (Fintype.equivFin {w : InfinitePlace F // w.IsComplex} w, j))
  invFun f := WithLp.toLp 2 (fun ij => (f ij.2).2
    ((Fintype.equivFin {w : InfinitePlace F // w.IsComplex}).symm ij.1))
  left_inv r := by ext ij; simp
  right_inv f := by
    haveI : IsEmpty {w : InfinitePlace F // w.IsReal} := Fintype.card_eq_zero_iff.mp hF
    funext j
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext w; simp
  map_add' r s := by ext j w <;> simp
  map_smul' a r := by ext j w <;> simp

def rowBasis (hF : InfinitePlace.nrRealPlaces F = 0) :=
  (Pi.basis (fun _ : Fin 2 => mixedEmbedding.latticeBasis F)).map (coordEquiv F hF).symm

def rowLattice (hF : InfinitePlace.nrRealPlaces F = 0) :
    Submodule ℤ (CuspShortRows.Space (InfinitePlace.nrComplexPlaces F)) :=
  Submodule.span ℤ (Set.range (rowBasis F hF))

instance instDiscreteTopologyCuspRowLattice (hF : InfinitePlace.nrRealPlaces F = 0) : DiscreteTopology (rowLattice F hF) := by
  unfold rowLattice rowBasis
  infer_instance

end DedekindZetaZeroFree.CuspHeightProof

end

section

noncomputable section
open scoped nonZeroDivisors Classical
open NumberField

namespace DedekindZetaZeroFree.CuspHeightProof
variable (F : Type*) [Field F] [NumberField F]

private theorem mem_coords (hF : InfinitePlace.nrRealPlaces F = 0)
    (r : CuspShortRows.Space (InfinitePlace.nrComplexPlaces F)) (hr : r ∈ rowLattice F hF)
    (j : Fin 2) : coordEquiv F hF r j ∈ mixedEmbedding.integerLattice F := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp only [rowBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
    rw [Pi.basis_apply]
    by_cases h : j = i.1
    · subst j
      simp only [Pi.single_eq_same]
      rw [← mixedEmbedding.span_latticeBasis]
      exact Submodule.subset_span (Set.mem_range_self _)
    · simp [Pi.single_eq_of_ne h]
  | zero => simp
  | add x y hx hy ihx ihy => simpa using add_mem ihx ihy
  | smul a x hx ih => simpa using Submodule.smul_mem (mixedEmbedding.integerLattice F) a ih

private theorem exists_integral_coords (hF : InfinitePlace.nrRealPlaces F = 0)
    (r : CuspShortRows.Space (InfinitePlace.nrComplexPlaces F)) (hr : r ∈ rowLattice F hF) :
    ∃ a b : 𝓞 F, ∀ i, r (i, 0) = (KPCusp.complexPlace F i).embedding (a : F) ∧
      r (i, 1) = (KPCusp.complexPlace F i).embedding (b : F) := by
  obtain ⟨a, ha⟩ := mem_coords F hF r hr 0
  obtain ⟨b, hb⟩ := mem_coords F hF r hr 1
  refine ⟨a, b, fun i => ?_⟩
  have ha' := congrArg (fun x : mixedEmbedding.mixedSpace F => x.2
    ((Fintype.equivFin {w : InfinitePlace F // w.IsComplex}).symm i)) ha
  have hb' := congrArg (fun x : mixedEmbedding.mixedSpace F => x.2
    ((Fintype.equivFin {w : InfinitePlace F // w.IsComplex}).symm i)) hb
  exact ⟨by simpa [coordEquiv, KPCusp.complexPlace] using ha'.symm,
    by simpa [coordEquiv, KPCusp.complexPlace] using hb'.symm⟩

private theorem nonzero_rows (hF : InfinitePlace.nrRealPlaces F = 0)
    (r : CuspShortRows.Space (InfinitePlace.nrComplexPlaces F)) (hr : r ∈ rowLattice F hF)
    (hr0 : r ≠ 0) (i : Fin (InfinitePlace.nrComplexPlaces F)) :
    CuspShortRows.row _ r i ≠ 0 := by
  obtain ⟨a, b, hab⟩ := exists_integral_coords F hF r hr
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [CuspShortRows.row, (hab i).1] at h0
  rw [CuspShortRows.row, (hab i).2] at h1
  have ha : (a : F) = 0 := (KPCusp.complexPlace F i).embedding.injective (by simpa using h0)
  have hb : (b : F) = 0 := (KPCusp.complexPlace F i).embedding.injective (by simpa using h1)
  apply hr0
  ext ⟨k, j⟩
  fin_cases j <;> simp [(hab k).1, (hab k).2, ha, hb]

private theorem iwasawa_norm (a b x : ℂ) (y : ℝ) (hy : 0 < y) :
    ‖WithLp.toLp 2 (Matrix.vecMul ![a,b] (CuspShortRows.iwasawaMatrix (x,y)))‖ ^ 2 =
      (‖a*x+b‖ ^ 2 + ‖a‖ ^ 2 * y^2) / y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hs2 := Real.sq_sqrt hy.le
  have hsc : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hv : Matrix.vecMul ![a,b] (CuspShortRows.iwasawaMatrix (x,y)) =
      ![a * (Real.sqrt y : ℂ), (a*x+b) / (Real.sqrt y : ℂ)] := by
    ext j
    fin_cases j <;> simp [CuspShortRows.iwasawaMatrix, Matrix.vecMul, Fin.sum_univ_two]
    ring
  rw [hv, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  field_simp
  rw [show Real.sqrt y ^ 4 = y ^ 2 by nlinarith]
  rw [hs2]
  ring

private theorem norm_height (r : KPCusp.Row F)
    (v : CuspShortRows.Space (InfinitePlace.nrComplexPlaces F))
    (hv : ∀ i, v (i,0) = (KPCusp.complexPlace F i).embedding r.val.1 ∧
      v (i,1) = (KPCusp.complexPlace F i).embedding r.val.2)
    (z : KPArch.Space (InfinitePlace.nrComplexPlaces F)) :
    CuspShortRows.height _ v
      (fun i => CuspShortRows.iwasawa ((z i).1, KPArch.height (z i)) (Real.exp_pos _)) =
    (∏ i, KPArch.height (z i)) / ∏ i, KPCusp.rowDenominator F r i (z i) := by
  have hh : ∀ i, CuspShortRows.row _ v i =
      ![(KPCusp.complexPlace F i).embedding r.val.1,
        (KPCusp.complexPlace F i).embedding r.val.2] := by
    intro i; ext j; fin_cases j <;> simp [CuspShortRows.row, (hv i).1, (hv i).2]
  simp only [CuspShortRows.height, CuspShortRows.rowNormSq, CuspShortRows.iwasawa, hh]
  have hi : ∀ i, 0 < KPArch.height (z i) := fun i => Real.exp_pos _
  simp_rw [iwasawa_norm _ _ _ _ (hi _)]
  simp only [KPCusp.rowDenominator, Finset.prod_div_distrib, inv_div]

private theorem content_lower (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0)
    (r : KPCusp.Row F) (a b : 𝓞 F) (ha : r.val.1 = a) (hb : r.val.2 = b) :
    0 < (FractionalIdeal.absNorm (1+J) : ℝ) ∧
      (FractionalIdeal.absNorm (1+J) : ℝ) ≤ (FractionalIdeal.absNorm (KPCusp.content F J r) : ℝ) := by
  have hn : KPCusp.content F J r ≠ 0 := by
    intro h
    change _ + _ = 0 at h
    rw [← FractionalIdeal.sup_eq_add] at h
    have hs := sup_eq_bot_iff.mp h
    have hc := FractionalIdeal.spanSingleton_eq_zero_iff.mp hs.1
    have hd := FractionalIdeal.spanSingleton_eq_zero_iff.mp ((mul_eq_zero.mp hs.2).resolve_right hJ)
    exact r.property (Prod.ext hc hd)
  have hle : KPCusp.content F J r ≤ 1+J := by
    have ha' : FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) ≤ 1 := by
      rw [FractionalIdeal.spanSingleton_le_iff_mem]
      exact (FractionalIdeal.mem_one_iff (𝓞 F)⁰).mpr ⟨a, rfl⟩
    have hb' : FractionalIdeal.spanSingleton (𝓞 F)⁰ (b : F) ≤ 1 := by
      rw [FractionalIdeal.spanSingleton_le_iff_mem]
      exact (FractionalIdeal.mem_one_iff (𝓞 F)⁰).mpr ⟨b, rfl⟩
    simpa [KPCusp.content, ha, hb] using add_le_add ha' (mul_le_mul' hb' (le_refl J))
  have hN : (1+J : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    intro h
    rw [← FractionalIdeal.sup_eq_add] at h
    exact one_ne_zero (sup_eq_bot_iff.mp h).1
  have hnpos : 0 < FractionalIdeal.absNorm (1+J) :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hN))
  have hint : KPCusp.content F J r * (1+J)⁻¹ ≤ 1 := by
    calc _ ≤ (1+J)*(1+J)⁻¹ := mul_le_mul' hle le_rfl
         _ = 1 := mul_inv_cancel₀ hN
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hint
  have hi0 : I ≠ ⊥ := by
    intro hi
    have hz : KPCusp.content F J r * (1+J)⁻¹ = 0 := by simpa [hi] using hI.symm
    exact mul_ne_zero hn (inv_ne_zero hN) hz
  have hn1 : (1 : ℚ) ≤ FractionalIdeal.absNorm (KPCusp.content F J r * (1+J)⁻¹) := by
    rw [← hI, FractionalIdeal.coeIdeal_absNorm]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hi0)
  rw [map_mul, map_inv₀, ← div_eq_mul_inv] at hn1
  have hbound := (le_div_iff₀ hnpos).mp hn1
  exact ⟨by exact_mod_cast hnpos, by exact_mod_cast (by simpa using hbound : FractionalIdeal.absNorm (1+J) ≤ FractionalIdeal.absNorm (KPCusp.content F J r))⟩

private theorem normalized_height_aux (hF : InfinitePlace.nrRealPlaces F = 0)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : KPArch.Space (InfinitePlace.nrComplexPlaces F),
      ∃ r : KPCusp.Row F, c ≤ KPCusp.normalizedHeight F J r z := by
  classical
  have hd : 1 ≤ InfinitePlace.nrComplexPlaces F := by
    have hr := InfinitePlace.card_add_two_mul_card_eq_rank F
    have hp := Module.finrank_pos (R := ℚ) (M := F)
    omega
  letI : IsZLattice ℝ (rowLattice F hF) := by unfold rowLattice rowBasis; infer_instance
  obtain ⟨c, hc, hshort⟩ := kp_cusp_minkowski_iwasawa_height
    (InfinitePlace.nrComplexPlaces F) hd (rowLattice F hF) (nonzero_rows F hF)
  have hn : 0 < (FractionalIdeal.absNorm (1+J) : ℝ) := by
    have hN : (1+J : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      intro h
      rw [← FractionalIdeal.sup_eq_add] at h
      exact one_ne_zero (sup_eq_bot_iff.mp h).1
    have hnpos : 0 < FractionalIdeal.absNorm (1+J) :=
      lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hN))
    exact_mod_cast hnpos
  refine ⟨(FractionalIdeal.absNorm (1+J) : ℝ)*c, mul_pos hn hc, fun z => ?_⟩
  obtain ⟨v, hv, hv0, hheight⟩ := hshort (fun i => ((z i).1, KPArch.height (z i)))
    (fun i => Real.exp_pos _)
  obtain ⟨a,b,hab⟩ := exists_integral_coords F hF v hv
  have hab0 : ((a : F), (b : F)) ≠ 0 := by
    intro hz
    have ha : (a : F) = 0 := congrArg Prod.fst hz
    have hb : (b : F) = 0 := congrArg Prod.snd hz
    apply hv0
    ext ⟨i,j⟩
    fin_cases j <;> simp [(hab i).1, (hab i).2, ha, hb]
  let r : KPCusp.Row F := ⟨((a : F), (b : F)), hab0⟩
  have hbound := (content_lower F J hJ r a b rfl rfl).2
  rw [norm_height F r v hab z] at hheight
  have hratio : 0 < (∏ i, KPArch.height (z i)) / ∏ i, KPCusp.rowDenominator F r i (z i) :=
    lt_of_lt_of_le hc hheight
  refine ⟨r, ?_⟩
  calc (FractionalIdeal.absNorm (1+J) : ℝ)*c ≤
      (FractionalIdeal.absNorm (1+J) : ℝ)*((∏ i, KPArch.height (z i)) / ∏ i, KPCusp.rowDenominator F r i (z i)) :=
        mul_le_mul_of_nonneg_left hheight hn.le
    _ ≤ (FractionalIdeal.absNorm (KPCusp.content F J r) : ℝ)*
      ((∏ i, KPArch.height (z i)) / ∏ i, KPCusp.rowDenominator F r i (z i)) :=
        mul_le_mul_of_nonneg_right hbound hratio.le
    _ = KPCusp.normalizedHeight F J r z := by rw [KPCusp.normalizedHeight, mul_div_assoc]

end DedekindZetaZeroFree.CuspHeightProof

namespace DedekindZetaZeroFree

theorem kp_cusp_minkowski_normalized_height (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hJ : J ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ z : KPArch.Space (NumberField.InfinitePlace.nrComplexPlaces F),
        ∃ r : KPCusp.Row F, c ≤ KPCusp.normalizedHeight F J r z := by
  exact CuspHeightProof.normalized_height_aux F hF J hJ

end DedekindZetaZeroFree

end
end
