module

public import DedekindZetaZeroFree.Eisenstein.Sections.FullProductFlatFamily
public import DedekindZetaZeroFree.Geometry.SymmetricSpaces.ArchimedeanSphericalQuotients

@[expose] public section

noncomputable section
open scoped NumberField Classical Matrix
open NumberField
namespace DedekindZetaZeroFree.KPContinuation.ArchCompact
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private lemma row_det_identity (a b c d : ℂ) :
    ‖a * d - b * c‖ ^ 2 = (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) -
      ‖a * star c + b * star d‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private lemma fixed_origin_rows (g : GL (Fin 2) ℂ)
    (h : KPArch.action g (0, 0) = (0, 0)) :
    (‖g 0 0‖ ^ 2 + ‖g 0 1‖ ^ 2 = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖) ∧
    (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖) ∧
    g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1) = 0 := by
  have hd := KPArch.actionDenominator_pos g (0, 0)
  have hbottom : 0 < ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 := by
    simpa [KPArch.actionDenominator, KPArch.height, add_comm] using hd
  have ht := congrArg Prod.snd h
  have hb : ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
    have hh := congrArg Real.exp ht
    have hx := KPArch.action_height g (0, 0)
    change KPArch.height (KPArch.action g (0, 0)) = Real.exp 0 at hh
    rw [hx, Real.exp_zero] at hh
    simp only [KPArch.height, Real.exp_zero, mul_one, mul_zero, zero_add, norm_zero,
      zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at hh
    have he := (div_eq_one_iff_eq (by nlinarith :
      ‖g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * 1 ^ 2 ≠ 0)).mp hh
    nlinarith
  have hn := congrArg Prod.fst h
  have hz : g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1) = 0 := by
    simp only [KPArch.action, KPArch.actionDenominator, KPArch.height, Real.exp_zero,
      mul_zero, zero_add, one_pow, Complex.ofReal_one, mul_one] at hn
    have hh : (‖g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 : ℝ) ≠ 0 := by linarith
    simpa only [add_comm] using
      (div_eq_zero_iff).mp hn |>.resolve_right (by exact_mod_cast hh)
  refine ⟨?_, hb, hz⟩
  have hi := row_det_identity (g 0 0) (g 0 1) (g 1 0) (g 1 1)
  rw [← Matrix.det_fin_two, hz, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, hb] at hi
  have hp : 0 < ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := norm_pos_iff.mpr g.det_ne_zero
  nlinarith

theorem fixed_origin_has_su2 (g : GL (Fin 2) ℂ)
    (h : KPArch.action g (0, 0) = (0, 0)) :
    ∃ k : KPCplxCharacterHaar.ComplexSU2,
      Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k) =
        Matrix.ProjGenLinGroup.mk g := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (g : Matrix (Fin 2) (Fin 2) ℂ).det
    (by decide : 0 < 2)
  have ht0 : t ≠ 0 := by
    intro he
    rw [he, zero_pow (by decide : 2 ≠ 0)] at ht
    exact g.det_ne_zero ht.symm
  let A : Matrix (Fin 2) (Fin 2) ℂ := t⁻¹ • (g : Matrix (Fin 2) (Fin 2) ℂ)
  have hdet : A.det = 1 := by
    dsimp only [A]
    rw [Matrix.det_smul]
    simp only [Fintype.card_fin]
    rw [← ht, ← mul_pow, inv_mul_cancel₀ ht0, one_pow]
  obtain ⟨ha, hb, hz⟩ := fixed_origin_rows g h
  have htNorm : ‖t‖ ^ 2 = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
    rw [← norm_pow, ht]
  have hnorm : ‖t⁻¹‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ = 1 := by
    rw [← htNorm, norm_inv, ← mul_pow, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht0), one_pow]
  have ha' : ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 = 1 := by
    simp only [A, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    rw [← mul_add, ha, hnorm]
  have hb' : ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 = 1 := by
    simp only [A, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    rw [← mul_add, hb, hnorm]
  have hz' : A 0 0 * star (A 1 0) + A 0 1 * star (A 1 1) = 0 := by
    simp only [A, Matrix.smul_apply, smul_eq_mul, star_mul]
    calc
      _ = (t⁻¹ * star t⁻¹) * (g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1)) := by ring
      _ = 0 := by rw [hz, mul_zero]
  have hu : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_conj, Complex.normSq_eq_norm_sq] using
        congrArg (fun r : ℝ => (r : ℂ)) ha'
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hz'
    · have hh := congrArg star hz'
      simpa [Matrix.mul_apply, Fin.sum_univ_two, star_add, star_mul, mul_comm] using hh
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_conj, Complex.normSq_eq_norm_sq] using
        congrArg (fun r : ℝ => (r : ℂ)) hb'
  let k : KPCplxCharacterHaar.ComplexSU2 :=
    ⟨A, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hu, hdet⟩⟩
  refine ⟨k, ?_⟩
  have he : KPCplxCharacterHaar.complexSU2Embedding k =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 t⁻¹ (inv_ne_zero ht0)) * g := by
    apply Units.ext
    ext i j
    simp [KPCplxCharacterHaar.complexSU2Embedding, k, A,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar,
      Matrix.mul_apply, Matrix.diagonal]
  rw [he, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

include ζ hζ in

theorem KInfinity_has_su2 (k : KPContSectorArchSphericalFibers.KInfinity F) :
    ∃ r : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2,
      ∀ w, Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (r w)) =
        k.val w := by
  have hk := (KPContSectorArchSphericalFibers.mem_KInfinity_iff F k.val).mp k.property
  have hw (w : InfinitePlace F) : KPArch.action (k.val w).out (0, 0) = (0, 0) := by
    let i := KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w
    have he : KPCusp.complexPlace F i = w :=
      (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).left_inv w
    have hi := congrFun hk i
    change KPArch.action (k.val (KPCusp.complexPlace F i)).out (0, 0) = (0, 0) at hi
    simpa only [he] using hi
  choose r hr using fun w => fixed_origin_has_su2 (k.val w).out (hw w)
  refine ⟨r, fun w => ?_⟩
  exact (hr w).trans (Quotient.out_eq (k.val w))

theorem archimedeanInsertion_mem_iwasawaCompact
    (k : KPContSectorArchSphericalFibers.KInfinity F) :
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val ∈
      (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K := by
  obtain ⟨r, hr⟩ := KInfinity_has_su2 F ζ hζ k
  have he : k.val = fun w =>
      Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (r w)) := by
    funext w
    exact (hr w).symm
  rw [he, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg
  exact KPContFlatFullProductIwasawa.complexCompactLift_mem F ζ hζ w (r w)

theorem alpha_archimedeanInsertion_right
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (k : KPContSectorArchSphericalFibers.KInfinity F) :
    KPContFlatFullProductIwasawa.alpha F ζ hζ
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) =
        KPContFlatFullProductIwasawa.alpha F ζ hζ g :=
  KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ g
    ⟨_, archimedeanInsertion_mem_iwasawaCompact F ζ hζ k⟩

end DedekindZetaZeroFree.KPContinuation.ArchCompact

end
