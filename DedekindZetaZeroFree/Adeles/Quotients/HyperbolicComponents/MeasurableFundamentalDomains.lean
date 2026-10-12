module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.SiegelCoverAndTruncation
public import DedekindZetaZeroFree.Metaplectic.Kubota.GenuineCuspLinesAndUnitaryMonodromy

@[expose] public section

section

noncomputable section
open scoped Classical NumberField
open MeasureTheory

namespace DedekindZetaZeroFree.KPFiniteAdelicCuspEnds.FundamentalDomainGeometry

private lemma fixed_height_eq (g : GL (Fin 2) ℂ) (z : KPArch.H3)
    (h : KPArch.action g z = z) :
    KPArch.actionDenominator g z = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
  have h2 := KPArch.action_height g z
  rw [h] at h2
  have h2' : KPArch.height z =
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ * KPArch.height z / KPArch.actionDenominator g z := by
    simpa [KPArch.actionDenominator] using h2
  have hy : KPArch.height z ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hD := KPArch.actionDenominator_pos g z
  have h3 : KPArch.actionDenominator g z * KPArch.height z =
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ * KPArch.height z := by
    rw [mul_comm (KPArch.actionDenominator g z)]
    nth_rewrite 1 [h2']
    exact div_mul_cancel₀ _ hD.ne'
  exact mul_right_cancel₀ hy h3

private lemma mem_center_of_eq (g : GL (Fin 2) ℂ) (h10 : g 1 0 = 0) (h01 : g 0 1 = 0)
    (h11 : g 0 0 = g 1 1) : g ∈ Subgroup.center (GL (Fin 2) ℂ) := by
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨g 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, h10, h01, h11]

private lemma fixed_first_coordinate (g : GL (Fin 2) ℂ) (hc : g 1 0 = 0) (z : KPArch.H3)
    (h : KPArch.action g z = z) :
    (g 0 0 - g 1 1) * z.1 = -g 0 1 := by
  have h1 : (KPArch.action g z).1 = z.1 := congrArg Prod.fst h
  have hd : (↑(‖g 1 1‖ ^ 2) : ℂ) = g 1 1 * star (g 1 1) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, Complex.star_def, mul_comm]
  have hden : KPArch.actionDenominator g z = ‖g 1 1‖ ^ 2 := by
    simp [KPArch.actionDenominator, hc]
  have h11ne : g 1 1 ≠ 0 := by
    intro hh
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero g
    rw [Matrix.det_fin_two, hc, hh] at hdet
    simp at hdet
  have hsd : star (g 1 1) ≠ 0 := by
    intro hs; exact h11ne (star_eq_zero.mp hs)
  have hdne : (↑(‖g 1 1‖ ^ 2) : ℂ) ≠ 0 := by
    rw [hd]; exact mul_ne_zero h11ne hsd
  have h1' : ((g 0 0 * z.1 + g 0 1) * star (g 1 0 * z.1 + g 1 1)
      + g 0 0 * star (g 1 0) * (KPArch.height z ^ 2 : ℝ))
      / (KPArch.actionDenominator g z : ℂ) = z.1 := h1
  rw [hc, hden] at h1'
  simp only [mul_zero, zero_mul, add_zero, zero_add, star_zero] at h1'
  have hmul : (g 0 0 * z.1 + g 0 1) * star (g 1 1) = z.1 * (↑(‖g 1 1‖ ^ 2) : ℂ) :=
    (div_eq_iff hdne).mp h1'
  rw [hd] at hmul
  have h2 : g 0 0 * z.1 + g 0 1 = z.1 * g 1 1 := by
    refine mul_right_cancel₀ hsd ?_
    rw [hmul, mul_assoc]
  linear_combination h2

private lemma volume_fixed_action_H3 (g : GL (Fin 2) ℂ)
    (hg : g ∉ Subgroup.center (GL (Fin 2) ℂ)) :
    (volume : Measure KPArch.H3) {z | KPArch.action g z = z} = 0 := by
  by_cases hc : g 1 0 = 0
  ·

    by_cases hdd : ‖g 1 1‖ ^ 2 = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖
    · by_cases h00 : g 0 0 = g 1 1
      · have hempty : {z | KPArch.action g z = z} = ∅ := by
          ext z; constructor
          · intro hz
            have h := fixed_first_coordinate g hc z hz
            rw [h00] at h
            have hz1 : g 0 1 = 0 := by
              have h' : -g 0 1 = 0 := by simpa using h.symm
              simpa using h'
            exact absurd (mem_center_of_eq g hc hz1 h00) hg
          · intro h; exact h.elim
        rw [hempty, measure_empty]
      · have hsub : {z | KPArch.action g z = z} ⊆
            {z : KPArch.H3 | z.1 = -g 0 1 / (g 0 0 - g 1 1)} := by
          intro z hz
          have h := fixed_first_coordinate g hc z hz
          have hne : g 0 0 - g 1 1 ≠ 0 := sub_ne_zero.mpr h00
          show z.1 = -g 0 1 / (g 0 0 - g 1 1)
          field_simp
          linear_combination h
        have hline : {z : KPArch.H3 | z.1 = -g 0 1 / (g 0 0 - g 1 1)} =
            {-g 0 1 / (g 0 0 - g 1 1)} ×ˢ (Set.univ : Set ℝ) := by
          ext z; simp
        have hvol : (volume : Measure KPArch.H3)
            {z : KPArch.H3 | z.1 = -g 0 1 / (g 0 0 - g 1 1)} = 0 := by
          rw [hline, Measure.volume_eq_prod ℂ ℝ, Measure.prod_prod, measure_singleton,
            zero_mul]
        exact measure_mono_null hsub hvol
    · have hempty : {z | KPArch.action g z = z} = ∅ := by
        ext z; constructor
        · intro hz
          have hden := fixed_height_eq g z hz
          have h' : ‖g 1 1‖ ^ 2 = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
            rw [← hden]; simp [KPArch.actionDenominator, hc]
          exact absurd h' hdd
        · intro h; exact h.elim
      rw [hempty, measure_empty]
  ·

    set D : ℝ := ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ with hD
    set ψ : ℂ → ℝ := fun x => (1/2) * Real.log ((D - ‖g 1 0 * x + g 1 1‖ ^ 2) / ‖g 1 0‖ ^ 2)
      with hψ
    have hψm : Measurable ψ := by rw [hψ]; fun_prop
    have hgraph : MeasurableSet {z : KPArch.H3 | z.2 = ψ z.1} := measurableSet_graph hψm
    have hsub : {z | KPArch.action g z = z} ⊆ {z : KPArch.H3 | z.2 = ψ z.1} := by
      intro z hz
      have hden := fixed_height_eq g z hz
      have hden' : ‖g 1 0 * z.1 + g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * (KPArch.height z) ^ 2 = D := by
        rw [hD, ← hden]; rfl
      have hcpos : (0:ℝ) < ‖g 1 0‖ := norm_pos_iff.mpr hc
      have hc2 : (‖g 1 0‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (ne_of_gt hcpos)
      have hw : (KPArch.height z) ^ 2 = (D - ‖g 1 0 * z.1 + g 1 1‖ ^ 2) / ‖g 1 0‖ ^ 2 := by
        rw [eq_div_iff hc2]
        nlinarith [hden']
      have hlog : Real.log ((KPArch.height z) ^ 2) =
          Real.log ((D - ‖g 1 0 * z.1 + g 1 1‖ ^ 2) / ‖g 1 0‖ ^ 2) := by rw [hw]
      rw [KPArch.height, Real.log_pow, Real.log_exp] at hlog
      show z.2 = ψ z.1
      rw [hψ]
      simp only
      linarith [hlog]
    have hfiber : (fun x : ℂ => (volume : Measure ℝ) (Prod.mk x ⁻¹' {z : KPArch.H3 | z.2 = ψ z.1}))
        =ᵐ[(volume : Measure ℂ)] 0 := by
      apply Filter.Eventually.of_forall
      intro x
      have hset : Prod.mk x ⁻¹' {z : KPArch.H3 | z.2 = ψ z.1} = {ψ x} := by
        ext u; simp
      change (volume : Measure ℝ) (Prod.mk x ⁻¹' {z : KPArch.H3 | z.2 = ψ z.1}) = 0
      rw [hset, measure_singleton]
    have hprod : ((volume : Measure ℂ).prod (volume : Measure ℝ))
        {z : KPArch.H3 | z.2 = ψ z.1} = 0 :=
      Measure.measure_prod_null_of_ae_null hgraph hfiber
    have hvol : (volume : Measure KPArch.H3) {z : KPArch.H3 | z.2 = ψ z.1} = 0 := by
      rw [Measure.volume_eq_prod ℂ ℝ]; exact hprod
    exact measure_mono_null hsub hvol

private lemma map_not_mem_center {F : Type} [Field F] (e : F →+* ℂ) (he : Function.Injective e)
    (A : GL (Fin 2) F) (hA : A ∉ Subgroup.center (GL (Fin 2) F)) :
    Matrix.GeneralLinearGroup.map e A ∉ Subgroup.center (GL (Fin 2) ℂ) := by
  intro hc
  apply hA
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hc ⊢
  obtain ⟨z, hz⟩ := hc
  have hentry : ∀ i j : Fin 2, e (A i j) = Matrix.scalar (Fin 2) z i j := by
    intro i j
    rw [← Matrix.GeneralLinearGroup.map_apply, hz]
  have h01 : A 0 1 = 0 := by
    have h := hentry 0 1
    simp [Matrix.scalar_apply, Matrix.diagonal_apply] at h
    exact he (by simpa using h)
  have h10 : A 1 0 = 0 := by
    have h := hentry 1 0
    simp [Matrix.scalar_apply, Matrix.diagonal_apply] at h
    exact he (by simpa using h)
  have hdiag : A 0 0 = A 1 1 := by
    have h1 := hentry 0 0
    have h2 := hentry 1 1
    simp [Matrix.scalar_apply, Matrix.diagonal_apply] at h1 h2
    exact he (h1.trans h2.symm)
  refine ⟨A 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, h01, h10, hdiag]

theorem rationalProjective_fixed_locus_volume_zero
    (F : Type) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (γ : KPCuspArithmetic.PGL2 F) (hγ : γ ≠ 1) :
    (volume : Measure (KPArch.Space (KPCuspLogShape.dimension F)))
      {x | γ • x = x} = 0 := by
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  have hAne : A ∉ Subgroup.center (GL (Fin 2) F) := by
    intro hc
    exact hγ (by rw [← hA, Matrix.ProjGenLinGroup.mk_eq_one.mpr hc])
  let i0 : Fin (KPCuspLogShape.dimension F) := ⟨0, hd⟩
  have he : Function.Injective (KPCusp.complexPlace F i0).embedding := RingHom.injective _
  have hge : Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i0).embedding A ∉
      Subgroup.center (GL (Fin 2) ℂ) := map_not_mem_center _ he A hAne
  have hS : (volume : Measure KPArch.H3)
      {z | KPArch.action (Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i0).embedding A) z = z}
      = 0 :=
    volume_fixed_action_H3 _ hge
  have hsub : {x : KPArch.Space (KPCuspLogShape.dimension F) | γ • x = x} ⊆
      Function.eval i0 ⁻¹' {z : KPArch.H3 |
        KPArch.action (Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i0).embedding A) z
          = z} := by
    intro x hx
    have hx' : KPCuspSiegel.action F γ x = x := hx
    rw [← hA, KPCuspSiegel.action_mk] at hx'
    have h2 := congrFun hx' i0
    simpa [KPCuspSiegel.glAction, KPArch.productAction, Function.eval] using h2
  have hpi : (volume : Measure (KPArch.Space (KPCuspLogShape.dimension F)))
      (Function.eval i0 ⁻¹' {z : KPArch.H3 |
        KPArch.action (Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i0).embedding A) z
          = z}) = 0 := by
    rw [MeasureTheory.volume_pi]
    exact Measure.pi_eval_preimage_null
      (fun _ : Fin (KPCuspLogShape.dimension F) => (volume : Measure KPArch.H3)) hS
  exact measure_mono_null hsub hpi

end DedekindZetaZeroFree.KPFiniteAdelicCuspEnds.FundamentalDomainGeometry

end

end

section

noncomputable section
open scoped Classical NumberField Matrix Pointwise

namespace DedekindZetaZeroFree.KPFiniteAdelicCuspEnds.FundamentalDomainGeometry

theorem arithmeticStabilizer_finiteRelativeIndex_of_compact_open
    (F : Type) [Field F] [NumberField F]
    (U V : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUc : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hVo : IsOpen (V : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F) :
    (KPFiniteComponents.arithmeticStabilizer F V g).IsFiniteRelIndex
      (KPFiniteComponents.arithmeticStabilizer F U g) := by
  letI : IsTopologicalGroup (KPFiniteComponents.FinitePGL2 F) :=
    KPFiniteAdelicLatticeStabilizers.projective_topological_group F
  have h := KPFiniteAdelicLatticeStabilizers.open_finite_relative_index_compact U V hUc hVo
  exact (h.map (MulAut.conj g).toMonoidHom).comap (KPFiniteComponents.diagonal F)

theorem arithmeticStabilizer_properlyDiscontinuous_of_compact_open_comparison
    (F : Type) [Field F] [NumberField F]
    (U V : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUc : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hVo : IsOpen (V : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F)
    (hV : ProperlyDiscontinuousSMul (KPFiniteComponents.arithmeticStabilizer F V g)
      (KPArch.Space (KPCuspLogShape.dimension F))) :
    ProperlyDiscontinuousSMul (KPFiniteComponents.arithmeticStabilizer F U g)
      (KPArch.Space (KPCuspLogShape.dimension F)) := by
  letI : ContinuousConstSMul (KPCuspArithmetic.PGL2 F)
      (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨KPCuspSiegel.continuous_action F⟩
  letI := arithmeticStabilizer_finiteRelativeIndex_of_compact_open F U V hUc hVo g
  letI := hV
  exact ProperlyDiscontinuousSMul.ofFiniteRelIndex
    (KPFiniteComponents.arithmeticStabilizer F U g)
    (KPFiniteComponents.arithmeticStabilizer F V g)

theorem arithmeticStabilizer_properlyDiscontinuous_of_integral_lattice
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUc : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F)
    (hL : ProperlyDiscontinuousSMul (KPFiniteComponents.projectiveIdealAut F 1)
      (KPArch.Space (KPCuspLogShape.dimension F))) :
    ProperlyDiscontinuousSMul (KPFiniteComponents.arithmeticStabilizer F U g)
      (KPArch.Space (KPCuspLogShape.dimension F)) := by
  letI : ContinuousConstSMul (KPCuspArithmetic.PGL2 F)
      (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨KPCuspSiegel.continuous_action F⟩
  have hI : ProperlyDiscontinuousSMul
      (KPFiniteComponents.arithmeticStabilizer F (KPFiniteComponents.integralCompact F) 1)
      (KPArch.Space (KPCuspLogShape.dimension F)) := by
    letI := KPFiniteAdelicLatticeStabilizers.StabilizerClassRaw.standard_stabilizer_identity_finite_index F
    letI : ProperlyDiscontinuousSMul (KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F 1)
        (KPArch.Space (KPCuspLogShape.dimension F)) := hL
    exact ProperlyDiscontinuousSMul.ofFiniteRelIndex
      (KPFiniteAdelicLatticeStabilizers.levelStabilizer F (KPFiniteAdelicLatticeStabilizers.integralPG F) 1)
      (KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F 1)
  have hK : ProperlyDiscontinuousSMul
      (KPFiniteComponents.arithmeticStabilizer F (KPFiniteComponents.integralCompact F) g)
      (KPArch.Space (KPCuspLogShape.dimension F)) :=
    (KPFiniteAdelicLatticeStabilizers.standard_stabilizers_commensurable_identity F g).properlyDiscontinuousSMul_iff.mpr hI
  exact arithmeticStabilizer_properlyDiscontinuous_of_compact_open_comparison F U
    (KPFiniteComponents.integralCompact F) hUc
    (KPFiniteAdelicLatticeStabilizers.integralPG_compact_open F).2 g hK

variable {F : Type} [Field F] [NumberField F]
def matrixCoefficients (A : GL (Fin 2) F) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → F :=
  fun i j k l => A.val i j * A⁻¹.val k l
lemma matrixCoefficients_eq_of_mk_eq (A B : GL (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    matrixCoefficients A = matrixCoefficients B := by
  obtain ⟨u, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  funext i j k l
  simp only [matrixCoefficients, mul_inv_rev, ← map_inv, Units.val_mul,
    Matrix.GeneralLinearGroup.coe_scalar]
  simp [Matrix.mul_apply, Matrix.scalar, Matrix.diagonal, mul_assoc]

def projectiveCoefficients (q : KPCuspArithmetic.PGL2 F) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → F :=
  matrixCoefficients (Classical.choose (Matrix.ProjGenLinGroup.mk_surjective q))
lemma projectiveCoefficients_mk (A : GL (Fin 2) F) :
    projectiveCoefficients (Matrix.ProjGenLinGroup.mk A) = matrixCoefficients A :=
  matrixCoefficients_eq_of_mk_eq _ _ (Classical.choose_spec (Matrix.ProjGenLinGroup.mk_surjective _))
lemma projectiveCoefficients_injective : Function.Injective (projectiveCoefficients (F := F)) := by
  intro q r h
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective q
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective r
  rw [projectiveCoefficients_mk, projectiveCoefficients_mk] at h
  have hAB : ∀ i j k l, A.val i j * A⁻¹.val k l = B.val i j * B⁻¹.val k l :=
    fun i j k l => congrFun (congrFun (congrFun (congrFun h i) j) k) l
  have hn : ∃ k l, A⁻¹.val k l ≠ 0 := by
    by_contra hh
    have hz : A⁻¹.val = 0 := by ext k l; simpa using not_exists.mp (not_exists.mp hh k) l
    exact A⁻¹.det_ne_zero (by rw [hz]; simp)
  obtain ⟨k, l, hkl⟩ := hn
  have hnB : B⁻¹.val k l ≠ 0 := by
    intro hz
    have hzA : A.val = 0 := by
      ext i j
      exact (mul_eq_zero.mp (by simpa [hz] using hAB i j k l)).resolve_right hkl
    exact A.det_ne_zero (by rw [hzA]; simp)
  let u : Fˣ := Units.mk0 (A⁻¹.val k l / B⁻¹.val k l) (div_ne_zero hkl hnB)
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨u, ?_⟩
  apply Units.ext
  ext i j
  change (A.val * (Matrix.GeneralLinearGroup.scalar (Fin 2) u).val) i j = B.val i j
  simp only [Matrix.GeneralLinearGroup.coe_scalar]
  change ((A.val * Matrix.diagonal (fun _ : Fin 2 => (u : F))) : Matrix (Fin 2) (Fin 2) F) i j = B.val i j
  rw [Matrix.mul_diagonal]
  change A.val i j * (A⁻¹.val k l / B⁻¹.val k l) = B.val i j
  rw [← mul_div_assoc, div_eq_iff hnB]
  exact hAB i j k l
lemma projectiveCoefficients_integral (q : KPFiniteComponents.projectiveIdealAut F 1)
    (i j k l : Fin 2) : IsIntegral ℤ (projectiveCoefficients q.val i j k l) := by
  obtain ⟨A, hA, hq⟩ := Subgroup.mem_map.mp q.property
  rw [← hq, projectiveCoefficients_mk]
  obtain ⟨a, ha⟩ := KPFiniteAdelicLatticeStabilizers.rational_stabilizer_entries F A hA i j
  obtain ⟨b, hb⟩ := KPFiniteAdelicLatticeStabilizers.rational_stabilizer_entries F A⁻¹
    ((MulAction.stabilizer (KPFiniteAdelicLatticeStabilizers.RationalGL F)
      (KPFiniteAdelicLatticeStabilizers.idealVectors F 1)).inv_mem hA) k l
  change IsIntegral ℤ (A.val i j * A⁻¹.val k l)
  rw [← ha, ← hb]
  exact a.isIntegral_coe.mul b.isIntegral_coe

lemma finite_projectiveCoefficients_bounded (B : ℝ) :
    {q : KPFiniteComponents.projectiveIdealAut F 1 |
      ∀ (φ : F →+* ℂ) i j k l, ‖φ (projectiveCoefficients q.val i j k l)‖ ≤ B}.Finite := by
  let S : Set F := {a | IsIntegral ℤ a ∧ ∀ φ : F →+* ℂ, ‖φ a‖ ≤ B}
  have hS : S.Finite := NumberField.Embeddings.finite_of_norm_le F ℂ B
  have hfun : {f : Fin 2 → Fin 2 → Fin 2 → Fin 2 → F |
      ∀ i j k l, f i j k l ∈ S}.Finite := by
    convert (show _ from
      (Set.Finite.pi fun _ : Fin 2 => Set.Finite.pi fun _ : Fin 2 =>
        Set.Finite.pi fun _ : Fin 2 => Set.Finite.pi fun _ : Fin 2 => hS)) using 1
    ext f
    simp [Set.mem_pi]
  apply Set.Finite.of_finite_image (f := fun q => projectiveCoefficients q.val)
  · apply hfun.subset
    rintro _ ⟨q, hq, rfl⟩ i j k l
    exact ⟨projectiveCoefficients_integral q i j k l, fun φ => hq φ i j k l⟩
  · exact fun _ _ _ _ h => Subtype.ext (projectiveCoefficients_injective h)
lemma embeddings_bound_of_complexPlaces (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    {x : F} {B : ℝ}
    (hx : ∀ i, ‖(KPCusp.complexPlace F i).embedding x‖ ≤ B) :
    ∀ φ : F →+* ℂ, ‖φ x‖ ≤ B := by
  intro φ
  let w := NumberField.InfinitePlace.mk φ
  haveI : IsEmpty {v : NumberField.InfinitePlace F // v.IsReal} :=
    Fintype.card_eq_zero_iff.mp hF
  have hw : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp
    (fun h => isEmptyElim (⟨w, h⟩ : {v : NumberField.InfinitePlace F // v.IsReal}))
  let i := Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex} ⟨w, hw⟩
  have hi : KPCusp.complexPlace F i = w :=
    congrArg Subtype.val ((Fintype.equivFin
      {v : NumberField.InfinitePlace F // v.IsComplex}).symm_apply_apply ⟨w, hw⟩)
  simpa [hi, NumberField.InfinitePlace.norm_embedding_eq, w] using hx i

lemma finite_projectiveCoefficients_complex_bounded
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) (B : ℝ) :
    {q : KPFiniteComponents.projectiveIdealAut F 1 |
      ∀ v i j k l, ‖(KPCusp.complexPlace F v).embedding
        (projectiveCoefficients q.val i j k l)‖ ≤ B}.Finite := by
  apply (finite_projectiveCoefficients_bounded B).subset
  intro q hq φ i j k l
  exact embeddings_bound_of_complexPlaces hF (fun v => hq v i j k l) φ

lemma projectiveIdealAut_properlyDiscontinuous_of_coefficient_bound
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (hbound : ∀ (K L : Set (KPArch.Space (KPCuspLogShape.dimension F))),
      IsCompact K → IsCompact L → ∃ B : ℝ,
        ∀ q : KPFiniteComponents.projectiveIdealAut F 1,
          ((fun z => q • z) '' K ∩ L).Nonempty →
            ∀ v i j k l, ‖(KPCusp.complexPlace F v).embedding
              (projectiveCoefficients q.val i j k l)‖ ≤ B) :
    ProperlyDiscontinuousSMul (KPFiniteComponents.projectiveIdealAut F 1)
      (KPArch.Space (KPCuspLogShape.dimension F)) := by
  constructor
  intro K L hK hL
  obtain ⟨B, hB⟩ := hbound K L hK hL
  exact (finite_projectiveCoefficients_complex_bounded hF B).subset (fun q hq => hB q hq)

lemma bottom_left_entry_sq_bound (g : GL (Fin 2) ℂ) (z : KPArch.H3) :
    ‖g.val 1 0‖ ^ 2 ≤ ‖g.val.det‖ / (KPArch.height z * KPArch.height (KPArch.action g z)) := by
  have hz : 0 < KPArch.height z := Real.exp_pos _
  have hw : 0 < KPArch.height (KPArch.action g z) := Real.exp_pos _
  have hD := KPArch.actionDenominator_pos g z
  have he : KPArch.height (KPArch.action g z) * KPArch.actionDenominator g z =
      ‖g.val.det‖ * KPArch.height z := by
    rw [KPArch.action_height]
    exact div_mul_cancel₀ _ hD.ne'
  rw [le_div_iff₀ (mul_pos hz hw)]
  have h : ‖g.val 1 0‖ ^ 2 * KPArch.height z ^ 2 ≤ KPArch.actionDenominator g z := by
    unfold KPArch.actionDenominator
    exact le_add_of_nonneg_left (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right h hw.le]

lemma bottom_right_entry_sq_bound (g : GL (Fin 2) ℂ) (z : KPArch.H3) :
    ‖g.val 1 1‖ ^ 2 ≤
      (2 * KPArch.height z / KPArch.height (KPArch.action g z) +
        2 * ‖z.1‖ ^ 2 / (KPArch.height z * KPArch.height (KPArch.action g z))) * ‖g.val.det‖ := by
  have hz : 0 < KPArch.height z := Real.exp_pos _
  have hw : 0 < KPArch.height (KPArch.action g z) := Real.exp_pos _
  have hc := bottom_left_entry_sq_bound g z
  have hD := KPArch.actionDenominator_pos g z
  have he : KPArch.actionDenominator g z =
      ‖g.val.det‖ * KPArch.height z / KPArch.height (KPArch.action g z) := by
    apply (eq_div_iff hw.ne').mpr
    have ht := KPArch.action_height g z
    change KPArch.height (KPArch.action g z) = ‖g.val.det‖ * KPArch.height z / KPArch.actionDenominator g z at ht
    rw [eq_div_iff hD.ne'] at ht
    linarith
  have hnorm : ‖g.val 1 1‖ ≤ ‖g.val 1 0 * z.1 + g.val 1 1‖ + ‖g.val 1 0‖ * ‖z.1‖ := by
    calc
      ‖g.val 1 1‖ = ‖(g.val 1 0 * z.1 + g.val 1 1) - g.val 1 0 * z.1‖ := by congr 1; ring
      _ ≤ _ := by simpa [norm_mul] using norm_sub_le (g.val 1 0 * z.1 + g.val 1 1) (g.val 1 0 * z.1)
  have hsq : ‖g.val 1 1‖ ^ 2 ≤ 2 * ‖g.val 1 0 * z.1 + g.val 1 1‖ ^ 2 +
      2 * ‖g.val 1 0‖ ^ 2 * ‖z.1‖ ^ 2 := by
    have hs := mul_self_le_mul_self (norm_nonneg _) hnorm
    nlinarith [sq_nonneg (‖g.val 1 0 * z.1 + g.val 1 1‖ - ‖g.val 1 0‖ * ‖z.1‖)]
  have hden : ‖g.val 1 0 * z.1 + g.val 1 1‖ ^ 2 ≤ KPArch.actionDenominator g z := by
    unfold KPArch.actionDenominator
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  calc
    _ ≤ 2 * KPArch.actionDenominator g z +
        2 * (‖g.val.det‖ / (KPArch.height z * KPArch.height (KPArch.action g z))) * ‖z.1‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg ‖z.1‖)]
    _ = _ := by rw [he]; ring
def rowSwap : GL (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply],
    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply]⟩
lemma rowSwap_bottom (g : GL (Fin 2) ℂ) (j : Fin 2) :
    (rowSwap * g).val 1 j = g.val 0 j := by
  simp [rowSwap, Matrix.mul_apply]
lemma rowSwap_det_norm (g : GL (Fin 2) ℂ) :
    ‖(rowSwap * g).val.det‖ = ‖g.val.det‖ := by
  rw [Units.val_mul, Matrix.det_mul, norm_mul]
  simp [rowSwap, Matrix.det_fin_two]

def matrixEntryBound (z w : KPArch.H3) : ℝ :=
  let w' := KPArch.action rowSwap w
  max (1 / (KPArch.height z * KPArch.height w))
    (max (2 * KPArch.height z / KPArch.height w + 2 * ‖z.1‖ ^ 2 / (KPArch.height z * KPArch.height w))
    (max (1 / (KPArch.height z * KPArch.height w'))
    (2 * KPArch.height z / KPArch.height w' + 2 * ‖z.1‖ ^ 2 / (KPArch.height z * KPArch.height w'))))
lemma matrixEntryBound_nonneg (z w : KPArch.H3) : 0 ≤ matrixEntryBound z w := by
  exact le_trans (one_div_nonneg.mpr (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))) : 0 ≤ 1 / (KPArch.height z * KPArch.height w)) (le_max_left _ _)
lemma matrix_entry_sq_bound (g : GL (Fin 2) ℂ) (z : KPArch.H3) (i j : Fin 2) :
    ‖g.val i j‖ ^ 2 ≤ matrixEntryBound z (KPArch.action g z) * ‖g.val.det‖ := by
    let w := KPArch.action g z
    let w' := KPArch.action rowSwap w
    let C := matrixEntryBound z w
    have h0 := bottom_left_entry_sq_bound g z
    have h1 := bottom_right_entry_sq_bound g z
    have h2 := bottom_left_entry_sq_bound (rowSwap * g) z
    have h3 := bottom_right_entry_sq_bound (rowSwap * g) z
    rw [rowSwap_bottom, rowSwap_det_norm, (KPArch.action_laws rowSwap g z).2] at h2 h3
    have hd : 0 ≤ ‖g.val.det‖ := norm_nonneg _
    have c0 : 1 / (KPArch.height z * KPArch.height w) ≤ C := le_max_left _ _
    have c1 : 2 * KPArch.height z / KPArch.height w + 2 * ‖z.1‖ ^ 2 / (KPArch.height z * KPArch.height w) ≤ C :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have c2 : 1 / (KPArch.height z * KPArch.height w') ≤ C :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have c3 : 2 * KPArch.height z / KPArch.height w' + 2 * ‖z.1‖ ^ 2 / (KPArch.height z * KPArch.height w') ≤ C :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    fin_cases i <;> fin_cases j
    · exact le_trans (by simpa [w', w, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h2) (mul_le_mul_of_nonneg_right c2 hd)
    · exact le_trans h3 (mul_le_mul_of_nonneg_right c3 hd)
    · exact le_trans (by simpa [w, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h0) (mul_le_mul_of_nonneg_right c0 hd)
    · exact le_trans h1 (mul_le_mul_of_nonneg_right c1 hd)
lemma continuous_matrixEntryBound : Continuous (fun p : KPArch.H3 × KPArch.H3 => matrixEntryBound p.1 p.2) := by
  have hz : Continuous (fun p : KPArch.H3 × KPArch.H3 => KPArch.height p.1) := Real.continuous_exp.comp (continuous_snd.comp continuous_fst)
  have hw : Continuous (fun p : KPArch.H3 × KPArch.H3 => KPArch.height p.2) := Real.continuous_exp.comp (continuous_snd.comp continuous_snd)
  have hw' : Continuous (fun p : KPArch.H3 × KPArch.H3 => KPArch.height (KPArch.action rowSwap p.2)) :=
    Real.continuous_exp.comp (continuous_snd.comp ((KPCuspSiegel.continuous_arch_action rowSwap).comp continuous_snd))
  have hn : Continuous (fun p : KPArch.H3 × KPArch.H3 => ‖p.1.1‖ ^ 2) := (continuous_fst.comp continuous_fst).norm.pow 2
  have hzw : ∀ p : KPArch.H3 × KPArch.H3, KPArch.height p.1 * KPArch.height p.2 ≠ 0 := fun p =>
    mul_ne_zero (Real.exp_pos _).ne' (Real.exp_pos _).ne'
  have hzw' : ∀ p : KPArch.H3 × KPArch.H3, KPArch.height p.1 * KPArch.height (KPArch.action rowSwap p.2) ≠ 0 := fun p =>
    mul_ne_zero (Real.exp_pos _).ne' (Real.exp_pos _).ne'
  exact (continuous_const.div (hz.mul hw) hzw).max
    ((((continuous_const.mul hz).div hw (fun _ => (Real.exp_pos _).ne')).add
      ((continuous_const.mul hn).div (hz.mul hw) hzw)).max
      ((continuous_const.div (hz.mul hw') hzw').max
        (((continuous_const.mul hz).div hw' (fun _ => (Real.exp_pos _).ne')).add
          ((continuous_const.mul hn).div (hz.mul hw') hzw'))))

lemma matrixCoefficients_complex_bound (g : GL (Fin 2) ℂ) (z : KPArch.H3) (i j k l : Fin 2) :
    ‖g.val i j * g⁻¹.val k l‖ ≤
      matrixEntryBound z (KPArch.action g z) * matrixEntryBound (KPArch.action g z) z + 1 := by
  let w := KPArch.action g z
  have hgz : KPArch.action g⁻¹ w = z := by
    rw [← (KPArch.action_laws g⁻¹ g z).2, inv_mul_cancel, (KPArch.action_laws g g z).1]
  have h0 := matrix_entry_sq_bound g z i j
  have h1 := matrix_entry_sq_bound g⁻¹ w k l
  rw [hgz] at h1
  have hd : ‖g.val.det‖ * ‖g⁻¹.val.det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul]
    change ‖(g * g⁻¹).val.det‖ = 1
    simp
  have hmul := mul_le_mul h0 h1 (sq_nonneg _) (mul_nonneg (matrixEntryBound_nonneg _ _) (norm_nonneg _))
  have hs : ‖g.val i j * g⁻¹.val k l‖ ^ 2 ≤ matrixEntryBound z w * matrixEntryBound w z := by
    calc
      _ = ‖g.val i j‖ ^ 2 * ‖g⁻¹.val k l‖ ^ 2 := by rw [norm_mul, mul_pow]
      _ ≤ _ := hmul.trans_eq (by calc
        _ = (matrixEntryBound z w * matrixEntryBound w z) * (‖g.val.det‖ * ‖g⁻¹.val.det‖) := by ring
        _ = _ := by rw [hd, mul_one])
  have hC : 0 ≤ matrixEntryBound z w * matrixEntryBound w z := mul_nonneg (matrixEntryBound_nonneg _ _) (matrixEntryBound_nonneg _ _)
  nlinarith [sq_nonneg (‖g.val i j * g⁻¹.val k l‖ - 1)]
lemma projectiveIdealAut_properlyDiscontinuous (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) :
    ProperlyDiscontinuousSMul (KPFiniteComponents.projectiveIdealAut F 1)
      (KPArch.Space (KPCuspLogShape.dimension F)) := by
  apply projectiveIdealAut_properlyDiscontinuous_of_coefficient_bound hF
  intro K L hK hL
  let f : (KPArch.Space (KPCuspLogShape.dimension F) × KPArch.Space (KPCuspLogShape.dimension F)) → ℝ :=
    fun p => ∑ v, (matrixEntryBound (p.1 v) (p.2 v) * matrixEntryBound (p.2 v) (p.1 v) + 1)
  have hf : Continuous f := by
    apply continuous_finset_sum
    intro v hv
    have hzw : Continuous (fun p : KPArch.Space (KPCuspLogShape.dimension F) × KPArch.Space (KPCuspLogShape.dimension F) => (p.1 v, p.2 v)) :=
      ((continuous_apply v).comp continuous_fst).prodMk ((continuous_apply v).comp continuous_snd)
    have hwz : Continuous (fun p : KPArch.Space (KPCuspLogShape.dimension F) × KPArch.Space (KPCuspLogShape.dimension F) => (p.2 v, p.1 v)) :=
      ((continuous_apply v).comp continuous_snd).prodMk ((continuous_apply v).comp continuous_fst)
    exact ((continuous_matrixEntryBound.comp hzw).mul (continuous_matrixEntryBound.comp hwz)).add continuous_const
  obtain ⟨B, hB⟩ := (hK.prod hL).bddAbove_image hf.continuousOn
  refine ⟨B, ?_⟩
  intro q hq v i j k l
  obtain ⟨w, ⟨⟨z, hz, rfl⟩, hw⟩⟩ := hq
  obtain ⟨A, hA, hqA⟩ := Subgroup.mem_map.mp q.property
  let Av := Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F v).embedding A
  have hact : (q • z) v = KPArch.action Av (z v) := by
    change KPCuspSiegel.action F q.val z v = _
    rw [← hqA, KPCuspSiegel.action_mk]
    rfl
  have hcoeff : (KPCusp.complexPlace F v).embedding (projectiveCoefficients q.val i j k l) =
      Av.val i j * Av⁻¹.val k l := by
    rw [← hqA, projectiveCoefficients_mk]
    simp [matrixCoefficients, Av, ← map_inv]
  rw [hcoeff]
  calc
    _ ≤ matrixEntryBound (z v) ((q • z) v) * matrixEntryBound ((q • z) v) (z v) + 1 := by
      rw [hact]
      exact matrixCoefficients_complex_bound Av (z v) i j k l
    _ ≤ f (z, q • z) := by
      apply Finset.single_le_sum (fun v hv => ?_) (Finset.mem_univ v)
      exact add_nonneg (mul_nonneg (matrixEntryBound_nonneg _ _) (matrixEntryBound_nonneg _ _)) zero_le_one
    _ ≤ B := hB ⟨(z, q • z), ⟨hz, hw⟩, rfl⟩

theorem arithmeticStabilizer_properlyDiscontinuous_of_compact
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUc : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F) :
    ProperlyDiscontinuousSMul (KPFiniteComponents.arithmeticStabilizer F U g)
      (KPArch.Space (KPCuspLogShape.dimension F)) := by
  exact arithmeticStabilizer_properlyDiscontinuous_of_integral_lattice F U hUc g
    (projectiveIdealAut_properlyDiscontinuous F hF)

end DedekindZetaZeroFree.KPFiniteAdelicCuspEnds.FundamentalDomainGeometry

end

end

section

noncomputable section
open scoped Classical NumberField
open MeasureTheory

namespace DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

theorem arithmeticStabilizer_countable
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F)) (g : KPFiniteComponents.FinitePGL2 F) :
    Countable (KPFiniteComponents.arithmeticStabilizer F U g) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F); infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) :=
    Function.Surjective.countable Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

theorem canonicalAction_continuousConstSMul (F : Type) [Field F] [NumberField F] :
    ContinuousConstSMul (KPCuspArithmetic.PGL2 F)
      (KPArch.Space (KPCuspLogShape.dimension F)) :=
  ⟨fun g => by
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have h : (fun z : KPArch.Space (KPCuspLogShape.dimension F) =>
        Matrix.ProjGenLinGroup.mk A • z) = fun z => KPArch.productAction _
          (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A) z := by
      funext z
      rw [show Matrix.ProjGenLinGroup.mk A • z =
        KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk A) z from rfl,
        KPCuspSiegel.action_mk]
      rfl
    rw [h]
    exact (KPArch.productAction_contDiff _
      (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A)).continuous⟩

theorem arithmeticStabilizer_continuousConstSMul
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F)) (g : KPFiniteComponents.FinitePGL2 F) :
    ContinuousConstSMul (KPFiniteComponents.arithmeticStabilizer F U g)
      (KPArch.Space (KPCuspLogShape.dimension F)) := by
  letI := canonicalAction_continuousConstSMul F
  exact ⟨fun γ => continuous_const_smul (Γ := KPCuspArithmetic.PGL2 F) γ.val⟩

theorem arithmeticStabilizer_ae_free_of_null_fixed_loci
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F)) (g : KPFiniteComponents.FinitePGL2 F)
    (hfixed : ∀ γ : KPFiniteComponents.arithmeticStabilizer F U g, γ ≠ 1 →
      (volume : Measure (KPArch.Space (KPCuspLogShape.dimension F)))
        {x | γ • x = x} = 0) :
    ∀ᵐ x ∂KPArch.hyperbolicVolume (KPCuspLogShape.dimension F),
      ∀ γ : KPFiniteComponents.arithmeticStabilizer F U g, γ • x = x → γ = 1 := by
  letI := arithmeticStabilizer_countable F U g
  apply ae_all_iff.mpr
  intro γ
  by_cases hγ : γ = 1
  · exact Filter.Eventually.of_forall fun _ _ => hγ
  · have hn : KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
        {x | γ • x = x} = 0 :=
      withDensity_absolutelyContinuous _ _ (hfixed γ hγ)
    filter_upwards [show ∀ᵐ x ∂KPArch.hyperbolicVolume (KPCuspLogShape.dimension F),
        ¬ γ • x = x from by simpa only [ae_iff, not_not] using hn] with x hx
    exact fun heq => (hx heq).elim

theorem finite_adelic_component_fundamental_domain_of_properlyDiscontinuous_ae_free
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F)) (g : KPFiniteComponents.FinitePGL2 F)
    (hproper : ProperlyDiscontinuousSMul (KPFiniteComponents.arithmeticStabilizer F U g)
      (KPArch.Space (KPCuspLogShape.dimension F)))
    (hfree : ∀ᵐ x ∂KPArch.hyperbolicVolume (KPCuspLogShape.dimension F),
      ∀ γ : KPFiniteComponents.arithmeticStabilizer F U g, γ • x = x → γ = 1) :
    ∃ A : Set (KPArch.Space (KPCuspLogShape.dimension F)), MeasurableSet A ∧
      IsFundamentalDomain (KPFiniteComponents.arithmeticStabilizer F U g) A
        (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) := by
  letI := arithmeticStabilizer_countable F U g
  letI := canonicalAction_continuousConstSMul F
  letI : ContinuousConstSMul (KPFiniteComponents.arithmeticStabilizer F U g)
      (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨fun γ => continuous_const_smul (γ : KPCuspArithmetic.PGL2 F)⟩
  letI := hproper
  exact KPCuspChart.SectionConstruction.measurable_fundamental_domain_of_properly_discontinuous_ae_free
    _ hfree

theorem finite_adelic_component_fundamental_domain
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUc : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hUo : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F) :
    ∃ A : Set (KPArch.Space (KPCuspLogShape.dimension F)),
      MeasurableSet A ∧
      IsFundamentalDomain (KPFiniteComponents.arithmeticStabilizer F U g) A
        (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) := by
  apply finite_adelic_component_fundamental_domain_of_properlyDiscontinuous_ae_free F U g
  · exact FundamentalDomainGeometry.arithmeticStabilizer_properlyDiscontinuous_of_compact
      F hF U hUc g
  · apply arithmeticStabilizer_ae_free_of_null_fixed_loci F U g
    intro γ hγ
    have hγval : (γ : KPCuspArithmetic.PGL2 F) ≠ 1 := by
      intro heq
      apply hγ
      exact Subtype.ext heq
    exact FundamentalDomainGeometry.rationalProjective_fixed_locus_volume_zero
      F (KPCuspLogShape.dimension_pos F hF) γ.val hγval

end DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

end

end
