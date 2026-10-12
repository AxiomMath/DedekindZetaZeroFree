module

public import DedekindZetaZeroFree.Geometry.HyperbolicActionMetricAndVolume
public import DedekindZetaZeroFree.Adeles.Quotients.PGL2CuspParabolicStabilizers

@[expose] public section

namespace DedekindZetaZeroFree.KPArithmeticAction

noncomputable section
open scoped MatrixGroups Pointwise
open NumberField

instance projectiveTopology : TopologicalSpace PGL(2, ℂ) := by
  unfold Matrix.ProjGenLinGroup
  infer_instance

instance hyperbolicGLAction : MulAction (GL (Fin 2) ℂ) KPArch.H3 where
  smul := KPArch.action
  one_smul z := (KPArch.action_laws 1 1 z).1
  mul_smul g h z := (KPArch.action_laws g h z).2

instance hyperbolicProjectiveAction : MulAction PGL(2, ℂ) KPArch.H3 :=
  Matrix.ProjGenLinGroup.mulActionOfGL KPArch.scalar_action

abbrev ProjectiveGroup (d : ℕ) := Fin d → PGL(2, ℂ)

instance productProjectiveAction (d : ℕ) : MulAction (ProjectiveGroup d) (KPArch.Space d) where
  smul g z := fun i => g i • z i
  one_smul z := by
    funext i
    change (1 : PGL(2, ℂ)) • z i = z i
    exact one_smul _ _
  mul_smul g h z := by
    funext i
    change (g i * h i) • z i = g i • (h i • z i)
    exact mul_smul _ _ _

instance projectiveTopologicalGroup : IsTopologicalGroup PGL(2, ℂ) :=
  inferInstanceAs (IsTopologicalGroup
    (GL (Fin 2) ℂ ⧸ Subgroup.center (GL (Fin 2) ℂ)))

instance projectiveT2 : T2Space PGL(2, ℂ) := by
  have he : (Subgroup.center (GL (Fin 2) ℂ) : Set (GL (Fin 2) ℂ)) =
      ⋂ g : GL (Fin 2) ℂ, {h | g * h = h * g} := by
    ext h
    simp [Subgroup.mem_center_iff]
  haveI : IsClosed (Subgroup.center (GL (Fin 2) ℂ) : Set (GL (Fin 2) ℂ)) := by
    rw [he]
    exact isClosed_iInter (fun g => isClosed_eq (continuous_const.mul continuous_id)
      (continuous_id.mul continuous_const))
  exact inferInstanceAs (T2Space (GL (Fin 2) ℂ ⧸ Subgroup.center (GL (Fin 2) ℂ)))

instance productContinuousConstSMul (d : ℕ) :
    ContinuousConstSMul (ProjectiveGroup d) (KPArch.Space d) where
  continuous_const_smul g := by
    classical
    choose h hh using fun i => Matrix.ProjGenLinGroup.mk_surjective (g i)
    have hg : g = fun i => Matrix.ProjGenLinGroup.mk (h i) := by
      funext i
      exact (hh i).symm
    rw [hg]
    exact (KPArch.productAction_contDiff d h).continuous

section HyperbolicProperAction

set_option maxHeartbeats 1000000

open Matrix

open scoped Matrix.Norms.Operator

def hyperbolicGLSection (z : KPArch.H3) : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![(KPArch.height z : ℂ), z.1; 0, 1] (by
    simpa [Matrix.det_fin_two, KPArch.height] using (Real.exp_ne_zero z.2))

theorem hyperbolicGLSection_action (z : KPArch.H3) :
    KPArch.action (hyperbolicGLSection z) (0, 0) = z := by
  ext
  · simp [KPArch.action, KPArch.actionDenominator, KPArch.height, hyperbolicGLSection]
  · simp [KPArch.action, KPArch.actionDenominator, KPArch.height, hyperbolicGLSection,
      Matrix.det_fin_two, abs_of_pos (Real.exp_pos _)]

theorem hyperbolicGLAction_continuous :
    Continuous (fun p : GL (Fin 2) ℂ × KPArch.H3 => KPArch.action p.1 p.2) := by
  have hc (i j : Fin 2) : Continuous (fun p : GL (Fin 2) ℂ × KPArch.H3 => p.1 i j) :=
    (Units.continuous_val.comp continuous_fst).matrix_elem i j
  have hh : Continuous (fun p : GL (Fin 2) ℂ × KPArch.H3 => KPArch.height p.2) := by
    unfold KPArch.height
    fun_prop
  have hd : Continuous (fun p : GL (Fin 2) ℂ × KPArch.H3 =>
      KPArch.actionDenominator p.1 p.2) := by
    unfold KPArch.actionDenominator
    fun_prop
  have hn : ∀ p : GL (Fin 2) ℂ × KPArch.H3,
      KPArch.actionDenominator p.1 p.2 ≠ 0 :=
    fun p => ne_of_gt (KPArch.actionDenominator_pos p.1 p.2)
  apply Continuous.prodMk
  · exact (((hc 0 0 |>.mul continuous_snd.fst |>.add (hc 0 1)).mul
      (hc 1 0 |>.mul continuous_snd.fst |>.add (hc 1 1)).star).add
        (((hc 0 0).mul (hc 1 0).star).mul (Complex.continuous_ofReal.comp (hh.pow 2)))).div
          (Complex.continuous_ofReal.comp hd) (fun p => by exact_mod_cast hn p)
  · have hp : ∀ p : GL (Fin 2) ℂ × KPArch.H3,
        ‖(p.1 : Matrix (Fin 2) (Fin 2) ℂ).det‖ * KPArch.height p.2 /
          KPArch.actionDenominator p.1 p.2 ≠ 0 := by
      intro p
      exact ne_of_gt (div_pos (mul_pos (norm_pos_iff.mpr p.1.det_ne_zero)
        (Real.exp_pos _)) (KPArch.actionDenominator_pos p.1 p.2))
    exact ((((Units.continuous_val.comp continuous_fst).matrix_det).norm.mul hh).div hd hn).log hp

instance hyperbolicContinuousSMul : @ContinuousSMul PGL(2, ℂ) KPArch.H3
    hyperbolicProjectiveAction.toSMul projectiveTopology inferInstance where
  continuous_smul := by
    apply ((QuotientGroup.isOpenQuotientMap_mk
      (N := Subgroup.center (GL (Fin 2) ℂ))).prodMap
        IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr
    exact hyperbolicGLAction_continuous

instance hyperbolicPretransitive : MulAction.IsPretransitive PGL(2, ℂ) KPArch.H3 where
  exists_smul_eq x y := by
    refine ⟨Matrix.ProjGenLinGroup.mk (hyperbolicGLSection y) *
      (Matrix.ProjGenLinGroup.mk (hyperbolicGLSection x))⁻¹, ?_⟩
    rw [mul_smul]
    have hx : Matrix.ProjGenLinGroup.mk (hyperbolicGLSection x) • (0, 0) = x :=
      hyperbolicGLSection_action x
    conv_lhs => arg 2; arg 2; rw [← hx]
    rw [inv_smul_smul]
    exact hyperbolicGLSection_action y

instance productContinuousSMul (d : ℕ) : ContinuousSMul (ProjectiveGroup d) (KPArch.Space d) where
  continuous_smul := by
    apply continuous_pi
    intro i
    exact continuous_smul.comp ((continuous_apply i |>.comp continuous_fst).prodMk
      (continuous_apply i |>.comp continuous_snd))

private theorem row_det_identity (a b c d : ℂ) :
    ‖a * d - b * c‖ ^ 2 = (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) -
      ‖a * star c + b * star d‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

 theorem origin_fixed_row (g : GL (Fin 2) ℂ) (h : KPArch.action g (0, 0) = (0, 0)) :
    (‖g 0 0‖ ^ 2 + ‖g 0 1‖ ^ 2 = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖) ∧
    (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖) := by
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
    have he := (div_eq_one_iff_eq (by nlinarith : ‖g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * 1 ^ 2 ≠ 0)).mp hh
    nlinarith
  have hn := congrArg Prod.fst h
  have hz : g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1) = 0 := by
    simp only [KPArch.action, KPArch.actionDenominator, KPArch.height, Real.exp_zero,
      mul_zero, zero_add, one_pow, Complex.ofReal_one, mul_one] at hn
    have hh : (‖g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 : ℝ) ≠ 0 := by linarith
    simpa only [add_comm] using
      (div_eq_zero_iff).mp hn |>.resolve_right (by exact_mod_cast hh)
  refine ⟨?_, hb⟩
  have hi := row_det_identity (g 0 0) (g 0 1) (g 1 0) (g 1 1)
  rw [← Matrix.det_fin_two, hz, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, hb] at hi
  have hp : 0 < ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := norm_pos_iff.mpr g.det_ne_zero
  nlinarith

def normalizedMatrixSet : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {A | ‖A.det‖ = 1 ∧ ∀ i j, ‖A i j‖ ≤ 1}

private theorem normalizedMatrixSet_compact : IsCompact normalizedMatrixSet := by
  have hc : IsClosed normalizedMatrixSet := by
    unfold normalizedMatrixSet
    apply IsClosed.inter
    · exact isClosed_eq continuous_id.matrix_det.norm continuous_const
    · have he : {A : Matrix (Fin 2) (Fin 2) ℂ | ∀ i j, ‖A i j‖ ≤ 1} =
          ⋂ i : Fin 2, ⋂ j : Fin 2, {A : Matrix (Fin 2) (Fin 2) ℂ | ‖A i j‖ ≤ 1} := by
        ext A
        simp
      change IsClosed {A : Matrix (Fin 2) (Fin 2) ℂ | ∀ i j, ‖A i j‖ ≤ 1}
      rw [he]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le ((show Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => A i j) from continuous_id.matrix_elem i j).norm)
          continuous_const
  apply (isCompact_pi_infinite fun _ : Fin 2 =>
    isCompact_pi_infinite fun _ : Fin 2 => isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hc
  intro A hA i j
  simpa [Metric.mem_closedBall, dist_zero_right] using hA.2 i j

def normalizedMatrixGL (A : normalizedMatrixSet) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A (by
    have h := A.property.1
    exact norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero))

private theorem normalizedMatrixGL_continuous : Continuous normalizedMatrixGL := by
  apply Units.isOpenEmbedding_val.isEmbedding.isInducing.continuous_iff.mpr
  exact continuous_subtype_val

 theorem normalized_representative (g : GL (Fin 2) ℂ)
    (h : KPArch.action g (0, 0) = (0, 0)) :
    ∃ A : normalizedMatrixSet, Matrix.ProjGenLinGroup.mk (normalizedMatrixGL A) =
      Matrix.ProjGenLinGroup.mk g := by
  let t := Real.sqrt ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖
  have ht : 0 < t := Real.sqrt_pos.mpr (norm_pos_iff.mpr g.det_ne_zero)
  have ht2 : t ^ 2 = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := Real.sq_sqrt (norm_nonneg _)
  let u : ℂˣ := Units.mk0 (t⁻¹ : ℂ) (by exact_mod_cast inv_ne_zero (ne_of_gt ht))
  let B : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.scalar (Fin 2) u * g
  have he (i j : Fin 2) : B i j = (t⁻¹ : ℂ) * g i j := by
    simp [B, Matrix.GeneralLinearGroup.scalar, Matrix.scalar, Matrix.mul_apply,
      Matrix.diagonal, u]
  have hn (i j : Fin 2) : ‖B i j‖ = t⁻¹ * ‖g i j‖ := by
    rw [he, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hd : (B : Matrix (Fin 2) (Fin 2) ℂ).det = (t⁻¹ : ℂ) ^ 2 *
      (g : Matrix (Fin 2) (Fin 2) ℂ).det := by
    simp only [Matrix.det_fin_two, he]
    ring
  have hd1 : ‖(B : Matrix (Fin 2) (Fin 2) ℂ).det‖ = 1 := by
    rw [hd, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, inv_pow, ← ht2]
    exact inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt ht))
  have hb (i j : Fin 2) : ‖B i j‖ ≤ 1 := by
    rw [hn]
    obtain ⟨hr0, hr1⟩ := origin_fixed_row g h
    have hg : ‖g i j‖ ≤ t := by
      fin_cases i <;> fin_cases j <;> norm_num only [Fin.isValue, Fin.mk_zero, Fin.mk_one] <;>
        nlinarith [sq_nonneg ‖g 0 0‖, sq_nonneg ‖g 0 1‖,
          sq_nonneg ‖g 1 0‖, sq_nonneg ‖g 1 1‖, norm_nonneg (g 0 0),
          norm_nonneg (g 0 1), norm_nonneg (g 1 0), norm_nonneg (g 1 1)]
    exact (inv_mul_le_iff₀ ht).mpr (by simpa using hg)
  refine ⟨⟨B, hd1, hb⟩, ?_⟩
  have hm : normalizedMatrixGL ⟨B, hd1, hb⟩ = B := Units.ext rfl
  rw [hm]
  simp [B, map_mul]

theorem hyperbolic_origin_stabilizer_compact :
    IsCompact (MulAction.stabilizer PGL(2, ℂ) ((0, 0) : KPArch.H3) : Set PGL(2, ℂ)) := by
  let f : normalizedMatrixSet → PGL(2, ℂ) :=
    fun A => Matrix.ProjGenLinGroup.mk (normalizedMatrixGL A)
  have hf : Continuous f := QuotientGroup.continuous_mk.comp normalizedMatrixGL_continuous
  letI : CompactSpace normalizedMatrixSet := isCompact_iff_compactSpace.mp normalizedMatrixSet_compact
  have hfc : IsCompact (Set.range f) := isCompact_range hf
  have hc : IsClosed (MulAction.stabilizer PGL(2, ℂ) ((0, 0) : KPArch.H3) : Set PGL(2, ℂ)) :=
    isClosed_eq (continuous_id.smul continuous_const) continuous_const
  apply hfc.of_isClosed_subset hc
  intro g hg
  obtain ⟨a, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  exact normalized_representative a hg

theorem product_origin_stabilizer_compact (d : ℕ) :
    IsCompact (MulAction.stabilizer (ProjectiveGroup d)
      (fun _ => (0, 0) : KPArch.Space d) : Set (ProjectiveGroup d)) := by
  have he : (MulAction.stabilizer (ProjectiveGroup d)
      (fun _ => (0, 0) : KPArch.Space d) : Set (ProjectiveGroup d)) =
      {g | ∀ i : Fin d, g i ∈
        (MulAction.stabilizer PGL(2, ℂ) ((0, 0) : KPArch.H3) : Set PGL(2, ℂ))} := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Set.mem_setOf_eq]
    exact funext_iff
  rw [he]
  exact isCompact_pi_infinite fun _ : Fin d => hyperbolic_origin_stabilizer_compact

end HyperbolicProperAction

end
end DedekindZetaZeroFree.KPArithmeticAction

section

namespace DedekindZetaZeroFree.KPArithmeticAction

noncomputable section
open scoped MatrixGroups Pointwise
open NumberField

theorem productProjectiveAction_mk (d : ℕ)
    (g : Fin d → GL (Fin 2) ℂ) (z : KPArch.Space d) :
    (fun i => Matrix.ProjGenLinGroup.mk (g i)) • z = KPArch.productAction d g z := by
  rfl

abbrev factors (F : Type) [Field F] [NumberField F] := Fintype.card (InfinitePlace F)

def place (F : Type) [Field F] [NumberField F] (i : Fin (factors F)) : InfinitePlace F :=
  (Fintype.equivFin (InfinitePlace F)).symm i

def archProjectiveEmbedding (F : Type) [Field F] [NumberField F] :
    KPCuspArithmetic.PGL2 F →* ProjectiveGroup (factors F) where
  toFun g i := Matrix.ProjGenLinGroup.map (place F i).embedding g
  map_one' := by funext i; simp
  map_mul' g h := by funext i; simp

abbrev OrbitSpace (d : ℕ) (Γ : Subgroup (ProjectiveGroup d)) :=
  Quotient (MulAction.orbitRel Γ (KPArch.Space d))

def orbitProjection (d : ℕ) (Γ : Subgroup (ProjectiveGroup d)) :
    KPArch.Space d → OrbitSpace d Γ := Quotient.mk _

def localOrbitRel (d : ℕ) (Γ : Subgroup (ProjectiveGroup d))
    (z : KPArch.Space d) (U : Set (KPArch.Space d)) : Setoid U :=
  (MulAction.orbitRel (MulAction.stabilizer Γ z) (KPArch.Space d)).comap Subtype.val

structure OrbifoldChart (d : ℕ) (Γ : Subgroup (ProjectiveGroup d)) (z : KPArch.Space d) where
  neighborhood : Set (KPArch.Space d)
  isOpen : IsOpen neighborhood
  center_mem : z ∈ neighborhood
  finite_stabilizer : Finite (MulAction.stabilizer Γ z)
  invariant : ∀ g : MulAction.stabilizer Γ z,
    (fun w : KPArch.Space d => g • w) '' neighborhood = neighborhood
  separated : ∀ g : Γ,
    ((fun w : KPArch.Space d => g • w) '' neighborhood ∩ neighborhood).Nonempty →
      g ∈ MulAction.stabilizer Γ z
  image_open : IsOpen (orbitProjection d Γ '' neighborhood)
  quotientChart : Quotient (localOrbitRel d Γ z neighborhood) ≃ₜ
    (orbitProjection d Γ '' neighborhood)
  quotientChart_mk : ∀ w : neighborhood,
    (quotientChart (Quotient.mk _ w)).val = orbitProjection d Γ w.val

section HyperbolicProperAction
set_option maxHeartbeats 1000000
open Matrix
open scoped Matrix.Norms.Operator

theorem hyperbolicGLSection_continuous : Continuous hyperbolicGLSection := by
  apply Units.isOpenEmbedding_val.isEmbedding.isInducing.continuous_iff.mpr
  change Continuous (fun z : KPArch.H3 => !![(KPArch.height z : ℂ), z.1; 0, 1])
  unfold KPArch.height
  fun_prop

def hyperbolicProjectiveSection (z : KPArch.H3) : PGL(2, ℂ) :=
  Matrix.ProjGenLinGroup.mk (hyperbolicGLSection z)

theorem hyperbolicProjectiveSection_continuous : Continuous hyperbolicProjectiveSection :=
  QuotientGroup.continuous_mk.comp hyperbolicGLSection_continuous

def productProjectiveSection (d : ℕ) (z : KPArch.Space d) : ProjectiveGroup d :=
  fun i => hyperbolicProjectiveSection (z i)

theorem productProjectiveSection_continuous (d : ℕ) : Continuous (productProjectiveSection d) := by
  exact continuous_pi fun i => hyperbolicProjectiveSection_continuous.comp (continuous_apply i)

theorem productProjectiveSection_action (d : ℕ) (z : KPArch.Space d) :
    productProjectiveSection d z • (fun _ => (0, 0)) = z := by
  funext i
  exact hyperbolicGLSection_action (z i)

open Set in
open scoped Pointwise in
theorem compact_transporter_of_section {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace X] [MulAction G X]
    (o : X) (s : X → G) (hs : Continuous s) (ho : ∀ x, s x • o = x)
    (hH : IsCompact (MulAction.stabilizer G o : Set G))
    {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact {g : G | ((fun x => g • x) '' K ∩ L).Nonempty} := by
  have he : {g : G | ((fun x => g • x) '' K ∩ L).Nonempty} =
      (s '' L) * (MulAction.stabilizer G o : Set G) * (s '' K)⁻¹ := by
    ext g
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, hy⟩
      let h := (s (g • x))⁻¹ * g * s x
      have hfix : h ∈ MulAction.stabilizer G o := by
        change h • o = o
        simp only [h, mul_smul, ho]
        exact inv_smul_eq_iff.mpr (ho (g • x)).symm
      have hg : s (g • x) * h * (s x)⁻¹ = g := by
        simp [h, mul_assoc]
      rw [← hg]
      exact Set.mul_mem_mul (Set.mul_mem_mul (mem_image_of_mem s hy) hfix)
        (by simpa only [Set.mem_inv, inv_inv] using mem_image_of_mem s hx)
    · rintro ⟨a, ⟨b, ⟨y, hy, rfl⟩, h, hh, rfl⟩, c, hc, rfl⟩
      obtain ⟨x, hx, hxc⟩ := hc
      have he : c = (s x)⁻¹ := by
        exact inv_eq_iff_eq_inv.mp hxc.symm
      subst c
      refine ⟨y, ⟨x, hx, ?_⟩, hy⟩
      have hh' : h • o = o := hh
      calc
        (s y * h * (s x)⁻¹) • x = s y • (h • ((s x)⁻¹ • x)) := by simp [mul_smul]
        _ = s y • (h • o) := by rw [inv_smul_eq_iff.mpr (ho x).symm]
        _ = y := by rw [hh', ho]
  rw [he]
  exact ((hL.image hs).mul hH).mul (hK.image hs).inv

open Set in

theorem properlyDiscontinuous_of_section {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [TopologicalSpace X] [MulAction G X]
    (o : X) (s : X → G) (hs : Continuous s) (ho : ∀ x, s x • o = x)
    (hH : IsCompact (MulAction.stabilizer G o : Set G))
    (Γ : Subgroup G) [DiscreteTopology Γ] : ProperlyDiscontinuousSMul Γ X := by
  constructor
  intro K L hK hL
  let T : Set G := {g : G | ((fun x => g • x) '' K ∩ L).Nonempty}
  have hT : IsCompact T := compact_transporter_of_section o s hs ho hH hK hL
  have hΓ : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  have hf : (Subtype.val ⁻¹' T : Set Γ).Finite := by
    exact (Topology.IsClosedEmbedding.isCompact_preimage
      (show Topology.IsClosedEmbedding (Subtype.val : Γ → G) from hΓ.isClosedEmbedding_subtypeVal) hT).finite (isDiscrete_iff_discreteTopology.mpr inferInstance)
  exact hf

end HyperbolicProperAction

end
end DedekindZetaZeroFree.KPArithmeticAction

end
