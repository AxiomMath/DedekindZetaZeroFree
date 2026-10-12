module

public import DedekindZetaZeroFree.Metaplectic.Kubota.LocalCoverChartTopology
public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.CorrectionAndDeterminantTwist

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPStandardLocalRootLifts

noncomputable section
set_option autoImplicit false

def lowerN (K : Type*) [Field K] (t : K) : KubotaRankTwo.GL2 K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; t, 1] (by
    simp [Matrix.det_fin_two])

def weylSwap (K : Type*) [Field K] : KubotaRankTwo.GL2 K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by
    simp [Matrix.det_fin_two])

private theorem n_zero_matrix (K : Type*) [Field K] : KubotaRankTwo.n K 0 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.n]

private theorem n_add_matrix (K : Type*) [Field K] (t u : K) :
    KubotaRankTwo.n K t * KubotaRankTwo.n K u = KubotaRankTwo.n K (t + u) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, add_comm]

private theorem lower_zero_matrix (K : Type*) [Field K] : lowerN K 0 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lowerN]

private theorem lower_add_matrix (K : Type*) [Field K] (t u : K) :
    lowerN K t * lowerN K u = lowerN K (t + u) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lowerN, Matrix.mul_apply]

theorem d_mul_matrix (K : Type*) [Field K] (x y : Kˣ) :
    KubotaRankTwo.d K x 1 * KubotaRankTwo.d K y 1 = KubotaRankTwo.d K (x * y) 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

private theorem d_one_matrix (K : Type*) [Field K] : KubotaRankTwo.d K 1 1 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp

private theorem swap_sq_matrix (K : Type*) [Field K] : weylSwap K * weylSwap K = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [weylSwap, Matrix.mul_apply]

private theorem signed_sq_matrix (K : Type*) [Field K] :
    KubotaRankTwo.w K * KubotaRankTwo.w K = KubotaRankTwo.d K (-1) (-1) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

private theorem lower_det (K : Type*) [Field K] (t : K) : KubotaRankTwo.det K (lowerN K t) = 1 := by
  apply Units.ext
  simp [KubotaRankTwo.det, lowerN, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

private theorem swap_det (K : Type*) [Field K] : KubotaRankTwo.det K (weylSwap K) = -1 := by
  apply Units.ext
  simp [KubotaRankTwo.det, weylSwap, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

private theorem swap_X (K : Type*) [Field K] : KubotaRankTwo.X K (weylSwap K) = 1 := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, weylSwap]

private theorem lower_X (K : Type*) [Field K] (t : K) (ht : t ≠ 0) :
    KubotaRankTwo.X K (lowerN K t) = Units.mk0 t ht := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, lowerN, ht]

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : KPHilbert.Place F)

 theorem B_one_left (a : (KPHilbert.Completion F v)ˣ) :
    KPHilbert.B3 F ζ hζ v 1 a = 1 :=
  KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ v).1 a

private theorem B_one_right (a : (KPHilbert.Completion F v)ˣ) :
    KPHilbert.B3 F ζ hζ v a 1 = 1 :=
  KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1 a

private theorem section_one : KPLocalCover.sectionMap F ζ hζ v 1 = 1 := rfl

def N (t : KPHilbert.Completion F v) : KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPLocalCover.sectionMap F ζ hζ v (KubotaRankTwo.n (KPHilbert.Completion F v) t)

def LowerN (t : KPHilbert.Completion F v) : KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPLocalCover.sectionMap F ζ hζ v (lowerN (KPHilbert.Completion F v) t)

def A (y : (KPHilbert.Completion F v)ˣ) : KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPLocalCover.sectionMap F ζ hζ v (KubotaRankTwo.d (KPHilbert.Completion F v) y 1)

def W : KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPLocalCover.sectionMap F ζ hζ v (weylSwap (KPHilbert.Completion F v))

def signedW : KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPLocalCover.sectionMap F ζ hζ v (KubotaRankTwo.w (KPHilbert.Completion F v))

@[simp] theorem N_zero : N F ζ hζ v 0 = 1 := by
  simp only [N, n_zero_matrix, section_one]

theorem N_add (t u : KPHilbert.Completion F v) :
    N F ζ hζ v (t + u) = N F ζ hζ v t * N F ζ hζ v u := by
  have hs : KPLocalCover.sigmaTwo F ζ hζ v
      (KubotaRankTwo.n _ t) (KubotaRankTwo.n _ u) = 1 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
      n_add_matrix, B_one_left, B_one_right]
  rw [N, N, N, KPLocalCover.sectionMap_mul, hs, map_one, one_mul, n_add_matrix]

@[simp] theorem LowerN_zero : LowerN F ζ hζ v 0 = 1 := by
  simp only [LowerN, lower_zero_matrix, section_one]

theorem LowerN_add (t u : KPHilbert.Completion F v) :
    LowerN F ζ hζ v (t + u) = LowerN F ζ hζ v t * LowerN F ζ hζ v u := by
  by_cases ht : t = 0
  · subst t; simp
  by_cases hu : u = 0
  · subst u; simp
  have hs : KPLocalCover.sigmaTwo F ζ hζ v (lowerN _ t) (lowerN _ u) = 1 := by
    simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
      lower_add_matrix, lower_det, B_one_left, one_pow, mul_one, lower_X _ t ht,
      lower_X _ u hu]
    by_cases hz : t + u = 0
    · rw [hz, lower_zero_matrix, KubotaRankTwo.X_one]
      simp only [one_div, mul_one]
      rw [KubotaDefectSymbolAlgebra.inv_inv _ _ _
        (KPHilbert.B3_laws F ζ hζ v).1 (KPHilbert.B3_laws F ζ hζ v).2.1]
      have he : Units.mk0 u hu = -Units.mk0 t ht := by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_neg]
        exact eq_neg_of_add_eq_zero_right hz
      rw [he]
      exact ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 _).2.2
    · rw [lower_X _ (t + u) hz]
      have he : (Units.mk0 (t + u) hz / Units.mk0 t ht) =
          (Units.mk0 t ht / Units.mk0 (t + u) hz)⁻¹ := by simp [div_eq_mul_inv, mul_comm]
      have he' : (Units.mk0 (t + u) hz / Units.mk0 u hu) =
          (Units.mk0 u hu / Units.mk0 (t + u) hz)⁻¹ := by simp [div_eq_mul_inv, mul_comm]
      rw [he, he', KubotaDefectSymbolAlgebra.inv_inv _ _ _
        (KPHilbert.B3_laws F ζ hζ v).1 (KPHilbert.B3_laws F ζ hζ v).2.1]
      apply (KPHilbert.B3_laws F ζ hζ v).2.2.2.1
      simp only [Units.val_div_eq_div_val, Units.val_mk0]
      exact (add_div t u (t + u)).symm.trans (div_self hz)
  rw [LowerN, LowerN, LowerN, KPLocalCover.sectionMap_mul, hs, map_one,
    one_mul, lower_add_matrix]

def N_hom : Multiplicative (KPHilbert.Completion F v) →*
    KPLocalCover.CubicGL2Raw F ζ hζ v where
  toFun t := N F ζ hζ v t.toAdd
  map_one' := N_zero F ζ hζ v
  map_mul' t u := N_add F ζ hζ v t.toAdd u.toAdd

def LowerN_hom : Multiplicative (KPHilbert.Completion F v) →*
    KPLocalCover.CubicGL2Raw F ζ hζ v where
  toFun t := LowerN F ζ hζ v t.toAdd
  map_one' := LowerN_zero F ζ hζ v
  map_mul' t u := LowerN_add F ζ hζ v t.toAdd u.toAdd

theorem W_sq : W F ζ hζ v ^ 2 = 1 := by
  have hs : KPLocalCover.sigmaTwo F ζ hζ v (weylSwap _) (weylSwap _) = 1 := by
    simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
      swap_sq_matrix, KubotaRankTwo.X_one, swap_X, swap_det, mul_neg_one,
      div_one, one_mul]
    rw [B_one_left, ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 (-1)).1]
    simp
  rw [pow_two, W, KPLocalCover.sectionMap_mul, hs, map_one, one_mul,
    swap_sq_matrix, section_one]

theorem signedW_sq :
    signedW F ζ hζ v ^ 2 = KPLocalCover.sectionMap F ζ hζ v
      (KubotaRankTwo.d (KPHilbert.Completion F v) (-1) (-1)) := by
  have hs : KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.w _) (KubotaRankTwo.w _) = 1 := by
    simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
      signed_sq_matrix, KubotaRankTwo.X_d, KubotaRankTwo.X_w,
      KubotaRankTwo.det_w, div_one, one_mul, one_pow]
    rw [((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 (-1)).1, B_one_left]
    simp
  rw [pow_two, signedW, KPLocalCover.sectionMap_mul, hs, map_one, one_mul,
    signed_sq_matrix]

@[simp] theorem A_one : A F ζ hζ v 1 = 1 := by
  simp only [A, d_one_matrix, section_one]

theorem A_mul (x y : (KPHilbert.Completion F v)ˣ) :
    A F ζ hζ v x * A F ζ hζ v y =
      KPLocalCover.centralInjection F ζ hζ v (KPHilbert.B3 F ζ hζ v x y ^ 2) *
        A F ζ hζ v (x * y) := by
  have hs : KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.d _ x 1)
      (KubotaRankTwo.d _ y 1) = KPHilbert.B3 F ζ hζ v x y ^ 2 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
      d_mul_matrix, B_one_left, B_one_right]
  rw [A, A, KPLocalCover.sectionMap_mul, hs, d_mul_matrix]
  rfl

private theorem n_continuous (K : Type*) [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (KubotaRankTwo.n K) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> simp only [Function.comp_def, KubotaRankTwo.coe_n,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
    all_goals first | exact continuous_const | exact continuous_id
  · have he : ∀ t : K, (KubotaRankTwo.n K t)⁻¹ = KubotaRankTwo.n K (-t) := by
      intro t
      apply inv_eq_of_mul_eq_one_right
      rw [n_add_matrix, add_neg_cancel, n_zero_matrix]
    simp only [he]
    apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> simp only [KubotaRankTwo.coe_n,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
    all_goals first | exact continuous_const | exact continuous_neg

private theorem lower_continuous (K : Type*) [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (lowerN K) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> change Continuous (fun t : K => _)
    all_goals first | exact continuous_const | exact continuous_id
  · have he : ∀ t : K, (lowerN K t)⁻¹ = lowerN K (-t) := by
      intro t
      apply inv_eq_of_mul_eq_one_right
      rw [lower_add_matrix, add_neg_cancel, lower_zero_matrix]
    simp only [he]
    apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> change Continuous (fun t : K => _)
    all_goals first | exact continuous_const | exact continuous_neg

private theorem d_continuous (K : Type*) [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (fun y : Kˣ => KubotaRankTwo.d K y 1) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> change Continuous (fun y : Kˣ => _)
    all_goals first | exact continuous_const | exact Units.continuous_val
  · have he : ∀ y : Kˣ, (KubotaRankTwo.d K y 1)⁻¹ = KubotaRankTwo.d K y⁻¹ 1 := by
      intro y
      apply inv_eq_of_mul_eq_one_right
      rw [d_mul_matrix, mul_inv_cancel, d_one_matrix]
    simp only [he]
    apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> change Continuous (fun y : Kˣ => _)
    all_goals first | exact continuous_const | exact Units.continuous_coe_inv

variable (q : HeightOneSpectrum (𝓞 F))

private theorem finite_section_continuousAt {X : Type*} [TopologicalSpace X]
    (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (f : X → KPLocalCover.LocalGL2 F (Sum.inr q)) (hf : Continuous f)
    (x : X) (hx : f x = 1) :
    letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
    ContinuousAt (fun t => KPLocalCover.sectionMap F ζ hζ (Sum.inr q) (f t)) x := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
  have hs : ContinuousOn (KPLocalCover.sectionMap F ζ hζ (Sum.inr q))
      (KPLocalCube.Gamma F q m) := by
    rw [continuousOn_iff_continuous_restrict]
    have hc := (KPLocalChartTopology.translatedChart_isOpenEmbedding F ζ hζ q m hm 1).continuous
    change Continuous (fun k : KPLocalCube.Gamma F q m => KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val)
    change Continuous (fun k : KPLocalCube.Gamma F q m =>
      (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) *
        KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val) at hc
    simpa only [one_mul] using hc
  have hopen := (KPLocalCube.Gamma_compact_open F q m hm.1).2
  exact (hs.comp hf.continuousOn (fun _ ht => ht)).continuousAt
    ((hopen.preimage hf).mem_nhds (by simp [hx]))

theorem finite_N_continuous (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
    Continuous (N F ζ hζ (Sum.inr q)) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ q m hm).2.2
  have hc := finite_section_continuousAt F ζ hζ q m hm (KubotaRankTwo.n _)
    (n_continuous _) 0 (n_zero_matrix _)
  have hh : Continuous (N_hom F ζ hζ (Sum.inr q)) :=
    continuous_of_continuousAt_one (N_hom F ζ hζ (Sum.inr q)) hc
  exact hh

theorem finite_LowerN_continuous (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
    Continuous (LowerN F ζ hζ (Sum.inr q)) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ q m hm).2.2
  have hc := finite_section_continuousAt F ζ hζ q m hm (lowerN _)
    (lower_continuous _) 0 (lower_zero_matrix _)
  have hh : Continuous (LowerN_hom F ζ hζ (Sum.inr q)) :=
    continuous_of_continuousAt_one (LowerN_hom F ζ hζ (Sum.inr q)) hc
  exact hh

theorem finite_A_continuous (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
    Continuous (A F ζ hζ (Sum.inr q)) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ q m hm).2.2
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  have ha : ContinuousAt (A F ζ hζ (Sum.inr q)) 1 :=
    finite_section_continuousAt F ζ hζ q m hm (fun y => KubotaRankTwo.d _ y 1)
      (d_continuous _) 1 (d_one_matrix _)
  rw [continuous_iff_continuousAt]
  intro x
  let t : (KPHilbert.Completion F (Sum.inr q))ˣ →
      (KPHilbert.Completion F (Sum.inr q))ˣ := fun y => x⁻¹ * y
  have ht : Continuous t := continuous_const.mul continuous_id
  have htx : t x = 1 := inv_mul_cancel x
  have hat : ContinuousAt (fun y => A F ζ hζ (Sum.inr q) (t y)) x := by
    have ha' : ContinuousAt (A F ζ hζ (Sum.inr q)) (t x) := by
      simpa only [htx] using ha
    exact ha'.comp ht.continuousAt
  have hb : Continuous (fun y => KPHilbert.B3 F ζ hζ (Sum.inr q) x (t y) ^ 2) :=
    ((KPHilbert.B3_continuous F ζ hζ (Sum.inr q)).comp
      (continuous_const.prodMk ht)).pow 2
  have hz : Continuous (KPLocalCover.centralInjection F ζ hζ (Sum.inr q)) :=
    continuous_of_discreteTopology
  have hc := (hz.comp hb).continuousAt.inv.mul
    ((continuousAt_const (y := A F ζ hζ (Sum.inr q) x)).mul hat)
  have he : ∀ y, A F ζ hζ (Sum.inr q) y =
      (KPLocalCover.centralInjection F ζ hζ (Sum.inr q)
        (KPHilbert.B3 F ζ hζ (Sum.inr q) x (t y) ^ 2))⁻¹ *
          (A F ζ hζ (Sum.inr q) x * A F ζ hζ (Sum.inr q) (t y)) := by
    intro y
    rw [A_mul, inv_mul_cancel_left]
    congr 1
    exact (mul_inv_cancel_left x y).symm
  exact hc.congr_of_eventuallyEq (Filter.Eventually.of_forall he)

variable (w : InfinitePlace F)

theorem complex_N_continuous :
    letI := KPLocalChartTopology.complexTopology F ζ hζ w
    Continuous (N F ζ hζ (Sum.inl w)) := by
  letI := KPLocalChartTopology.complexTopology F ζ hζ w
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  apply continuous_induced_rng.mpr
  exact (n_continuous (KPHilbert.Completion F (Sum.inl w))).prodMk continuous_const

theorem complex_A_continuous :
    letI := KPLocalChartTopology.complexTopology F ζ hζ w
    Continuous (A F ζ hζ (Sum.inl w)) := by
  letI := KPLocalChartTopology.complexTopology F ζ hζ w
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  apply continuous_induced_rng.mpr
  exact (d_continuous (KPHilbert.Completion F (Sum.inl w))).prodMk continuous_const

def integralN (t : KPTameCompact.O F q) : KPTameCompact.K0 F q :=
  Matrix.GeneralLinearGroup.mk'' !![1, t; 0, 1] (by
    simp [Matrix.det_fin_two])

def integralLowerN (t : KPTameCompact.O F q) : KPTameCompact.K0 F q :=
  Matrix.GeneralLinearGroup.mk'' !![1, 0; t, 1] (by
    simp [Matrix.det_fin_two])

def integralA (y : (KPTameCompact.O F q)ˣ) : KPTameCompact.K0 F q :=
  Matrix.GeneralLinearGroup.mk'' !![(y : KPTameCompact.O F q), 0; 0, 1] (by
    simpa [Matrix.det_fin_two] using y.isUnit)

def integralW : KPTameCompact.K0 F q :=
  Matrix.GeneralLinearGroup.mk'' !![0, 1; 1, 0] (by
    simp [Matrix.det_fin_two])

variable (hq : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)

include hq

theorem N_eq_compact (t : KPTameCompact.O F q) :
    N F ζ hζ (Sum.inr q) (t : KPTameCompact.K F q) =
      (⟨KPTameCompact.inclusion F q (integralN F q t),
        KPTameCompact.kappa F q ζ hζ (integralN F q t)⟩ :
          KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) := by
  unfold N KPLocalCover.sectionMap
  congr 1
  · apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · symm
    apply KPTameCompact.kappa_zero
    simp [KPTameCompact.c, integralN]

theorem LowerN_eq_compact (t : KPTameCompact.O F q) :
    LowerN F ζ hζ (Sum.inr q) (t : KPTameCompact.K F q) =
      (⟨KPTameCompact.inclusion F q (integralLowerN F q t),
        KPTameCompact.kappa F q ζ hζ (integralLowerN F q t)⟩ :
          KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) := by
  unfold LowerN KPLocalCover.sectionMap
  congr 1
  · apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · symm
    unfold KPTameCompact.kappa
    have hd : KPTameCompact.d F q (integralLowerN F q t) = 1 := rfl
    have hdet : KPTameCompact.Δ F q (integralLowerN F q t) = 1 := by
      simp [KPTameCompact.Δ, KPTameCompact.inclusion, KPLocalCube.integerInclusion,
        Matrix.GeneralLinearGroup.map_det, Matrix.GeneralLinearGroup.val_det_apply,
        integralLowerN, Matrix.det_fin_two]
    simp only [hd, hdet, div_self one_ne_zero]
    split_ifs <;> try rfl
    have he : ∀ h : (1 : KPTameCompact.K F q) ≠ 0, Units.mk0 1 h = 1 := by
      intro h; apply Units.ext; rfl
    rw [he]
    exact B_one_right F ζ hζ (Sum.inr q) _

theorem A_eq_compact (y : (KPTameCompact.O F q)ˣ) :
    A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q y) =
      (⟨KPTameCompact.inclusion F q (integralA F q y),
        KPTameCompact.kappa F q ζ hζ (integralA F q y)⟩ :
          KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) := by
  unfold A KPLocalCover.sectionMap
  congr 1
  · apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · symm
    apply KPTameCompact.kappa_zero
    simp [KPTameCompact.c, integralA]

theorem W_eq_compact :
    W F ζ hζ (Sum.inr q) =
      (⟨KPTameCompact.inclusion F q (integralW F q),
        KPTameCompact.kappa F q ζ hζ (integralW F q)⟩ :
          KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) := by
  unfold W KPLocalCover.sectionMap
  congr 1
  · apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · symm
    apply KPTameCompact.kappa_norm_one
    change ‖(1 : KPTameCompact.K F q)‖ = 1
    exact norm_one

end
end DedekindZetaZeroFree.KPStandardLocalRootLifts
