module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalPGLCoverModules

@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.KPJacquetBruhatCharts

open scoped NumberField
open NumberField IsDedekindDomain
open KPLocalSmoothRepresentation

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)

def ordinaryOmega : Set (KPRankOneInduction.PGL2 F w) :=
  {g | ∃ A : KPRankOneInduction.GL2 F w,
    Matrix.ProjGenLinGroup.mk A = g ∧ A 1 0 ≠ 0}

def ordinaryDelta : Set (KPRankOneInduction.PGL2 F w) :=
  {g | ∃ A : KPRankOneInduction.GL2 F w,
    Matrix.ProjGenLinGroup.mk A = g ∧ A 1 1 ≠ 0}

def omega : Set (FiniteCover F ζ hζ w) :=
  projection F ζ hζ w ⁻¹' ordinaryOmega F w

def delta : Set (FiniteCover F ζ hζ w) :=
  projection F ζ hζ w ⁻¹' ordinaryDelta F w

private theorem entry_zero_iff (A B : KPRankOneInduction.GL2 F w)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (i j : Fin 2) : A i j = 0 ↔ B i j = 0 := by
  obtain ⟨u, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal_apply]
  fin_cases j <;> simp [Units.ne_zero u]

private theorem entry_ratio_eq (A B : KPRankOneInduction.GL2 F w)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (i j k : Fin 2) : A i j / A i k = B i j / B i k := by
  obtain ⟨u, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal_apply]
  fin_cases j <;> fin_cases k <;> simp [mul_div_mul_right _ _ (Units.ne_zero u)]

theorem mem_ordinaryOmega_iff (A : KPRankOneInduction.GL2 F w) :
    Matrix.ProjGenLinGroup.mk A ∈ ordinaryOmega F w ↔ A 1 0 ≠ 0 := by
  constructor
  · rintro ⟨B, hB, hne⟩
    exact fun hz => hne ((entry_zero_iff F w A B hB.symm 1 0).mp hz)
  · exact fun h => ⟨A, rfl, h⟩

theorem mem_ordinaryDelta_iff (A : KPRankOneInduction.GL2 F w) :
    Matrix.ProjGenLinGroup.mk A ∈ ordinaryDelta F w ↔ A 1 1 ≠ 0 := by
  constructor
  · rintro ⟨B, hB, hne⟩
    exact fun hz => hne ((entry_zero_iff F w A B hB.symm 1 1).mp hz)
  · exact fun h => ⟨A, rfl, h⟩

def omegaCoordinate (g : omega F ζ hζ w) : KPRankOneInduction.LocalField F w :=
  let A := Classical.choose g.property
  A 1 1 / A 1 0

def deltaCoordinate (g : delta F ζ hζ w) : KPRankOneInduction.LocalField F w :=
  let A := Classical.choose g.property
  A 1 0 / A 1 1

theorem omegaCoordinate_eq (g : omega F ζ hζ w)
    (A : KPRankOneInduction.GL2 F w)
    (hA : Matrix.ProjGenLinGroup.mk A = projection F ζ hζ w g.val) :
    omegaCoordinate F ζ hζ w g = A 1 1 / A 1 0 := by
  exact entry_ratio_eq F w _ A ((Classical.choose_spec g.property).1.trans hA.symm) 1 1 0

theorem deltaCoordinate_eq (g : delta F ζ hζ w)
    (A : KPRankOneInduction.GL2 F w)
    (hA : Matrix.ProjGenLinGroup.mk A = projection F ζ hζ w g.val) :
    deltaCoordinate F ζ hζ w g = A 1 0 / A 1 1 := by
  exact entry_ratio_eq F w _ A ((Classical.choose_spec g.property).1.trans hA.symm) 1 0 1

 theorem projection_upper (x : KPRankOneInduction.LocalField F w) :
    projection F ζ hζ w (upperRoot F ζ hζ w (Multiplicative.ofAdd x)) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (KPRankOneInduction.LocalField F w) x) := rfl

 theorem projection_lower (y : KPRankOneInduction.LocalField F w) :
    projection F ζ hζ w (lowerRoot F ζ hζ w (Multiplicative.ofAdd y)) =
      Matrix.ProjGenLinGroup.mk
        (KPStandardLocalRootLifts.lowerN (KPRankOneInduction.LocalField F w) y) := rfl

 theorem projection_weyl : projection F ζ hζ w
    (KPPGLLocalCover.W F ζ hζ (Sum.inr w)) =
      Matrix.ProjGenLinGroup.mk
        (KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w)) := rfl

 theorem borel_bottom_right (A : KPRankOneInduction.GL2 F w)
    (hA : A 1 0 = 0) : A 1 1 ≠ 0 := by
  intro hz
  exact A.det_ne_zero (by simp [Matrix.det_fin_two, hA, hz])

def omegaMap (p : Borel F ζ hζ w × KPRankOneInduction.LocalField F w) :
    omega F ζ hζ w :=
  ⟨p.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
    upperRoot F ζ hζ w (Multiplicative.ofAdd p.2), by
      obtain ⟨A, hA, hc⟩ := p.1.property
      refine ⟨A * KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w) *
        KubotaRankTwo.n (KPRankOneInduction.LocalField F w) p.2, ?_, ?_⟩
      · rw [map_mul, map_mul, map_mul, map_mul, projection_upper, projection_weyl, hA]
      · simpa [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
          KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.n,
          Matrix.GeneralLinearGroup.mkOfDetNeZero] using borel_bottom_right F w A hc⟩

def deltaMap (p : Borel F ζ hζ w × KPRankOneInduction.LocalField F w) :
    delta F ζ hζ w :=
  ⟨p.1.val * lowerRoot F ζ hζ w (Multiplicative.ofAdd p.2), by
    obtain ⟨A, hA, hc⟩ := p.1.property
    refine ⟨A * KPStandardLocalRootLifts.lowerN (KPRankOneInduction.LocalField F w) p.2,
      ?_, ?_⟩
    · rw [map_mul, map_mul, projection_lower, hA]
    · simpa [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        KPStandardLocalRootLifts.lowerN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
        using borel_bottom_right F w A hc⟩

 theorem upper_matrix_inv (x : KPRankOneInduction.LocalField F w) :
    (KubotaRankTwo.n (KPRankOneInduction.LocalField F w) x)⁻¹ =
      KubotaRankTwo.n (KPRankOneInduction.LocalField F w) (-x) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.n,
      Matrix.GeneralLinearGroup.mkOfDetNeZero]

 theorem lower_matrix_inv (x : KPRankOneInduction.LocalField F w) :
    (KPStandardLocalRootLifts.lowerN (KPRankOneInduction.LocalField F w) x)⁻¹ =
      KPStandardLocalRootLifts.lowerN (KPRankOneInduction.LocalField F w) (-x) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, KPStandardLocalRootLifts.lowerN,
      Matrix.GeneralLinearGroup.mkOfDetNeZero]

 theorem weyl_matrix_inv :
    (KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w))⁻¹ =
      KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, KPStandardLocalRootLifts.weylSwap,
      Matrix.GeneralLinearGroup.mkOfDetNeZero]

def omegaInverse (g : omega F ζ hζ w) :
    Borel F ζ hζ w × KPRankOneInduction.LocalField F w :=
  (⟨g.val * (KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
    upperRoot F ζ hζ w (Multiplicative.ofAdd (omegaCoordinate F ζ hζ w g)))⁻¹,
    by
      obtain ⟨A, hA, hc⟩ := g.property
      refine ⟨A * (KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w) *
        KubotaRankTwo.n (KPRankOneInduction.LocalField F w)
          (omegaCoordinate F ζ hζ w g))⁻¹, ?_, ?_⟩
      · rw [map_mul, map_inv, map_mul, map_mul, map_inv, map_mul,
          projection_upper, projection_weyl, hA]
      · rw [mul_inv_rev, upper_matrix_inv, weyl_matrix_inv,
          omegaCoordinate_eq F ζ hζ w g A hA]
        simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.n,
          KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          mul_div_cancel₀ _ hc]⟩, omegaCoordinate F ζ hζ w g)

def deltaInverse (g : delta F ζ hζ w) :
    Borel F ζ hζ w × KPRankOneInduction.LocalField F w :=
  (⟨g.val * (lowerRoot F ζ hζ w
    (Multiplicative.ofAdd (deltaCoordinate F ζ hζ w g)))⁻¹, by
      obtain ⟨A, hA, hd⟩ := g.property
      refine ⟨A * (KPStandardLocalRootLifts.lowerN (KPRankOneInduction.LocalField F w)
        (deltaCoordinate F ζ hζ w g))⁻¹, ?_, ?_⟩
      · rw [map_mul, map_inv, map_mul, map_inv, projection_lower, hA]
      · rw [lower_matrix_inv, deltaCoordinate_eq F ζ hζ w g A hA]
        simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
          KPStandardLocalRootLifts.lowerN, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          mul_div_cancel₀ _ hd]⟩,
    deltaCoordinate F ζ hζ w g)

private theorem omegaCoordinate_map
    (p : Borel F ζ hζ w × KPRankOneInduction.LocalField F w) :
    omegaCoordinate F ζ hζ w (omegaMap F ζ hζ w p) = p.2 := by
  obtain ⟨A, hA, hc⟩ := p.1.property
  rw [omegaCoordinate_eq F ζ hζ w _
    (A * KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w) *
      KubotaRankTwo.n (KPRankOneInduction.LocalField F w) p.2) (by
        simp only [omegaMap, map_mul, projection_upper, projection_weyl, hA])]
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.n,
    KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.mkOfDetNeZero, hc,
    borel_bottom_right F w A hc]

private theorem deltaCoordinate_map
    (p : Borel F ζ hζ w × KPRankOneInduction.LocalField F w) :
    deltaCoordinate F ζ hζ w (deltaMap F ζ hζ w p) = p.2 := by
  obtain ⟨A, hA, hc⟩ := p.1.property
  rw [deltaCoordinate_eq F ζ hζ w _
    (A * KPStandardLocalRootLifts.lowerN (KPRankOneInduction.LocalField F w) p.2) (by
      simp only [deltaMap, map_mul, projection_lower, hA])]
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
    KPStandardLocalRootLifts.lowerN, Matrix.GeneralLinearGroup.mkOfDetNeZero, hc,
    borel_bottom_right F w A hc]

 theorem omega_left_inv : Function.LeftInverse (omegaInverse F ζ hζ w)
    (omegaMap F ζ hζ w) := by
  intro p
  apply Prod.ext
  · apply Subtype.ext
    change (omegaMap F ζ hζ w p).val *
      (KPPGLLocalCover.W F ζ hζ (Sum.inr w) * upperRoot F ζ hζ w
        (Multiplicative.ofAdd (omegaCoordinate F ζ hζ w (omegaMap F ζ hζ w p))))⁻¹ = _
    rw [omegaCoordinate_map]
    change (p.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd p.2)) * _ = _
    group
  · exact omegaCoordinate_map F ζ hζ w p

 theorem omega_right_inv : Function.RightInverse (omegaInverse F ζ hζ w)
    (omegaMap F ζ hζ w) := by
  intro g
  apply Subtype.ext
  simp only [omegaMap, omegaInverse]
  group

 theorem delta_left_inv : Function.LeftInverse (deltaInverse F ζ hζ w)
    (deltaMap F ζ hζ w) := by
  intro p
  apply Prod.ext
  · apply Subtype.ext
    change (deltaMap F ζ hζ w p).val * (lowerRoot F ζ hζ w
      (Multiplicative.ofAdd (deltaCoordinate F ζ hζ w (deltaMap F ζ hζ w p))))⁻¹ = _
    rw [deltaCoordinate_map]
    change (p.1.val * lowerRoot F ζ hζ w (Multiplicative.ofAdd p.2)) * _ = _
    group
  · exact deltaCoordinate_map F ζ hζ w p

 theorem delta_right_inv : Function.RightInverse (deltaInverse F ζ hζ w)
    (deltaMap F ζ hζ w) := by
  intro g
  apply Subtype.ext
  simp only [deltaMap, deltaInverse]
  group

private theorem projection_continuous (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteCoverTopology F ζ hζ w m
    Continuous (projection F ζ hζ w) := by
  letI := finiteCoverTopology F ζ hζ w m
  have hmap : Continuous (ordinaryPGLMap F w) := by
    apply (QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff).mp
    change Continuous (Matrix.ProjGenLinGroup.mk : KPRankOneInduction.GL2 F w →
      KPRankOneInduction.PGL2 F w)
    exact QuotientGroup.continuous_mk
  exact hmap.comp (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.2.1.continuous

private theorem ordinary_domain_open (j : Fin 2) :
    IsOpen {g : KPRankOneInduction.PGL2 F w | ∃ A : KPRankOneInduction.GL2 F w,
      Matrix.ProjGenLinGroup.mk A = g ∧ A 1 j ≠ 0} := by
  have hq : Topology.IsQuotientMap
      (Matrix.ProjGenLinGroup.mk : KPRankOneInduction.GL2 F w → KPRankOneInduction.PGL2 F w) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap
  rw [← hq.isOpen_preimage]
  have he : (fun A : KPRankOneInduction.GL2 F w => A 1 j) ⁻¹' {0}ᶜ =
      Matrix.ProjGenLinGroup.mk ⁻¹'
        {g : KPRankOneInduction.PGL2 F w | ∃ A : KPRankOneInduction.GL2 F w,
          Matrix.ProjGenLinGroup.mk A = g ∧ A 1 j ≠ 0} := by
    ext A
    constructor
    · exact fun hn => ⟨A, rfl, hn⟩
    · rintro ⟨B, hB, hn⟩ hz
      exact hn ((entry_zero_iff F w A B hB.symm 1 j).mp hz)
  rw [← he]
  exact isClosed_singleton.isOpen_compl.preimage
    ((continuous_apply j).comp ((continuous_apply 1).comp (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (KPRankOneInduction.LocalField F w)))))

 def ordinaryCoordinate (j k : Fin 2)
    (g : {g : KPRankOneInduction.PGL2 F w | ∃ A : KPRankOneInduction.GL2 F w,
      Matrix.ProjGenLinGroup.mk A = g ∧ A 1 k ≠ 0}) : KPRankOneInduction.LocalField F w :=
  let A := Classical.choose g.property
  A 1 j / A 1 k

private theorem ordinaryCoordinate_continuous (j k : Fin 2) :
    Continuous (ordinaryCoordinate F w j k) := by
  have hq : IsOpenQuotientMap
      (Matrix.ProjGenLinGroup.mk : KPRankOneInduction.GL2 F w → KPRankOneInduction.PGL2 F w) :=
    QuotientGroup.isOpenQuotientMap_mk
  apply ((hq.restrictPreimage _).continuous_comp_iff).mp
  have he : (ordinaryCoordinate F w j k) ∘
      Set.restrictPreimage
        {g : KPRankOneInduction.PGL2 F w | ∃ A : KPRankOneInduction.GL2 F w,
          Matrix.ProjGenLinGroup.mk A = g ∧ A 1 k ≠ 0} Matrix.ProjGenLinGroup.mk =
      (fun A => A.val 1 j / A.val 1 k) := by
    funext A
    exact entry_ratio_eq F w _ A.val
      (Classical.choose_spec A.property).1 1 j k
  rw [he]
  apply Continuous.div
  · exact (continuous_apply j).comp ((continuous_apply 1).comp
      ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (KPRankOneInduction.LocalField F w))).comp continuous_subtype_val))
  · exact (continuous_apply k).comp ((continuous_apply 1).comp
      ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (KPRankOneInduction.LocalField F w))).comp continuous_subtype_val))
  · intro A
    obtain ⟨B, hB, hn⟩ := A.property
    exact fun hz => hn ((entry_zero_iff F w A.val B hB.symm 1 k).mp hz)

 theorem omegaCoordinate_continuous (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteCoverTopology F ζ hζ w m
    Continuous (omegaCoordinate F ζ hζ w) := by
  letI := finiteCoverTopology F ζ hζ w m
  let f : omega F ζ hζ w → ordinaryOmega F w :=
    fun g => ⟨projection F ζ hζ w g.val, g.property⟩
  have hf : Continuous f :=
    ((projection_continuous F ζ hζ w m hm).comp continuous_subtype_val).subtype_mk _
  have hh : Continuous (fun g => ordinaryCoordinate F w 1 0 (f g)) :=
    (ordinaryCoordinate_continuous F w 1 0).comp hf
  apply hh.congr
  intro g
  rfl

 theorem deltaCoordinate_continuous (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteCoverTopology F ζ hζ w m
    Continuous (deltaCoordinate F ζ hζ w) := by
  letI := finiteCoverTopology F ζ hζ w m
  let f : delta F ζ hζ w → ordinaryDelta F w :=
    fun g => ⟨projection F ζ hζ w g.val, g.property⟩
  have hf : Continuous f :=
    ((projection_continuous F ζ hζ w m hm).comp continuous_subtype_val).subtype_mk _
  have hh : Continuous (fun g => ordinaryCoordinate F w 0 1 (f g)) :=
    (ordinaryCoordinate_continuous F w 0 1).comp hf
  apply hh.congr
  intro g
  rfl

def omegaHomeomorph (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteCoverTopology F ζ hζ w m
    (Borel F ζ hζ w × KPRankOneInduction.LocalField F w) ≃ₜ omega F ζ hζ w := by
  letI := finiteCoverTopology F ζ hζ w m
  exact {
    toFun := omegaMap F ζ hζ w
    invFun := omegaInverse F ζ hζ w
    left_inv := omega_left_inv F ζ hζ w
    right_inv := omega_right_inv F ζ hζ w
    continuous_toFun := by
      letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
      have hN := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).1
      apply Continuous.subtype_mk
      change Continuous (fun p : Borel F ζ hζ w × KPRankOneInduction.LocalField F w =>
        p.1.val * KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr w) p.2)
      exact ((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
        (hN.comp continuous_snd)
    continuous_invFun := by
      letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
      have hx := omegaCoordinate_continuous F ζ hζ w m hm
      have hN := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).1
      exact (continuous_subtype_val.mul
        (continuous_const.mul (hN.comp hx)).inv).subtype_mk _ |>.prodMk hx }

def deltaHomeomorph (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteCoverTopology F ζ hζ w m
    (Borel F ζ hζ w × KPRankOneInduction.LocalField F w) ≃ₜ delta F ζ hζ w := by
  letI := finiteCoverTopology F ζ hζ w m
  exact {
    toFun := deltaMap F ζ hζ w
    invFun := deltaInverse F ζ hζ w
    left_inv := delta_left_inv F ζ hζ w
    right_inv := delta_right_inv F ζ hζ w
    continuous_toFun := by
      letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
      have hL := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).2.1
      exact ((continuous_subtype_val.comp continuous_fst).mul
        (hL.comp continuous_snd)).subtype_mk _
    continuous_invFun := by
      letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
      have hy := deltaCoordinate_continuous F ζ hζ w m hm
      have hL := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).2.1
      exact (continuous_subtype_val.mul (hL.comp hy).inv).subtype_mk _ |>.prodMk hy }

theorem overlap_coordinates (g : FiniteCover F ζ hζ w)
    (hΩ : g ∈ omega F ζ hζ w) (hΔ : g ∈ delta F ζ hζ w) :
    omegaCoordinate F ζ hζ w ⟨g, hΩ⟩ =
      (deltaCoordinate F ζ hζ w ⟨g, hΔ⟩)⁻¹ ∧
    omegaCoordinate F ζ hζ w ⟨g, hΩ⟩ ≠ 0 ∧
    deltaCoordinate F ζ hζ w ⟨g, hΔ⟩ ≠ 0 := by
  obtain ⟨A, hA, hc⟩ := hΩ
  have hd : A 1 1 ≠ 0 := (mem_ordinaryDelta_iff F w A).mp (hA.symm ▸ hΔ)
  rw [omegaCoordinate_eq F ζ hζ w _ A hA, deltaCoordinate_eq F ζ hζ w _ A hA]
  exact ⟨(inv_div _ _).symm, div_ne_zero hd hc, div_ne_zero hc hd⟩

theorem omega_complement :
    (omega F ζ hζ w)ᶜ = (Borel F ζ hζ w : Set (FiniteCover F ζ hζ w)) := by
  ext g
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (projection F ζ hζ w g)
  change (¬ projection F ζ hζ w g ∈ ordinaryOmega F w) ↔
    ∃ B : KPRankOneInduction.GL2 F w, Matrix.ProjGenLinGroup.mk B =
      projection F ζ hζ w g ∧ B 1 0 = 0
  rw [← hA, mem_ordinaryOmega_iff]
  constructor
  · exact fun h => ⟨A, rfl, not_ne_iff.mp h⟩
  · rintro ⟨B, hB, hz⟩
    exact not_ne_iff.mpr ((entry_zero_iff F w A B hB.symm 1 0).mpr hz)

theorem charts_cover : omega F ζ hζ w ∪ delta F ζ hζ w = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (projection F ζ hζ w g)
  by_cases hc : A 1 0 = 0
  · right
    refine ⟨A, hA, ?_⟩
    intro hd
    exact A.det_ne_zero (by simp [Matrix.det_fin_two, hc, hd])
  · left
    exact ⟨A, hA, hc⟩

theorem closed_cell_coordinate (g : delta F ζ hζ w) :
    g.val ∈ Borel F ζ hζ w ↔ deltaCoordinate F ζ hζ w g = 0 := by
  obtain ⟨A, hA, hd⟩ := g.property
  rw [deltaCoordinate_eq F ζ hζ w g A hA, div_eq_zero_iff]
  simp only [hd, or_false]
  change g.val ∈ (Borel F ζ hζ w : Set (FiniteCover F ζ hζ w)) ↔ _
  rw [← omega_complement F ζ hζ w]
  change (¬ projection F ζ hζ w g.val ∈ ordinaryOmega F w) ↔ _
  rw [← hA, mem_ordinaryOmega_iff, not_ne_iff]

theorem charts_open_and_borel_closed
    (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteCoverTopology F ζ hζ w m
    IsOpen (omega F ζ hζ w) ∧ IsOpen (delta F ζ hζ w) ∧
      IsClosed (Borel F ζ hζ w : Set (FiniteCover F ζ hζ w)) := by
  letI := finiteCoverTopology F ζ hζ w m
  have hΩ : IsOpen (omega F ζ hζ w) :=
    (ordinary_domain_open F w 0).preimage (projection_continuous F ζ hζ w m hm)
  have hΔ : IsOpen (delta F ζ hζ w) :=
    (ordinary_domain_open F w 1).preimage (projection_continuous F ζ hζ w m hm)
  exact ⟨hΩ, hΔ, omega_complement F ζ hζ w ▸ hΩ.isClosed_compl⟩

def compactTransversal : Set (FiniteCover F ζ hζ w) :=
  (fun x : KPRankOneInduction.LocalField F w =>
    KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
      upperRoot F ζ hζ w (Multiplicative.ofAdd x)) ''
      (KPLocalCube.LocalIntegers F w : Set (KPRankOneInduction.LocalField F w)) ∪
  (fun y : KPRankOneInduction.LocalField F w =>
    lowerRoot F ζ hζ w (Multiplicative.ofAdd y)) ''
      (KPLocalCube.LocalIntegers F w : Set (KPRankOneInduction.LocalField F w))

theorem compactTransversal_isCompact
    (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteCoverTopology F ζ hζ w m
    IsCompact (compactTransversal F ζ hζ w) := by
  letI : ValuativeRel (KPRankOneInduction.LocalField F w) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F w
  letI : IsNonarchimedeanLocalField (KPRankOneInduction.LocalField F w) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F w
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  have hO : IsCompact (KPLocalCube.LocalIntegers F w :
      Set (KPRankOneInduction.LocalField F w)) :=
    IsNonarchimedeanLocalField.isCompact_closedBall (KPRankOneInduction.LocalField F w) 1
  obtain ⟨hN, hL, _⟩ := KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm
  exact (hO.image (continuous_const.mul hN)).union (hO.image hL)

theorem borel_mul_compactTransversal :
    (fun p : Borel F ζ hζ w × FiniteCover F ζ hζ w => p.1.val * p.2) ''
      (Set.univ ×ˢ compactTransversal F ζ hζ w) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  by_cases hc : g ∈ omega F ζ hζ w
  · let q : omega F ζ hζ w := ⟨g, hc⟩
    let x := omegaCoordinate F ζ hζ w q
    by_cases hx : x ∈ (KPLocalCube.LocalIntegers F w : Set (KPRankOneInduction.LocalField F w))
    · refine ⟨((omegaInverse F ζ hζ w q).1,
        KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
          upperRoot F ζ hζ w (Multiplicative.ofAdd x)), ⟨Set.mem_univ _, ?_⟩, ?_⟩
      · exact Or.inl ⟨x, hx, rfl⟩
      · change (omegaInverse F ζ hζ w q).1.val * _ = g
        have h := congrArg Subtype.val (omega_right_inv F ζ hζ w q)
        simpa only [omegaMap, omegaInverse, mul_assoc] using h
    · obtain ⟨A, hA, hAc⟩ := hc
      have hd : A 1 1 ≠ 0 := by
        intro hz
        have hx0 : x = 0 := by
          dsimp [x, q]
          rw [omegaCoordinate_eq F ζ hζ w _ A hA, hz, zero_div]

        have hxmem : x ∈ (KPLocalCube.LocalIntegers F w :
            Set (KPRankOneInduction.LocalField F w)) := hx0 ▸ (KPLocalCube.LocalIntegers F w).zero_mem
        exact hx hxmem
      have hxi : x⁻¹ ∈ (KPLocalCube.LocalIntegers F w : Set (KPRankOneInduction.LocalField F w)) :=
        (Valuation.val_le_one_or_val_inv_le_one
          (ClassFieldTheory.finitePlaceCompletionValuativeRel F w).valuation x).resolve_left hx
      let q' : delta F ζ hζ w := ⟨g, ⟨A, hA, hd⟩⟩
      let y := deltaCoordinate F ζ hζ w q'
      have hxy : y = x⁻¹ := by
        dsimp [y, x, q, q']
        rw [omegaCoordinate_eq F ζ hζ w _ A hA, deltaCoordinate_eq F ζ hζ w _ A hA]
        exact (inv_div _ _).symm
      refine ⟨((deltaInverse F ζ hζ w q').1,
        lowerRoot F ζ hζ w (Multiplicative.ofAdd y)), ⟨Set.mem_univ _, ?_⟩, ?_⟩
      · exact Or.inr ⟨y, hxy ▸ hxi, rfl⟩
      · exact congrArg Subtype.val (delta_right_inv F ζ hζ w q')
  · have hgB : g ∈ Borel F ζ hζ w := by
      change g ∈ (Borel F ζ hζ w : Set (FiniteCover F ζ hζ w))
      rw [← omega_complement]
      exact hc
    refine ⟨(⟨g, hgB⟩, 1), ⟨Set.mem_univ _, ?_⟩, mul_one g⟩
    right
    refine ⟨0, (KPLocalCube.LocalIntegers F w).zero_mem, ?_⟩
    exact (lowerRoot F ζ hζ w).map_one

end DedekindZetaZeroFree.KPJacquetBruhatCharts

end
