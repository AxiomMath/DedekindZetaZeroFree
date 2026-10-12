module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates
public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteLevelActionsAndDensity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff Matrix
namespace DedekindZetaZeroFree.KPLiteralChamber.JointProfile.ArchChartProduct
open KPGlobalResidualConstruction KPLiteralChamber NumberField
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def product (p : ArchCoordinates F × ArchCoordinates F) : ArchCoordinates F := fun q =>
  ![p.1 q 0 + p.1 q 1 * p.2 q 0 / (1 + p.1 q 2 * p.2 q 0),
    p.1 q 1 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)^2,
    p.2 q 2 + p.1 q 2 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)]
theorem product_coordinate (y x : Fin 3 → ℂ) (hy : y 1 ≠ 0) (hx : x 1 ≠ 0)
    (hden : 1+y 2*x 0 ≠ 0) :
    rightCoordinates (rightMatrix y * rightMatrix x).val =
    ![y 0+y 1*x 0/(1+y 2*x 0), y 1*x 1/(1+y 2*x 0)^2,
      x 2+y 2*x 1/(1+y 2*x 0)] := by
  rw [Units.val_mul, rightMatrix_val y hy, rightMatrix_val x hx]
  ext i
  fin_cases i <;> simp [rightCoordinates, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [hden, add_comm (y 2*x 0) 1] <;> ring
private theorem product_domain (y x : ArchCoordinates F) (hy : y ∈ archDomain F)
    (hx : x ∈ archDomain F) (hden : ∀w, 1+y w 2*x w 0 ≠ 0) :
    product F (y,x) ∈ archDomain F := by
  intro w
  exact div_ne_zero (mul_ne_zero (hy w) (hx w)) (pow_ne_zero _ (hden w))
private theorem product_chart (y x : ArchCoordinates F) (hy : y ∈ archDomain F)
    (hx : x ∈ archDomain F) (hden : ∀w, 1+y w 2*x w 0 ≠ 0) :
    archChart F ζ hζ (product F (y,x)) = archChart F ζ hζ y * archChart F ζ hζ x := by
  rw [right_insertion, right_insertion, right_insertion,
    ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  congr 1
  funext w
  change Matrix.ProjGenLinGroup.mk (rightMatrix (product F (y,x) w)) =
    Matrix.ProjGenLinGroup.mk (rightMatrix (y w)) * Matrix.ProjGenLinGroup.mk (rightMatrix (x w))
  rw [← map_mul]
  rw [show product F (y,x) w = rightCoordinates (rightMatrix (y w)*rightMatrix (x w)).val from
    (product_coordinate (y w) (x w) (hy w) (hx w) (hden w)).symm]
  apply rightCoordinates_reconstruct
  simpa [Units.val_mul, rightMatrix_val _ (hy w), rightMatrix_val _ (hx w),
    Matrix.mul_apply, Fin.sum_univ_two, add_comm] using hden w
private theorem domain_open : IsOpen (archDomain F) := by
  have he : archDomain F = ⋂ w : InfinitePlace F, {x : ArchCoordinates F | x w 1 ≠ 0} := by
    ext x; simp [archDomain]
  rw [he]
  apply isOpen_iInter_of_finite
  intro w
  exact isOpen_ne_fun (by fun_prop) continuous_const
private theorem base_domain : archBase F ∈ archDomain F := by
  intro w
  simp [archBase]
private theorem choose_domain : ∃ V : Set (ArchCoordinates F), IsOpen V ∧ archBase F ∈ V ∧
    V ⊆ archDomain F ∧ ∀y∈V, ∀x∈V, ∀w, 1+y w 2*x w 0 ≠ 0 := by
  let O : Set (ArchCoordinates F × ArchCoordinates F) :=
    ⋂ w : InfinitePlace F, {p | 1+p.1 w 2*p.2 w 0 ≠ 0}
  have hO : IsOpen O := by
    apply isOpen_iInter_of_finite
    intro w
    exact isOpen_ne_fun (by fun_prop) continuous_const
  have hb : (archBase F,archBase F) ∈ O := by simp [O,archBase]
  have hn := hO.mem_nhds hb
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hn
  obtain ⟨S₁,h₁,S₂,h₂,hs⟩ := hn
  obtain ⟨W₁,hW₁,ho₁,hb₁⟩ := mem_nhds_iff.mp h₁
  obtain ⟨W₂,hW₂,ho₂,hb₂⟩ := mem_nhds_iff.mp h₂
  refine ⟨W₁∩W₂∩archDomain F, (ho₁.inter ho₂).inter (domain_open F),
    ⟨⟨hb₁,hb₂⟩,base_domain F⟩, Set.inter_subset_right, ?_⟩
  intro y hy x hx w
  have hp : (y,x) ∈ O := hs (show (y,x) ∈ S₁ ×ˢ S₂ from ⟨hW₁ hy.1.1, hW₂ hx.1.2⟩)
  exact Set.mem_iInter.mp hp w
private theorem product_smooth (V : Set (ArchCoordinates F))
    (hden : ∀y∈V, ∀x∈V, ∀w, 1+y w 2*x w 0 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (product F) (V ×ˢ V) := by
  apply contDiffOn_pi.mpr
  intro w
  apply contDiffOn_pi.mpr
  intro i
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ArchCoordinates F × ArchCoordinates F =>
      1+p.1 w 2*p.2 w 0) (V ×ˢ V) := by fun_prop
  have hn : ∀p∈V ×ˢ V, 1+p.1 w 2*p.2 w 0 ≠ 0 := fun p hp => hden p.1 hp.1 p.2 hp.2 w
  have hinv := hd.inv hn
  have hc₁ (k : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ArchCoordinates F × ArchCoordinates F => p.1 w k) (V ×ˢ V) := by fun_prop
  have hc₂ (k : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ArchCoordinates F × ArchCoordinates F => p.2 w k) (V ×ˢ V) := by fun_prop
  fin_cases i <;> simp [product, div_eq_mul_inv, inv_pow]
  · exact (hc₁ 0).add (((hc₁ 1).mul (hc₂ 0)).mul hinv)
  · exact ((hc₁ 1).mul (hc₂ 1)).mul ((hd.pow 2).inv (fun p hp => pow_ne_zero _ (hn p hp)))
  · exact (hc₂ 2).add (((hc₁ 2).mul (hc₂ 1)).mul hinv)
private theorem finitePart_eq : KPGlobalTorusFunctionData.finitePart F ζ hζ =
    PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ := by
  unfold KPGlobalTorusFunctionData.finitePart PGLComplex.AdelicSlices.finiteSubgroup
  congr 1
  ext r
  simp [PGLComplex.AdelicSlices.finiteTuples]

 def matrixCoordinates (M : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    ArchCoordinates F := fun w => rightCoordinates (M w).val
private theorem coordinates_continuousAt_one : ContinuousAt (matrixCoordinates F)
    (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) := by
  apply continuousAt_pi.mpr
  intro w
  apply continuousAt_pi.mpr
  intro i
  have he (j k : Fin 2) : ContinuousAt (fun M : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ =>
      (M w).val j k) 1 := by
    exact (continuous_apply k).continuousAt.comp
      ((continuous_apply j).continuousAt.comp
        ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℂ)).continuousAt.comp (continuous_apply w).continuousAt))
  have hd : ContinuousAt (fun M : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ => (M w).val.det) 1 := by
    simp only [Matrix.det_fin_two]
    exact ((he 0 0).mul (he 1 1)).sub ((he 0 1).mul (he 1 0))
  have hn : ((1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) w).val 1 1 ≠ 0 := by simp
  fin_cases i <;> simp [matrixCoordinates, rightCoordinates]
  · exact (he 0 1).div (he 1 1) hn
  · exact hd.div ((he 1 1).pow 2) (pow_ne_zero _ hn)
  · exact (he 1 0).div (he 1 1) hn
private theorem archImage_nhds (W : Set (ArchCoordinates F)) (hW : IsOpen W) (hb : archBase F ∈ W) :
    (fun x w => Matrix.ProjGenLinGroup.mk (rightMatrix (x w))) '' W ∈
      nhds (1 : InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ) := by
  let Q : (InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) →
      (InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ) := Pi.map (fun _ => Matrix.ProjGenLinGroup.mk)
  have hQ : IsOpenMap Q := IsOpenMap.piMap
    (fun _ => QuotientGroup.isOpenMap_coe) (Filter.Eventually.of_forall (fun _ => Matrix.ProjGenLinGroup.mk_surjective))
  have hn : ∀ᶠ M in nhds (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ),
      matrixCoordinates F M ∈ W := by
    have hbase : matrixCoordinates F (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) = archBase F := by
      funext w i; fin_cases i <;> simp [matrixCoordinates, rightCoordinates, archBase]
    exact (coordinates_continuousAt_one F) (hbase ▸ hW.mem_nhds hb)
  have hden : ∀ᶠ M in nhds (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ),
      ∀w, (M w).val 1 1 ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro w
    have he : Continuous (fun M : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ => (M w).val 1 1) := by fun_prop
    exact he.continuousAt (isOpen_ne.mem_nhds (by simp))
  have hpre : Q ⁻¹' ((fun x w => Matrix.ProjGenLinGroup.mk (rightMatrix (x w))) '' W) ∈
      nhds (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) := by
    filter_upwards [hn,hden] with M hM hD
    refine ⟨matrixCoordinates F M, hM, ?_⟩
    funext w
    exact rightCoordinates_reconstruct (M w) (hD w)
  have hnh := hQ.nhds_le (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ)
  have hone : Q (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) = 1 := by funext w; simp [Q]
  rw [hone] at hnh
  exact hnh hpre
private theorem thickening_nhds (W : Set (ArchCoordinates F)) (hW : IsOpen W) (hb : archBase F ∈ W)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    {g | ∃ y ∈ W, ∃ u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      g = archChart F ζ hζ y * u} ∈ nhds (1 : G F ζ hζ) := by
  obtain ⟨e,he,hep⟩ := PGLComplex.AdelicSlices.actual_product_splitting F ζ hζ
  have hf := finitePart_eq F ζ hζ
  let E : KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ := Homeomorph.setCongr (congrArg (fun S : Subgroup (G F ζ hζ) => (S : Set (G F ζ hζ))) hf)
  let L : Set (PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) := E '' (U.toOpenSubgroup : Set _)
  have hL : L ∈ nhds (1 : PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) := by
    have hopen : IsOpen L := E.isOpenMap _ U.toOpenSubgroup.isOpen
    have hmem : (1 : PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) ∈ L := by
      exact ⟨1,U.toOpenSubgroup.one_mem,Subtype.ext rfl⟩
    exact hopen.mem_nhds hmem
  have hA := archImage_nhds F W hW hb
  let A : Set (PGLComplex.AdelicSlices.ArchGroup F) :=
    (fun x w => Matrix.ProjGenLinGroup.mk (rightMatrix (x w))) '' W
  have hprod : A ×ˢ L ∈ nhds (1 : PGLComplex.AdelicSlices.ArchGroup F ×
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hA hL
  have himage : e '' (A ×ˢ L) ∈ nhds (1 : G F ζ hζ) := by
    have hh := e.toHomeomorph.isOpenMap.nhds_le (1 : PGLComplex.AdelicSlices.ArchGroup F ×
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ)
    have heone : e (1 : PGLComplex.AdelicSlices.ArchGroup F ×
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) = 1 := e.map_one
    change nhds (e (1 : PGLComplex.AdelicSlices.ArchGroup F ×
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ)) ≤ Filter.map e (nhds 1) at hh
    rw [heone] at hh
    have hpre : e ⁻¹' (e '' (A ×ˢ L)) ∈ nhds (1 : PGLComplex.AdelicSlices.ArchGroup F ×
        PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) :=
      Filter.mem_of_superset hprod (Set.subset_preimage_image e (A ×ˢ L))
    exact hh hpre
  apply Filter.mem_of_superset himage
  rintro g ⟨⟨a,u⟩,⟨⟨y,hy,rfl⟩,⟨v,hv,hu⟩⟩,rfl⟩
  refine ⟨y,hy,v.val,?_,?_⟩
  · exact ⟨v,hv,rfl⟩
  · rw [he, right_insertion]
    have hval : u.val = v.val := congrArg Subtype.val hu.symm
    rw [hval]
    rfl

theorem actual_archChart_product :
    let μ : ArchCoordinates F × ArchCoordinates F → ArchCoordinates F := fun p q =>
      ![p.1 q 0 + p.1 q 1 * p.2 q 0 / (1 + p.1 q 2 * p.2 q 0),
        p.1 q 1 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)^2,
        p.2 q 2 + p.1 q 2 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)]
    ∃ V : Set (ArchCoordinates F), IsOpen V ∧ archBase F ∈ V ∧ V ⊆ archDomain F ∧
      ContDiffOn ℝ (⊤ : ℕ∞) μ (V ×ˢ V) ∧ Set.MapsTo μ (V ×ˢ V) (archDomain F) ∧
      (∀ y ∈ V, ∀ x ∈ V, archChart F ζ hζ (μ (y,x)) =
        archChart F ζ hζ y * archChart F ζ hζ x) ∧
      (∀ W : Set (ArchCoordinates F), IsOpen W → archBase F ∈ W → W ⊆ V →
        ∀ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
          {g | ∃ y ∈ W, ∃ u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
            g = archChart F ζ hζ y * u} ∈ nhds (1 : G F ζ hζ)) ∧
      (∀ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ, ∀ u ∈
        KPGlobalTorusFunctionData.globalLevel F ζ hζ U, ∀ x : ArchCoordinates F,
          Commute (archChart F ζ hζ x) u) := by
  dsimp only
  obtain ⟨V,hVo,hb,hVD,hden⟩ := choose_domain F
  refine ⟨V,hVo,hb,hVD,product_smooth F V hden,?_,?_,?_,?_⟩
  · rintro ⟨y,x⟩ ⟨hy,hx⟩
    exact product_domain F y x (hVD hy) (hVD hx) (hden y hy x hx)
  · intro y hy x hx
    exact product_chart F ζ hζ y x (hVD hy) (hVD hx) (hden y hy x hx)
  · intro W hW hbW hWV U
    exact thickening_nhds F ζ hζ W hW hbW U
  · intro U u hu x
    obtain ⟨v,hv,rfl⟩ := hu
    exact ActualFiniteTranslationEstimates.archChart_commutes_finite F ζ hζ x v

end DedekindZetaZeroFree.KPLiteralChamber.JointProfile.ArchChartProduct

end
