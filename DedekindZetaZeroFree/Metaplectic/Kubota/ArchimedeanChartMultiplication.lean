module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff Matrix
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeChartProduct
open KPGlobalResidualConstruction KPLiteralChamber NumberField
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def product (p : ArchCoordinates F × ArchCoordinates F) : ArchCoordinates F := fun q =>
  ![p.1 q 0 + p.1 q 1 * p.2 q 0 / (1 + p.1 q 2 * p.2 q 0),
    p.1 q 1 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)^2,
    p.2 q 2 + p.1 q 2 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)]
private theorem product_coordinate (y x : Fin 3 → ℂ) (hy : y 1 ≠ 0) (hx : x 1 ≠ 0)
    (hden : 1+y 2*x 0 ≠ 0) :
    rightCoordinates (rightMatrix y * rightMatrix x).val =
    ![y 0+y 1*x 0/(1+y 2*x 0), y 1*x 1/(1+y 2*x 0)^2,
      x 2+y 2*x 1/(1+y 2*x 0)] := by
  rw [Units.val_mul, rightMatrix_val y hy, rightMatrix_val x hx]
  ext i
  fin_cases i <;> simp [rightCoordinates, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [hden, add_comm (y 2*x 0) 1] <;> ring

 theorem product_chart (y x : ArchCoordinates F) (hy : y ∈ archDomain F)
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
 theorem domain_open : IsOpen (archDomain F) := by
  have he : archDomain F = ⋂ w : InfinitePlace F, {x : ArchCoordinates F | x w 1 ≠ 0} := by
    ext x; simp [archDomain]
  rw [he]
  apply isOpen_iInter_of_finite
  intro w
  exact isOpen_ne_fun (by fun_prop) continuous_const
private theorem base_domain : archBase F ∈ archDomain F := by
  intro w
  simp [archBase]
 theorem choose_domain : ∃ V : Set (ArchCoordinates F), IsOpen V ∧ archBase F ∈ V ∧
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
 theorem product_smooth (V : Set (ArchCoordinates F))
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

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeChartProduct

end
