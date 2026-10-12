module

public import DedekindZetaZeroFree.Adeles.Quotients.ExponentialChartsAndRightLieFields
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PGLComplex.ExponentialCoordinates

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LocalQuotientCharts.ExponentialHaarFrame
open Raw
open scoped NumberField Classical Manifold ContDiff Matrix.Norms.Operator

def coordinateReindex (F : Type) [Field F] [NumberField F] :
    Coordinates F ≃L[ℝ] PGLComplex.ProductCoordinates (NumberField.InfinitePlace F) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : NumberField.InfinitePlace F × Fin 6 => ℝ)
    (Equiv.prodCongr (Equiv.refl (NumberField.InfinitePlace F))
      (finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6)))

end DedekindZetaZeroFree.LocalQuotientCharts.ExponentialHaarFrame

end

section

noncomputable section
namespace DedekindZetaZeroFree.LocalQuotientCharts.ExponentialHaarFrame
open Raw
open scoped NumberField Classical Manifold ContDiff Matrix.Norms.Operator

def rawAffineChart (F : Type) [Field F] [NumberField F] (g : ArchGroup F) :
    OpenPartialHomeomorph (Coordinates F) (ArchGroup F) :=
  (coordinateReindex F).toHomeomorph.toOpenPartialHomeomorph.trans
    (PGLComplex.productAffineChart (NumberField.InfinitePlace F) (fun w =>
      (PGLComplex.affineChart.trans
        (Homeomorph.mulLeft (g w)).toOpenPartialHomeomorph).symm)).symm

def reindexChart (F : Type) [Field F] [NumberField F] :
    OpenPartialHomeomorph (Coordinates F)
      (PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) :=
  (coordinateReindex F).toHomeomorph.toOpenPartialHomeomorph

@[instance_reducible]
def reindexChartedSpace (F : Type) [Field F] [NumberField F] :
    ChartedSpace (Coordinates F)
      (PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) where
  atlas := {reindexChart F |>.symm}
  chartAt := fun _ => (reindexChart F).symm
  mem_chart_source := fun _ => by simp [reindexChart]
  chart_mem_atlas := fun _ => Set.mem_singleton _

theorem chartAt_reindexChartedSpace (F : Type) [Field F] [NumberField F]
    (x : PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) :
    @chartAt _ _ _ _ (reindexChartedSpace F) x = (reindexChart F).symm := rfl

theorem extend_self_model (F : Type) [Field F] [NumberField F]
    (e : OpenPartialHomeomorph (Coordinates F)
      (PGLComplex.ProductCoordinates (NumberField.InfinitePlace F))) :
    e.extend 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) =
      e.toPartialEquiv := by
  have h : 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)).toPartialEquiv
      = PartialEquiv.refl _ := by ext <;> simp
  simp only [OpenPartialHomeomorph.extend, h, PartialEquiv.trans_refl]

section ReindexTransport

variable (F : Type) [Field F] [NumberField F]
variable {M : Type*} [TopologicalSpace M] [C₀ : ChartedSpace (PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) M]
@[instance_reducible] private def transported : ChartedSpace (Coordinates F) M := by
  letI := reindexChartedSpace F
  exact ChartedSpace.comp (Coordinates F) (PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) M
private theorem ext_transport (x : M) :
    (letI := transported F (M := M); extChartAt 𝓘(ℝ, Coordinates F) x) =
    (extChartAt 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) x).trans
      (reindexChart F).symm.toPartialEquiv := by
  letI := reindexChartedSpace F
  change ((chartAt (PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) x).trans
    (reindexChart F).symm).extend 𝓘(ℝ, Coordinates F) = _
  have h {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] :
      (𝓘(ℝ, V)).toPartialEquiv = PartialEquiv.refl V := by ext <;> simp
  simp only [extChartAt, OpenPartialHomeomorph.extend, h, PartialEquiv.trans_refl,
    chartAt_reindexChartedSpace]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
private theorem smooth_transport_right {n : ℕ∞ω} {f : N → M}
    (hf : ContMDiff I 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) n f) :
    letI := transported F (M := M)
    ContMDiff I 𝓘(ℝ, Coordinates F) n f := by
  letI := transported F (M := M)
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨(hf x).continuousAt, ?_⟩
  have hc := (contMDiffAt_iff.mp (hf x)).2
  rw [ext_transport]
  exact (coordinateReindex F).symm.contDiff.contDiffAt.comp_contDiffWithinAt _ hc

private theorem smooth_transport_left {n : ℕ∞ω} {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) I n f) :
    letI := transported F (M := M)
    ContMDiff 𝓘(ℝ, Coordinates F) I n f := by
  letI := transported F (M := M)
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨(hf x).continuousAt, ?_⟩
  have hc := (contMDiffAt_iff.mp (hf x)).2
  simp only [modelWithCornersSelf_coe, Set.range_id] at hc ⊢
  rw [ext_transport]
  have hc' : ContDiffAt ℝ n
      ((extChartAt I (f x)) ∘ f ∘ (extChartAt 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) x).symm)
      ((coordinateReindex F) ((coordinateReindex F).symm
        (extChartAt 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) x x))) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using contDiffWithinAt_univ.mp hc
  have hh := hc'.comp ((coordinateReindex F).symm
      (extChartAt 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) x x))
    ((coordinateReindex F).contDiff.contDiffAt (x := (coordinateReindex F).symm
      (extChartAt 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) x x)))
  convert hh.contDiffWithinAt using 1 <;> rfl

private theorem manifold_transport [IsManifold 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) ∞ M] :
    letI := transported F (M := M)
    IsManifold 𝓘(ℝ, Coordinates F) ∞ M := by
  letI := transported F (M := M)
  apply isManifold_of_contDiffOn
  intro e f he hf
  obtain ⟨e, he, e', he', rfl⟩ := he
  obtain ⟨f, hf, f', hf', rfl⟩ := hf
  change e' ∈ {(reindexChart F).symm} at he'
  change f' ∈ {(reindexChart F).symm} at hf'
  obtain rfl := Set.mem_singleton_iff.mp he'
  obtain rfl := Set.mem_singleton_iff.mp hf'
  have hc := (𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F))).contDiffOn_extendCoordChange
    (IsManifold.subset_maximalAtlas (n := ∞) (I := 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F))) he)
    (IsManifold.subset_maximalAtlas (n := ∞) (I := 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F))) hf)
  simp only [ModelWithCorners.extendCoordChange, modelWithCornersSelf_coe, Function.id_comp,
    Function.comp_id, Set.range_id, Set.preimage_id_eq, Set.inter_univ] at hc ⊢
  have h : (𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F))).toPartialEquiv = PartialEquiv.refl _ := by ext <;> simp
  simp only [OpenPartialHomeomorph.extend, h, PartialEquiv.trans_refl] at hc
  change ContDiffOn ℝ ∞ (fun a => f (e.symm a)) (e.target ∩ e.symm ⁻¹' f.source) at hc
  change ContDiffOn ℝ ∞ (fun a => (coordinateReindex F).symm (f (e.symm ((coordinateReindex F) a)))) _
  apply (coordinateReindex F).symm.contDiff.contDiffOn.comp
  · apply hc.comp (coordinateReindex F).contDiff.contDiffOn
    intro a ha
    exact ⟨ha.1.2, ha.2.1⟩
  · exact Set.mapsTo_univ _ _

private def identity_transport : letI := transported F (M := M)
    Diffeomorph 𝓘(ℝ, Coordinates F) 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) M M ∞ := by
  letI := transported F (M := M)
  exact { Homeomorph.refl M with
    contMDiff_toFun := smooth_transport_left F contMDiff_id
    contMDiff_invFun := smooth_transport_right F contMDiff_id }

private theorem lie_transport [Group M]
    [LieGroup 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) ∞ M] :
    letI := transported F (M := M)
    LieGroup 𝓘(ℝ, Coordinates F) ∞ M := by
  let e := identity_transport F (M := M)
  letI := transported F (M := M)
  letI := manifold_transport F (M := M)
  have hm : ContMDiff (𝓘(ℝ, Coordinates F).prod 𝓘(ℝ, Coordinates F))
      𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) ∞
      (fun p : M × M => p.1 * p.2) := by
    exact (e.contMDiff.comp contMDiff_fst).mul (e.contMDiff.comp contMDiff_snd)
  letI : ContMDiffMul 𝓘(ℝ, Coordinates F) ∞ M := {
    contMDiff_mul := e.symm.contMDiff.comp hm }
  exact { contMDiff_inv := e.symm.contMDiff.comp ((e.contMDiff).inv) }

private def indexReindex : (NumberField.InfinitePlace F × Fin 3 × Fin 2) ≃ (NumberField.InfinitePlace F × Fin 6) :=
  Equiv.prodCongr (Equiv.refl _) finProdFinEquiv

private theorem exponential_reindex :
    PGLComplex.productExponential (NumberField.InfinitePlace F) ∘ coordinateReindex F = matrixExp F := by
  funext a w
  unfold PGLComplex.productExponential PGLComplex.exponential matrixExp
  have hm : PGLComplex.sl2Matrix ((PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F)).symm (coordinateReindex F a) w) = lieMatrix F a w := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [lieMatrix, PGLComplex.sl2Matrix, PGLComplex.productCoordinatesFlatten,
        coordinateReindex, ContinuousLinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft,
        Equiv.piCongrLeft, Equiv.piCongrLeft', finProdFinEquiv] <;> rfl
  change Matrix.ProjGenLinGroup.mk ((NormedSpace.isUnit_exp (PGLComplex.sl2Matrix
    ((PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F)).symm (coordinateReindex F a) w))).unit) = _
  rw [hm]

private def reindexedData [Group M]
    [LieGroup 𝓘(ℝ, PGLComplex.ProductCoordinates (NumberField.InfinitePlace F)) ∞ M]
    (D : HilbertLieExponentialData M (PGLComplex.ProductCoordinates (NumberField.InfinitePlace F))
      (NumberField.InfinitePlace F × Fin 6)) :
    letI := transported F (M := M)
    letI := lie_transport F (M := M)
    HilbertLieExponentialData M (Coordinates F) (NumberField.InfinitePlace F × Fin 3 × Fin 2) := by
  let e := identity_transport F (M := M)
  let r := coordinateReindex F
  let b := (D.basis.map r.symm.toLinearEquiv).reindex (indexReindex F).symm
  let E₀ := r.toDiffeomorph.toPartialDiffeomorph.trans D.exponentialChart
  letI := transported F (M := M)
  letI := lie_transport F (M := M)
  let EP := E₀.trans e.symm.toPartialDiffeomorph
  refine { basis := b
           exponential := D.exponential ∘ r
           exponential_zero := ?_
           exponential_add_ray := ?_
           exponential_smooth := e.symm.contMDiff.comp (D.exponential_smooth.comp r.contDiff.contMDiff)
           exponentialChart := EP
           zero_mem_source := ?_
           chart_eq_exponential := ?_
           adjoint := fun g => r.toLinearEquiv.trans ((D.adjoint g).trans r.symm.toLinearEquiv)
           adjoint_smooth := ?_
           exponential_conjugation := ?_ }
  · simpa using D.exponential_zero
  · intro X s t
    simpa only [Function.comp_apply, map_smul] using D.exponential_add_ray (r X) s t
  · refine ⟨⟨Set.mem_univ _, ?_⟩, Set.mem_univ _⟩
    change r 0 ∈ D.exponentialChart.source
    simpa using D.zero_mem_source
  · intro a ha
    exact D.chart_eq_exponential _ ha.1.2
  · intro a c
    have h := e.contMDiff
    have hh := (D.adjoint_smooth ((indexReindex F) a) ((indexReindex F) c)).comp h
    convert hh using 1
    funext g
    simp [b, Module.Basis.equivFun, Module.Basis.reindex_apply, Module.Basis.map_apply,
      LinearEquiv.trans_apply, r]
    rfl
  · intro g X
    simpa only [Function.comp_apply, LinearEquiv.trans_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply] using D.exponential_conjugation g (r X)

end ReindexTransport

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

theorem raw_lie_exponential_data (F : Type) [Field F] [NumberField F] :
    ∃ C : ChartedSpace (Coordinates F) (ArchGroup F),
      letI := C
      ∃ L : LieGroup (𝓘(ℝ, Coordinates F)) (⊤ : ℕ∞) (ArchGroup F),
        letI := L
        ∃ D : HilbertLieExponentialData (ArchGroup F) (Coordinates F)
          (NumberField.InfinitePlace F × Fin 3 × Fin 2),
          D.exponential = matrixExp F ∧
          (∀ b, D.basis b = Pi.single b 1) ∧
          (∀ g, chartAt (Coordinates F) g = (rawAffineChart F g).symm) := by
  let ι := NumberField.InfinitePlace F
  letI : Fintype ι := inferInstance
  obtain ⟨C₀, L₀, hC₀⟩ := PGLComplex.affine_lie_structure
  letI := C₀
  letI := L₀
  obtain ⟨D₀, hD₀, _, _⟩ := PGLComplex.single_lie_exponential_data hC₀
  let CP := PGLComplex.productAffineChartedSpace ι (C := C₀)
  letI := CP
  let LP := PGLComplex.productAffineLieGroup ι (C := C₀)
  letI := LP
  let EP := PGLComplex.productExponentialDiffeomorph ι D₀
  have hs : ContMDiff (𝓘(ℝ, PGLComplex.ProductCoordinates ι)) (𝓘(ℝ, PGLComplex.ProductCoordinates ι))
      (⊤ : ℕ∞) (PGLComplex.productExponential ι) := by
    apply PGLComplex.product_contMDiff
    intro i
    exact (PGLComplex.exponential_contMDiff hC₀).comp
      (((contDiff_apply ℝ PGLComplex.Coordinates i).comp
        (PGLComplex.productCoordinatesFlatten ι).symm.contDiff).contMDiff)
  have ha (a b : ι × Fin 6) :
      ContMDiff (𝓘(ℝ, PGLComplex.ProductCoordinates ι)) (𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
        (fun g : PGLComplex.ProductGroup ι => PGLComplex.productAdjointMatrix ι g a b) := by
    by_cases hab : a.1 = b.1
    · have hh := (PGLComplex.adjointMatrix_contMDiff hC₀ a.2 b.2).comp
          (PGLComplex.product_projection_contMDiff (C := C₀) a.1)
      change ContMDiff (𝓘(ℝ, PGLComplex.ProductCoordinates ι)) (𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
        (fun g : PGLComplex.ProductGroup ι => PGLComplex.adjointMatrix (g a.1) a.2 b.2) at hh
      exact hh.congr (fun g => by simp [PGLComplex.productAdjointMatrix, hab])
    · simp only [PGLComplex.productAdjointMatrix, hab, ↓reduceIte]
      exact contMDiff_const
  let DP : HilbertLieExponentialData (PGLComplex.ProductGroup ι) (PGLComplex.ProductCoordinates ι) (ι × Fin 6) :=
    { basis := Pi.basisFun ℝ (ι × Fin 6)
      exponential := PGLComplex.productExponential ι
      exponential_zero := PGLComplex.productExponential_zero ι
      exponential_add_ray := PGLComplex.productExponential_add_ray ι
      exponential_smooth := hs
      exponentialChart := EP
      zero_mem_source := ⟨Set.mem_univ _, fun i _ => D₀.zero_mem_source⟩
      chart_eq_exponential := by
        intro a ha
        funext i
        change D₀.exponentialChart ((PGLComplex.productCoordinatesFlatten ι).symm a i) = _
        have hi : (PGLComplex.productCoordinatesFlatten ι).symm a i ∈ D₀.exponentialChart.source :=
          ha.2 i (Set.mem_univ i)
        rw [D₀.chart_eq_exponential _ hi, hD₀]
        rfl
      adjoint := PGLComplex.productAdjointLinearEquiv ι
      adjoint_smooth := by
        intro a b
        simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_apply,
          PGLComplex.productAdjointLinearEquiv_basis] using ha a b
      exponential_conjugation := PGLComplex.productExponential_adjoint ι }
  let D := reindexedData F DP
  let C := transported F (M := ArchGroup F)
  let L := lie_transport F (M := ArchGroup F)
  refine ⟨C, L, D, ?_, ?_, ?_⟩
  · exact exponential_reindex F
  · intro b
    dsimp [D, reindexedData]
    simp only [Module.Basis.reindex_apply, Module.Basis.map_apply, Equiv.symm_symm]
    change (coordinateReindex F).symm ((Pi.basisFun ℝ (ι × Fin 6)) ((indexReindex F) b)) = Pi.single b 1
    ext c
    change (Pi.basisFun ℝ (ι × Fin 6)) ((indexReindex F) b) ((indexReindex F) c) = (Pi.single b 1 : Coordinates F) c
    simp [Pi.basisFun_apply, Pi.single_apply, (indexReindex F).injective.eq_iff]
  · intro g
    change (PGLComplex.productAffineChart ι (fun w => chartAt PGLComplex.Coordinates (g w))).trans
      (reindexChart F).symm = (rawAffineChart F g).symm
    simp only [rawAffineChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    congr 1
    exact congrArg (PGLComplex.productAffineChart ι) (funext (fun w => hC₀ (g w)))

end DedekindZetaZeroFree.LocalQuotientCharts.ExponentialHaarFrame

end
end
