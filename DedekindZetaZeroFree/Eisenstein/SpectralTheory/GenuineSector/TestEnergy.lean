module

public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.ChartGreenIdentities
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree
namespace KPTestOperator
variable {S T H V : Type*}
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

abbrev testDomain (ι : S →ₗ[ℂ] H) : Submodule ℂ H := ι.range

def representative (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι) :
    testDomain ι ≃ₗ[ℂ] S := (LinearEquiv.ofInjective ι hι).symm

def descend (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (A : S →ₗ[ℂ] T) : H →ₗ.[ℂ] V :=
  ⟨testDomain ι, j.comp (A.comp (representative ι hι).toLinearMap)⟩

@[simp] theorem descend_domain (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (A : S →ₗ[ℂ] T) :
    (descend ι hι j A).domain = testDomain ι := rfl

@[simp] theorem representative_image (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (f : S) : representative ι hι ⟨ι f, LinearMap.mem_range_self ι f⟩ = f := by
  exact (LinearEquiv.ofInjective ι hι).symm_apply_apply f

@[simp] theorem image_representative (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (f : testDomain ι) : ι (representative ι hι f) = f :=
  LinearEquiv.ofInjective_symm_apply ι f

@[simp] theorem descend_image (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (A : S →ₗ[ℂ] T) (f : S) :
    descend ι hι j A ⟨ι f, LinearMap.mem_range_self ι f⟩ = j (A f) := by
  change j (A (representative ι hι ⟨ι f, _⟩)) = _
  rw [representative_image]

theorem descend_mem (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (A : S →ₗ[ℂ] T) (f : testDomain ι) :
    descend ι hι j A f ∈ testDomain j :=
  LinearMap.mem_range_self j _

def laplacian (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S) : testDomain ι →ₗ[ℂ] H :=
  ι.comp (B.comp (A.comp (representative ι hι).toLinearMap))

theorem laplacian_eq_divergence_differential
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S) (f : testDomain ι) :
    laplacian ι hι A B f =
      descend j hj ι B ⟨descend ι hι j A f, descend_mem ι hι j A f⟩ := by
  change ι (B (A (representative ι hι f))) =
    ι (B (representative j hj ⟨j (A (representative ι hι f)), _⟩))
  rw [representative_image]

theorem descend_formalAdjoint
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w))) :
    (descend ι hι j A).IsFormalAdjoint (descend j hj ι B) := by
  intro f w
  change inner ℂ (j (A (representative ι hι f))) (w : V) =
    inner ℂ (f : H) (ι (B (representative j hj w)))
  rw [← image_representative j hj w, ← image_representative ι hι f]
  exact hgreen _ _

end KPTestOperator

namespace KPTestL2
open MeasureTheory
variable {S X W : Type*} [AddCommGroup S] [Module ℂ S]
  [MeasurableSpace X] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def embedding (μ : Measure X) (e : S →ₗ[ℂ] (X → W))
    (he : ∀ f : S, MemLp (e f) 2 μ) : S →ₗ[ℂ] Lp W 2 μ where
  toFun f := (he f).toLp (e f)
  map_add' f g := by
    simpa only [map_add] using (MemLp.toLp_add (he f) (he g))
  map_smul' c f := by
    simpa only [map_smul, RingHom.id_apply] using (MemLp.toLp_const_smul c (he f))

theorem integrable_pairing (μ : Measure X) (f g : X → W)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℂ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

end KPTestL2
end DedekindZetaZeroFree

end
