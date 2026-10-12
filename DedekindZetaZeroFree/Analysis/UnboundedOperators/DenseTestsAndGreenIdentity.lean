module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestEnergy

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree
namespace KPTestGreenTransfer

variable {S T H V : Type*}
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem laplacian_pairing
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w)))
    (f g : KPTestOperator.testDomain ι) :
    inner ℂ (KPTestOperator.descend ι hι j A f)
        (KPTestOperator.descend ι hι j A g) =
      inner ℂ (f : H) (KPTestOperator.laplacian ι hι A B g) := by
  rw [KPTestOperator.laplacian_eq_divergence_differential ι hι j hj A B g]
  exact KPTestOperator.descend_formalAdjoint ι hι j hj A B hgreen f
    ⟨KPTestOperator.descend ι hι j A g, KPTestOperator.descend_mem ι hι j A g⟩

theorem descend_dense_green
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hscalar : DenseRange ι) (hcotangent : DenseRange j)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w))) :
    Dense (KPTestOperator.testDomain ι : Set H) ∧
      Dense (KPTestOperator.testDomain j : Set V) ∧
      (KPTestOperator.descend ι hι j A).IsFormalAdjoint
        (KPTestOperator.descend j hj ι B) ∧
      (∀ (f : KPTestOperator.testDomain ι) (w : KPTestOperator.testDomain j),
        inner ℂ (KPTestOperator.descend ι hι j A f) (w : V) =
          inner ℂ (f : H) (KPTestOperator.descend j hj ι B w)) ∧
      (∀ f g : KPTestOperator.testDomain ι,
        inner ℂ (KPTestOperator.descend ι hι j A f)
            (KPTestOperator.descend ι hι j A g) =
          inner ℂ (f : H) (KPTestOperator.laplacian ι hι A B g)) := by
  have hs : Dense (KPTestOperator.testDomain ι : Set H) := by
    simpa only [KPTestOperator.testDomain, LinearMap.coe_range, DenseRange] using hscalar
  have ht : Dense (KPTestOperator.testDomain j : Set V) := by
    simpa only [KPTestOperator.testDomain, LinearMap.coe_range, DenseRange] using hcotangent
  have hf := KPTestOperator.descend_formalAdjoint ι hι j hj A B hgreen
  exact ⟨hs, ht, hf, hf, laplacian_pairing ι hι j hj A B hgreen⟩

end KPTestGreenTransfer
end DedekindZetaZeroFree

end
