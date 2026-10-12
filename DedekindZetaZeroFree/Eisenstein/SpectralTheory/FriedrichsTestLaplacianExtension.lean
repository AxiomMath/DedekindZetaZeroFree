module

public import DedekindZetaZeroFree.Analysis.UnboundedOperators.DenseTestsAndGreenIdentity
public import DedekindZetaZeroFree.Analysis.UnboundedOperators.FormalAdjointClosability
public import DedekindZetaZeroFree.Analysis.QuadraticForms.FriedrichsVariationalDomain

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree

private theorem closedGradient_test_inner_eq
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (δ : V →ₗ.[ℂ] H)
    (hclosable : D.IsClosable) (hformal : D.IsFormalAdjoint δ)
    (himage : ∀ f : D.domain, D f ∈ δ.domain) (f : D.domain) (v : D.closure.domain) :
    inner ℂ (D.closure ⟨(f : H), D.le_closure.1 f.property⟩) (D.closure v) =
      inner ℂ (δ ⟨D f, himage f⟩) (v : H) := by
  obtain ⟨s, hsH, hsV, -⟩ := closedGradientForm_core D hclosable v
  have hkey : ∀ n : ℕ,
      inner ℂ ((s n : H)) (δ ⟨D f, himage f⟩) = inner ℂ (D (s n)) (D f) :=
    fun n => (hformal (s n) ⟨D f, himage f⟩).symm
  have h1 : Filter.Tendsto (fun n : ℕ => inner ℂ ((s n : H)) (δ ⟨D f, himage f⟩))
      Filter.atTop (nhds (inner ℂ (v : H) (δ ⟨D f, himage f⟩))) :=
    hsH.inner tendsto_const_nhds
  have h2 : Filter.Tendsto (fun n : ℕ => inner ℂ (D (s n)) (D f))
      Filter.atTop (nhds (inner ℂ (D.closure v) (D f))) :=
    hsV.inner tendsto_const_nhds
  have hlim : inner ℂ (v : H) (δ ⟨D f, himage f⟩) = inner ℂ (D.closure v) (D f) :=
    tendsto_nhds_unique_of_forall h1 h2 hkey
  rw [← D.le_closure.2 (rfl : (f : H) =
    (⟨(f : H), D.le_closure.1 f.property⟩ : D.closure.domain))]
  rw [← inner_conj_symm (D f) (D.closure v),
    ← inner_conj_symm (δ ⟨D f, himage f⟩) (v : H), hlim]

theorem closedGradientFriedrichsOperator_test_domain
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (δ : V →ₗ.[ℂ] H)
    (hdense : Dense (D.domain : Set H)) (hclosable : D.IsClosable)
    (hδ : Dense (δ.domain : Set V)) (hformal : D.IsFormalAdjoint δ)
    (himage : ∀ f : D.domain, D f ∈ δ.domain) :
    D.domain ≤ (closedGradientFriedrichsOperator D hdense hclosable).domain := by
  intro f hf
  exact ((closedGradientFriedrichsOperator_variational D hdense hclosable
      ⟨f, D.le_closure.1 hf⟩ (δ ⟨D ⟨f, hf⟩, himage ⟨f, hf⟩⟩)).mpr
      (fun v => closedGradient_test_inner_eq D δ hclosable hformal himage
        ⟨f, hf⟩ v)).1

theorem kp_cont_smooth_test_operator_extension
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (δ : V →ₗ.[ℂ] H)
    (hdense : Dense (D.domain : Set H)) (hclosable : D.IsClosable)
    (hδ : Dense (δ.domain : Set V)) (hformal : D.IsFormalAdjoint δ)
    (himage : ∀ f : D.domain, D f ∈ δ.domain) :
    ∀ f : D.domain,
      closedGradientFriedrichsOperator D hdense hclosable
        ⟨(f : H), closedGradientFriedrichsOperator_test_domain
          D δ hdense hclosable hδ hformal himage f.property⟩ =
        δ ⟨D f, himage f⟩ := by
  intro f
  have h := (closedGradientFriedrichsOperator_variational D hdense hclosable
      ⟨(f : H), D.le_closure.1 f.property⟩ (δ ⟨D f, himage f⟩)).mpr
      (fun v => closedGradient_test_inner_eq D δ hclosable hformal himage f v)
  have hsub : (⟨(f : H), closedGradientFriedrichsOperator_test_domain
        D δ hdense hclosable hδ hformal himage f.property⟩ :
        (closedGradientFriedrichsOperator D hdense hclosable).domain)
      = ⟨(f : H), h.1⟩ := Subtype.ext rfl
  rw [hsub]
  exact h.2

namespace KPTestGreenTransfer

theorem friedrichs_extends_test_laplacian
    {S T H V : Type*}
    [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hscalar : DenseRange ι) (hcotangent : DenseRange j)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w))) :
    let D := KPTestOperator.descend ι hι j A
    let δ := KPTestOperator.descend j hj ι B
    let htransfer := descend_dense_green ι hι j hj A B hscalar hcotangent hgreen
    let hdense : Dense (D.domain : Set H) := htransfer.1
    let hδ : Dense (δ.domain : Set V) := htransfer.2.1
    let hformal : D.IsFormalAdjoint δ := htransfer.2.2.1
    let hclosable : D.IsClosable :=
      (formalAdjoint_gradient_closable D δ hδ hformal).2.1
    let Δ := closedGradientFriedrichsOperator D hdense hclosable
    KPTestOperator.testDomain ι ≤ Δ.domain ∧
      ∀ f : KPTestOperator.testDomain ι,
        ∃ hf : (f : H) ∈ Δ.domain,
          Δ ⟨(f : H), hf⟩ = KPTestOperator.laplacian ι hι A B f := by
  dsimp only
  obtain ⟨hdense, hδ, hformal, -, -⟩ :=
    descend_dense_green ι hι j hj A B hscalar hcotangent hgreen
  have hclosable : (KPTestOperator.descend ι hι j A).IsClosable :=
    (formalAdjoint_gradient_closable _ _ hδ hformal).2.1
  have himage : ∀ f : (KPTestOperator.descend ι hι j A).domain,
      KPTestOperator.descend ι hι j A f ∈ (KPTestOperator.descend j hj ι B).domain :=
    fun f => KPTestOperator.descend_mem ι hι j A f
  refine ⟨?_, ?_⟩
  · exact closedGradientFriedrichsOperator_test_domain
      (KPTestOperator.descend ι hι j A) (KPTestOperator.descend j hj ι B)
      hdense hclosable hδ hformal himage
  · intro f
    refine ⟨closedGradientFriedrichsOperator_test_domain
        (KPTestOperator.descend ι hι j A) (KPTestOperator.descend j hj ι B)
        hdense hclosable hδ hformal himage f.property, ?_⟩
    rw [kp_cont_smooth_test_operator_extension
        (KPTestOperator.descend ι hι j A) (KPTestOperator.descend j hj ι B)
        hdense hclosable hδ hformal himage f,
      KPTestOperator.laplacian_eq_divergence_differential ι hι j hj A B f]

end KPTestGreenTransfer
end DedekindZetaZeroFree

end
