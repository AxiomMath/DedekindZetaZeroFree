module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FriedrichsTestLaplacianExtension

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree
namespace KPTestFriedrichs

variable {S T H V : Type*}
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem gradient_closable
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hcotangent : DenseRange j)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w))) :
    (KPTestOperator.descend ι hι j A).IsClosable := by
  have ht : Dense ((KPTestOperator.descend j hj ι B).domain : Set V) := by
    simpa only [KPTestOperator.descend_domain, KPTestOperator.testDomain,
      LinearMap.coe_range, DenseRange] using hcotangent
  exact (formalAdjoint_gradient_closable _ _ ht
    (KPTestOperator.descend_formalAdjoint ι hι j hj A B hgreen)).2.1

def resolvent
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hcotangent : DenseRange j)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w))) : H →L[ℂ] H :=
  closedGradientResolvent (KPTestOperator.descend ι hι j A)
    (gradient_closable ι hι j hj A B hcotangent hgreen)

def laplacian
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hscalar : DenseRange ι) (hcotangent : DenseRange j)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w))) : H →ₗ.[ℂ] H :=
  closedGradientFriedrichsOperator (KPTestOperator.descend ι hι j A)
    (by simpa only [KPTestOperator.descend_domain, KPTestOperator.testDomain,
      LinearMap.coe_range, DenseRange] using hscalar)
    (gradient_closable ι hι j hj A B hcotangent hgreen)

theorem hilbert_laplacian
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hscalar : DenseRange ι) (hcotangent : DenseRange j)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w))) :
    let D := KPTestOperator.descend ι hι j A
    let Δ := laplacian ι hι j hj A B hscalar hcotangent hgreen
    let R := resolvent ι hι j hj A B hcotangent hgreen
    Dense (D.domain : Set H) ∧ D.IsClosable ∧
      (∀ f : D.domain, 0 ≤ ‖D f‖ ^ 2) ∧
      (∀ (s : ℕ → D.domain),
        Filter.Tendsto (fun n => (s n : H)) Filter.atTop (nhds 0) →
        CauchySeq (fun n => D (s n)) →
        Filter.Tendsto (fun n => D (s n)) Filter.atTop (nhds 0)) ∧
      CompleteSpace (ClosedGradientSpace D) ∧
      Dense (D.closure.domain : Set H) ∧
      (∀ u : D.closure.domain,
        0 ≤ closedGradientEnergy D u ∧
        closedGradientForm D u u = (closedGradientEnergy D u : ℂ)) ∧
      (∀ u : D.closure.domain, ∃ s : ℕ → D.domain,
        Filter.Tendsto (fun n => (s n : H)) Filter.atTop (nhds (u : H)) ∧
        Filter.Tendsto (fun n => D (s n)) Filter.atTop (nhds (D.closure u)) ∧
        Filter.Tendsto (fun n => ‖D (s n)‖ ^ 2) Filter.atTop
          (nhds (closedGradientEnergy D u))) ∧
      (∀ f g : D.domain,
        closedGradientForm D ⟨(f : H), D.le_closure.1 f.property⟩
          ⟨(g : H), D.le_closure.1 g.property⟩ = inner ℂ (D f) (D g)) ∧
      (∀ (s : ℕ → D.domain) (u : H),
        Filter.Tendsto (fun n => (s n : H)) Filter.atTop (nhds u) →
        CauchySeq (fun n => D (s n)) →
        ∃ hu : u ∈ D.closure.domain,
          Filter.Tendsto (fun n => D (s n)) Filter.atTop
            (nhds (D.closure ⟨u, hu⟩)) ∧
          Filter.Tendsto (fun n => ‖D (s n)‖ ^ 2) Filter.atTop
            (nhds (closedGradientEnergy D ⟨u, hu⟩))) ∧
      IsSelfAdjoint Δ ∧ Δ.IsClosed ∧
      (∀ u : Δ.domain, 0 ≤ (inner ℂ (u : H) (Δ u)).re) ∧
      ClosedGradientVariationalAssociation D Δ ∧
      (∀ f : KPTestOperator.testDomain ι,
        ∃ hf : (f : H) ∈ Δ.domain,
          Δ ⟨(f : H), hf⟩ = KPTestOperator.laplacian ι hι A B f) ∧
      IsSelfAdjoint R ∧ ‖R‖ ≤ 1 ∧ Function.Injective R ∧ DenseRange R ∧
      (∀ f : H, ∃ hf : R f ∈ Δ.domain, R f + Δ ⟨R f, hf⟩ = f) ∧
      (∀ u : Δ.domain, R ((u : H) + Δ u) = (u : H)) := by
  dsimp only
  let D := KPTestOperator.descend ι hι j A
  have hd : Dense (D.domain : Set H) := by
    simpa only [D, KPTestOperator.descend_domain, KPTestOperator.testDomain,
      LinearMap.coe_range, DenseRange] using hscalar
  have hc : D.IsClosable := gradient_closable ι hι j hj A B hcotangent hgreen
  letI : CompleteSpace (ClosedGradientSpace D) := closedGradientSpace_complete D hc
  have he := closedGradientEmbedding_properties D hd hc
  have hr := energyRieszResolvent_properties (closedGradientEmbedding D)
    he.2.1 he.2.2.1 he.1
  have ho := kp_cont_resolvent_selfadjoint_operator (closedGradientResolvent D hc)
    hr.1 hr.2.2.1 hr.2.2.2.1
    (fun f => (energyRieszResolvent_estimates (closedGradientEmbedding D) he.1 f).1)
  have hf := closedGradientForm_nonnegative_dense D hd hc
  refine ⟨hd, hc, fun f => sq_nonneg _, gradientQuadraticForm_closable D hc,
    inferInstance, hf.1, hf.2, closedGradientForm_core D hc,
    closedGradientForm_extends D, closedGradientForm_closure_characterization D hc,
    ho.1, ho.2.1, ho.2.2.1, ?_, ?_, hr.1, hr.2.2.2.2,
    hr.2.2.1, hr.2.2.2.1, ho.2.2.2.1, ho.2.2.2.2.1⟩
  · change ClosedGradientVariationalAssociation D (closedGradientFriedrichsOperator D hd hc)
    intro u h
    constructor
    · rintro ⟨hu, hvalue⟩
      have huForm := closedGradientFriedrichsOperator_domain_subset D hd hc hu
      refine ⟨huForm, ?_⟩
      exact (closedGradientFriedrichsOperator_variational D hd hc ⟨u, huForm⟩ h).mp
        ⟨hu, hvalue⟩
    · rintro ⟨hu, hform⟩
      exact (closedGradientFriedrichsOperator_variational D hd hc ⟨u, hu⟩ h).mpr hform
  · exact (KPTestGreenTransfer.friedrichs_extends_test_laplacian
      ι hι j hj A B hscalar hcotangent hgreen).2

end KPTestFriedrichs
end DedekindZetaZeroFree

end
