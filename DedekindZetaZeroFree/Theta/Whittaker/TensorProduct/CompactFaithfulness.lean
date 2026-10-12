module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.HighestRoot

@[expose] public section

noncomputable section
open scoped Classical Topology
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPCplxJacquetFunctional KPCplxIntertwinerEigenvalues TraceHaarTransport
open KPCplxHarmonicPropagation.RaisingCalculation
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem highest_intertwiner (n : ℕ) :
    standardIntertwiner standardComplexParameter (harmonicSection positiveParameter n) =
      (eigenvalue standardComplexParameter n:ℂ) • harmonicSection negativeParameter n := by
  apply compactRestriction_injective negativeParameter
  rw [(standardIntertwiner_harmonic_eigenvalue standardComplexParameter n _
    (harmonicSection_harmonic positiveParameter n)).2, map_smul,
    harmonicSection_compact, harmonicSection_compact]

theorem highest_positive_jacquet_ne_zero (n : ℕ) :
    jacquetFunctional standardComplexParameter (harmonicSection positiveParameter n) ≠ 0 := by
  have h := highestImage_jacquet_ne_zero n
  have he : intertwinerToImage standardComplexParameter (harmonicSection positiveParameter n) =
      (eigenvalue standardComplexParameter n:ℂ) • highestImage standardComplexParameter n := by
    apply Subtype.ext
    exact highest_intertwiner n
  rw [← thetaJacquetFunctional_intertwiner, he, map_smul, smul_eq_mul]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (eigenvalue_ne_zero _ _)) h

theorem jacquet_compacts_separate (f : PrincipalSeries positiveParameter)
    (hf : ∀ k : ComplexSU2, jacquetIntegral standardComplexParameter
      (KPCplxPrincipalSeriesCharts.pi positiveParameter (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k)) f) = 0) :
    f = 0 := by
  let J := jacquetFunctional standardComplexParameter
  let U : Submodule ℂ (PrincipalSeries positiveParameter) :=
    ⨅ k : ComplexSU2, (J.comp (jacquetEvaluationRightAction
      (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k)))).ker
  have hmem (x : PrincipalSeries positiveParameter) :
      x ∈ U ↔ ∀ k : ComplexSU2, J (KPCplxPrincipalSeriesCharts.pi positiveParameter
        (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k)) x) = 0 := by
    simp only [U, Submodule.mem_iInf, LinearMap.mem_ker,
      ContinuousLinearMap.coe_comp', Function.comp_apply]
    rfl
  have hc : IsClosed (U : Set (PrincipalSeries positiveParameter)) := by
    letI := principalSeries_t2 positiveParameter
    have he : (U : Set (PrincipalSeries positiveParameter)) =
        ⋂ k : ComplexSU2, ((J.comp (jacquetEvaluationRightAction
          (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k)))).ker :
            Set (PrincipalSeries positiveParameter)) := by
      ext x
      simp only [U, Set.mem_iInter, SetLike.mem_coe, Submodule.mem_iInf]
    rw [he]
    exact isClosed_iInter (fun k => (J.comp (jacquetEvaluationRightAction
      (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k)))).isClosed_ker)
  have hi : IsKInvariant positiveParameter U := by
    rintro ⟨g,k,hk⟩ x hx
    apply (hmem _).mpr
    intro a
    change J (KPCplxPrincipalSeriesCharts.pi positiveParameter (Matrix.ProjGenLinGroup.mk (complexSU2Embedding a))
      (KPCplxPrincipalSeriesCharts.pi positiveParameter g x)) = 0
    change Matrix.ProjGenLinGroup.mk (complexSU2Embedding k) = g at hk
    rw [← hk, ← pi_mul, ← map_mul, ← map_mul]
    exact (hmem x).mp hx (a*k)
  have hu : U = ⊥ := by
    by_contra hn
    obtain ⟨n,hU⟩ := KPCplxActualImageProof.closed_invariant_harmonic_extraction
      positiveParameter U hc hi hn
    have hh := hU (harmonicSection_harmonic positiveParameter n)
    have hz := (hmem _).mp hh 1
    simp only [map_one, pi_one] at hz
    exact highest_positive_jacquet_ne_zero n hz
  have hx : f ∈ U := (hmem f).mpr hf
  simpa only [hu, Submodule.mem_bot] using hx

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
