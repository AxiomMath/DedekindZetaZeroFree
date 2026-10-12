module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberComparisonAndPoleOrders

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource
open MomentSources ThetaExpansion
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.FiniteWordNumerator renaming finite_word_numerator → finite_word_numerator

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_scalar_order_zero
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (B : JointRootAlignedSources R N) (v : R.A.UnitQuotient) (D : SelectedScalarBranch R B v) :
    ∀ g, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => D.E s g) 0 := by
  let ζ := R.A.zeta12
  let hζ := R.A.primitive_zeta12
  letI : T2Space (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨C, _⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨Haar, _, _, P, ⟨H⟩⟩ :=
    kp_ms_fixed_haar_disintegration F ζ hζ
      (Measure.haar : Measure (KPLiteralRaw.G F ζ hζ)) inferInstance
  obtain ⟨Q, A, T, r, hQ, hQ0, hA, hch, hr, _, _, hT, hclear⟩ :=
    finite_word_numerator F ζ hζ C Haar P H
      B.sources.K B.sources.iwasawa (B.sources.flat v)
  apply ResidueContinuity.selected_order_of_reconstruction_numerator D Q A hQ hQ0 hA hch
  intro g
  refine ⟨fun s => T s g, hT g 0 (Metric.mem_ball_self hr), ?_⟩
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
    self_mem_nhdsWithin] with s hs hne
  exact hclear s hs hne g

end DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource

end
