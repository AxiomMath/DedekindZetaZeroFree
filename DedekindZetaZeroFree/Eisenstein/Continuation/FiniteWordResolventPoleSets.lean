module

public import DedekindZetaZeroFree.Eisenstein.Continuation.FiniteWordLocalNumerator
public import DedekindZetaZeroFree.Eisenstein.Continuation.LocalPoleClearing
public import DedekindZetaZeroFree.Eisenstein.Continuation.ReconstructionDenominatorPoleSet

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource
open MomentSources ThetaExpansion ResidueContinuity.ScalarSourcePoleGeometry
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_pole_set
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (B : JointRootAlignedSources R N) (v : R.A.UnitQuotient) (D : SelectedScalarBranch R B v) :
    Nonempty (SelectedPoleSet D) := by
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
  obtain ⟨Q, A, hQ, hQ0, hch, hlocal⟩ :=
    finite_word_local_numerator F ζ hζ C Haar P H
      B.sources.K B.sources.iwasawa (B.sources.flat v)
  have hc : ∀ c ∈ KPContinuation.spectralDomain,
      ∃ (r : ℝ) (m : ℕ) (w : ℂ → Functions R),
        0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
        (∀ g, AnalyticOnNhd ℂ (fun s => w s g) (Metric.ball c r)) ∧
        ∀ s ∈ Metric.ball c r, s ≠ c → ∀ g, w s g = (s-c)^m * A s g := by
    intro c hc
    obtain ⟨r, w, hr, hb, ha, he⟩ := hlocal c hc
    exact ⟨r, 1, w, hr, hb, ha, fun s hs hn g => by simpa using he s hs hn g⟩
  let Z : Set ℂ := {s | s ∈ KPContinuation.spectralDomain ∧
    ∃ g, ¬ AnalyticAt ℂ (fun z => A z g) s}
  have hm := KPScalarContinuation.meromorphicOn_of_local_clearing A KPContinuation.spectralDomain hc
  have hi := KPScalarContinuation.scalar_singularities_isolated_of_local_clearing
    A KPContinuation.spectralDomain hc
  apply selectedPoleSet_of_weighted_comparison D Z (fun _ hs => hs.1) hi Q A
    hQ (by rw [hQ0]; exact one_ne_zero) hm hch
  intro s hs hn g
  by_contra ha
  exact hn ⟨hs, g, ha⟩

end DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource

end
