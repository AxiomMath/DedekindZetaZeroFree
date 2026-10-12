module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.SmoothExtensionByHarmonicDensity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactMatrixEvaluation
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexPrincipalSeries.TopologicalImage
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.FiniteDegreeEnergyEstimates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines.NativeStageSlot
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPActualReflectionData.LiteralProductEvaluator
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

def sourceEquiv : PrincipalSeries positiveParameter ≃L[ℂ] Theta (1 : ℂˣ) :=
  (standardIntertwiner_topological_image_isomorphism (1 : ℂˣ)).choose

theorem sourceEquiv_forward (f : PrincipalSeries positiveParameter) :
    sourceEquiv f = intertwinerToImage (1 : ℂˣ) f :=
  (standardIntertwiner_topological_image_isomorphism (1 : ℂˣ)).choose_spec.1 f

def inverse : PrincipalSeries negativeParameter →L[ℂ] PrincipalSeries positiveParameter :=
  sourceEquiv.symm.toContinuousLinearMap.comp
    ⟨(LinearMap.id : PrincipalSeries negativeParameter →ₗ[ℂ] _).codRestrict
      (imageSubmodule (1 : ℂˣ)) (by intro f; rw [imageSubmodule_eq_top]; trivial),
      continuous_id.subtype_mk _⟩

@[simp] theorem inverse_integral (f : PrincipalSeries positiveParameter) :
    inverse (KPCplxIntertwinerEigenvalues.standardIntertwiner (1 : ℂˣ) f) = f := by
  change sourceEquiv.symm (intertwinerToImage (1 : ℂˣ) f) = f
  rw [← sourceEquiv_forward, sourceEquiv.symm_apply_apply]

@[simp] theorem integral_inverse (f : PrincipalSeries negativeParameter) :
    KPCplxIntertwinerEigenvalues.standardIntertwiner (1 : ℂˣ) (inverse f) = f := by
  have h := congrArg Subtype.val (sourceEquiv.apply_symm_apply
    (⟨f, by rw [imageSubmodule_eq_top]; trivial⟩ : Theta (1 : ℂˣ)))
  rw [sourceEquiv_forward] at h
  exact h

theorem inverse_compact_bound (K : Set KPCplxCharacterHaar.ComplexGL2) (hK : IsCompact K) :
    ∃ orders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ (f : PrincipalSeries negativeParameter) (a : KPCplxCharacterHaar.ComplexGL2), a ∈ K →
        ‖(inverse f) a‖ ≤ B * (orders.sup (chartSeminorm negativeParameter)) f := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ev := KPActualReflectionData.LiteralProductPointBound.compactMatrixEvaluation
    positiveParameter K hK
  let Q : Seminorm ℂ (PrincipalSeries negativeParameter) :=
    (normSeminorm ℂ C(K, ℂ)).comp (ev.comp inverse.toLinearMap)
  have hQ : Continuous Q := continuous_norm.comp
    ((KPActualReflectionData.LiteralProductPointBound.compactMatrixEvaluation_continuous
      positiveParameter K hK).comp inverse.continuous)
  obtain ⟨orders, B, hB, hb⟩ := Seminorm.bound_of_continuous
    (show WithSeminorms (chartSeminorm negativeParameter) from ⟨rfl⟩) Q hQ
  exact ⟨orders, B, hB, fun f a ha =>
    ((ev (inverse f)).norm_coe_le_norm ⟨a, ha⟩).trans (hb f)⟩

end DedekindZetaZeroFree.FourierContinuation.ComplexLines.NativeStageSlot

end
