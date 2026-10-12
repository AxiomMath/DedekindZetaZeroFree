module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.TraceCharacterLines

@[expose] public section

noncomputable section
open scoped Classical Topology NNReal
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts
open KPCplxActualImage KPCplxWhittakerUnique
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype

def coreSeminorm (n : ℕ) : Seminorm ℂ complexCore :=
  (chartSeminorm negativeParameter n).comp complexCore.subtype

theorem core_withSeminorms : WithSeminorms coreSeminorm :=
  complexCore.subtype.withSeminorms_induced
    (show WithSeminorms (chartSeminorm negativeParameter) from ⟨rfl⟩)

def smoothInclusion : complexCore →L[ℂ] PrincipalSeries negativeParameter :=
  ⟨complexCore.subtype, continuous_subtype_val⟩

theorem exists_harmonic_sequence (v : PrincipalSeries negativeParameter) :
    ∃ a : ℕ → complexCore, Tendsto (fun n => smoothInclusion (a n)) atTop (𝓝 v) := by
  obtain ⟨b, hb, ht⟩ := KPCplxInverseTopology.harmonic_finiteSum_approximation
    negativeParameter v
  have hm (N : ℕ) : (∑ ℓ ∈ Finset.range N, b ℓ) ∈ complexCore := by
    apply Submodule.sum_mem
    intro ℓ hℓ
    constructor
    · rw [imageSubmodule_eq_top]
      trivial
    · exact (le_iSup (fun ℓ => KPCplxIntertwinerEigenvalues.harmonicKType
        negativeParameter ℓ) ℓ) (hb ℓ)
  exact ⟨fun N => ⟨∑ ℓ ∈ Finset.range N, b ℓ, hm N⟩, ht⟩

theorem smoothInclusion_denseRange : DenseRange smoothInclusion := by
  intro v
  obtain ⟨a, ha⟩ := exists_harmonic_sequence v
  exact mem_closure_of_tendsto ha (Eventually.of_forall (fun n => ⟨a n, rfl⟩))

local instance : IsUniformAddGroup (PrincipalSeries negativeParameter) :=
  isUniformAddGroup_of_addCommGroup
local instance : IsUniformAddGroup complexCore := complexCore.toAddSubgroup.isUniformAddGroup

theorem smoothInclusion_isUniformInducing : IsUniformInducing smoothInclusion := by
  apply AddMonoidHom.isUniformInducing_of_isInducing
    (f := smoothInclusion.toLinearMap.toAddMonoidHom)
  exact ⟨rfl⟩

theorem continuous_of_native_bound (l : complexCore →ₗ[ℂ] ℂ)
    (orders : Finset ℕ) (B : ℝ≥0)
    (hb : ∀ v, ‖l v‖ ≤ B * (orders.sup coreSeminorm) v) : Continuous l := by
  apply core_withSeminorms.continuous_normedSpace_rng ℂ
  exact ⟨orders, B, hb⟩

theorem exists_smooth_extension (l : complexCore →ₗ[ℂ] ℂ) (hl : Continuous l) :
    ∃ L : Theta traceFrequency →L[ℂ] ℂ,
      ∀ v, L (harmonicInclusion v) = l v := by
  let j : complexCore →L[ℂ] ℂ := ⟨l, hl⟩
  let inc : Theta traceFrequency →L[ℂ] PrincipalSeries negativeParameter :=
    ⟨(imageSubmodule traceFrequency).subtype, continuous_subtype_val⟩
  refine ⟨(j.extend smoothInclusion).comp inc, ?_⟩
  intro v
  exact j.extend_eq smoothInclusion_denseRange smoothInclusion_isUniformInducing v

theorem smooth_extension_unique (l : complexCore →ₗ[ℂ] ℂ)
    (L M : Theta traceFrequency →L[ℂ] ℂ)
    (hL : ∀ v, L (harmonicInclusion v) = l v)
    (hM : ∀ v, M (harmonicInclusion v) = l v) : L = M := by
  apply restriction_injective
  ext v
  exact (hL v).trans (hM v).symm

theorem extension_whittaker_of_limits (l : complexCore →ₗ[ℂ] ℂ)
    (L : Theta traceFrequency →L[ℂ] ℂ)
    (he : ∀ v, L (harmonicInclusion v) = l v)
    (hroot : ∀ (t : ℂ) (v : Theta traceFrequency),
      ∃ a b : ℕ → complexCore,
        Tendsto (fun n => harmonicInclusion (a n)) atTop (𝓝 v) ∧
        Tendsto (fun n => harmonicInclusion (b n)) atTop
          (𝓝 (imageAction traceFrequency
            (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.upperUnipotent t)) v)) ∧
        Tendsto (fun n => l (b n) - (traceCharacter t : ℂ) * l (a n)) atTop (𝓝 0)) :
    L ∈ whittakerSpace traceFrequency traceCharacter := by
  intro t v
  obtain ⟨a, b, ha, hb, hr⟩ := hroot t v
  have hA := (L.continuous.tendsto v).comp ha
  have hB := (L.continuous.tendsto _).comp hb
  change Tendsto (fun n => L (harmonicInclusion (a n))) atTop (𝓝 (L v)) at hA
  change Tendsto (fun n => L (harmonicInclusion (b n))) atTop (𝓝 (L _)) at hB
  simp only [he] at hA hB
  have hlim := hB.sub (hA.const_mul (traceCharacter t : ℂ))
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim hr)

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
