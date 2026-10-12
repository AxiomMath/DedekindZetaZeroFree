module

public import Mathlib
public import DedekindZetaZeroFree.Adeles.Approximation.FiniteDenominatorClearing
public import DedekindZetaZeroFree.Adeles.Approximation.IntegralProductCRTDensity

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open NumberField IsDedekindDomain

set_option backward.isDefEq.respectTransparency false in

theorem finiteAdele_dense (F : Type*) [Field F] [NumberField F] :
    DenseRange (algebraMap F (FiniteAdeleRing (𝓞 F) F)) := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨z, hz⟩ := hUne
  obtain ⟨d, hd, t, ht⟩ := finiteAdele_exists_integral_denominator_mem_range F z
  let A := FiniteAdeleRing (𝓞 F) F
  let s : ((v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F) → A :=
    RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite
  let c : A := algebraMap F A (algebraMap (𝓞 F) F d)⁻¹
  have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd
  have hc : c * algebraMap (𝓞 F) A d = 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F A]
    dsimp [c]
    rw [← map_mul, inv_mul_cancel₀ hdF, map_one]
  have hs : Continuous s :=
    (RestrictedProduct.isOpenEmbedding_structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring
        (v.adicCompletion F))).continuous
  have hg : Continuous (fun x => c * s x) := continuous_const.mul hs
  have htz : c * s t = z := by
    have ht' : s t = algebraMap (𝓞 F) A d * z := ht
    rw [ht', ← mul_assoc, hc, one_mul]
  obtain ⟨a, ha⟩ := (denseRange_ringOfIntegers_integralDiagonal F).exists_mem_open
    (hU.preimage hg) ⟨t, by simpa only [Set.mem_preimage, htz] using hz⟩
  have hdiag : s (ringOfIntegers_integralDiagonal F a) = algebraMap (𝓞 F) A a := by
    apply FiniteAdeleRing.ext
    intro v
    rfl
  refine ⟨algebraMap F A (a / algebraMap (𝓞 F) F d), ?_,
    ⟨a / algebraMap (𝓞 F) F d, rfl⟩⟩
  change c * s (ringOfIntegers_integralDiagonal F a) ∈ U at ha
  rw [hdiag, IsScalarTower.algebraMap_apply (𝓞 F) F A] at ha
  simpa [c, div_eq_mul_inv, map_mul, mul_comm] using ha

theorem finiteAdele_strongApprox (F : Type*) [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hKopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hKcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (z : FiniteAdeleRing (𝓞 F) F) :
    ∃ lam : F, ∃ k : K, z = algebraMap F (FiniteAdeleRing (𝓞 F) F) lam + k := by
  let U := (Homeomorph.addLeft z) '' (K : Set (FiniteAdeleRing (𝓞 F) F))
  have hU : IsOpen U := (Homeomorph.addLeft z).isOpenMap _ hKopen
  have hz : z ∈ U := ⟨0, K.zero_mem, by simp⟩
  obtain ⟨lam, k', hk', heq⟩ := (finiteAdele_dense F).exists_mem_open hU ⟨z, hz⟩
  refine ⟨lam, ⟨-k', K.neg_mem hk'⟩, ?_⟩
  change z = algebraMap F (FiniteAdeleRing (𝓞 F) F) lam + -k'
  change z + k' = algebraMap F (FiniteAdeleRing (𝓞 F) F) lam at heq
  rw [← heq, add_neg_cancel_right]

end
end DedekindZetaZeroFree
