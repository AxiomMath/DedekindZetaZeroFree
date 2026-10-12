module

public import DedekindZetaZeroFree.Adeles.Quotients.Additive.CompactOpenBasis
public import DedekindZetaZeroFree.Adeles.Quotients.CompactOpenLevelTori

@[expose] public section

namespace DedekindZetaZeroFree.AdelicSeparation

open scoped NumberField
open NumberField IsDedekindDomain

theorem nonzero_survives_finiteLevel
    (F : Type) [Field F] [NumberField F]
    (q : AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) (hq : q ≠ 0) :
    ∃ K : AddSubgroup (FiniteAdeleRing (𝓞 F) F),
      IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      (QuotientAddGroup.mk' (finiteLevelImage K)) q ≠ 0 := by
  haveI := (additiveAdeleQuotient_compactHausdorff F).2
  let f := (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)).comp
    (finiteLevelFiniteInclusion F)
  have hf : Continuous f := by
    exact (QuotientAddGroup.continuous_mk (N := AdeleRing.principalSubgroup (𝓞 F) F)).comp
      (by
        show Continuous (fun x : FiniteAdeleRing (𝓞 F) F => ((0, x) : AdeleRing (𝓞 F) F))
        fun_prop)
  let U := f ⁻¹' ({q}ᶜ)
  have hU : U ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F) := by
    apply (isClosed_singleton.isOpen_compl.preimage hf).mem_nhds
    change f 0 ≠ q
    simpa using hq.symm
  obtain ⟨K, hKc, hKo, hKU⟩ := finiteAdeles_compactOpen_basis_zero F U hU
  refine ⟨K, hKc, hKo, ?_⟩
  intro hzero
  have hmem : q ∈ finiteLevelImage K := (QuotientAddGroup.eq_zero_iff q).mp hzero
  obtain ⟨a, ha, heq⟩ := hmem
  have hne := hKU ha
  change f a ≠ q at hne
  exact hne heq

end DedekindZetaZeroFree.AdelicSeparation
