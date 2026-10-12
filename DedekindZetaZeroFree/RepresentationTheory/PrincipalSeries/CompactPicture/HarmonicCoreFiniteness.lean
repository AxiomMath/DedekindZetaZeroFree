module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarCompactPicturesAndLocalQuotientTensors

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPLiteralScalarArchHarmonicCore
open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

private theorem pi_add (s : ℝ) (k : compactSubgroup) (f g : PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.pi s k (f + g) = KPCplxPrincipalSeriesCharts.pi s k f + KPCplxPrincipalSeriesCharts.pi s k g := by
  induction k.val using Quotient.inductionOn with
  | h a => rfl

theorem finite_invariant_subspace (s : ℝ) (f : PrincipalSeries s)
    (hf : f ∈ ⨆ ℓ : ℕ, harmonicKType s ℓ) :
    ∃ U : Submodule ℂ (PrincipalSeries s),
      Module.Finite ℂ U ∧ f ∈ U ∧ IsKInvariant s U ∧
        U ≤ ⨆ ℓ : ℕ, harmonicKType s ℓ := by
  refine Submodule.iSup_induction (fun ℓ : ℕ => harmonicKType s ℓ)
    (motive := fun f => ∃ U : Submodule ℂ (PrincipalSeries s),
      Module.Finite ℂ U ∧ f ∈ U ∧ IsKInvariant s U ∧
        U ≤ ⨆ ℓ : ℕ, harmonicKType s ℓ) hf ?_ ?_ ?_
  · intro ℓ f hf
    exact ⟨harmonicKType s ℓ,
      KPCplxHarmonicIntertwinerSpectrum.harmonicKType_finite s ℓ, hf,
      (harmonicKType_multiplicity_one s ℓ).1, le_iSup _ ℓ⟩
  · refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_, bot_le⟩
    intro k f hf
    have hf' : f = 0 := by simpa using hf
    subst f
    change KPCplxPrincipalSeriesCharts.pi s k 0 = 0
    induction k.val using Quotient.inductionOn with
    | h a => rfl
  · intro f g hf hg
    obtain ⟨U, hU, hfU, hinvU, hleU⟩ := hf
    obtain ⟨V, hV, hgV, hinvV, hleV⟩ := hg
    let : Module.Finite ℂ U := hU
    let : Module.Finite ℂ V := hV
    refine ⟨U ⊔ V, inferInstance,
      Submodule.add_mem _ (Submodule.mem_sup_left hfU) (Submodule.mem_sup_right hgV),
      ?_, sup_le hleU hleV⟩
    intro k x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    rw [pi_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hinvU k u hu))
      (Submodule.mem_sup_right (hinvV k v hv))

end DedekindZetaZeroFree.KPLiteralScalarArchHarmonicCore

end
