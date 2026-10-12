module

public import DedekindZetaZeroFree.Metaplectic.Weil.SquareClassOpennessAndPhaseContinuity

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

theorem weil_finite_squareclass_approximation
    (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (aLocal : (v : {v : HeightOneSpectrum (𝓞 F) // v ∈ T}) →
      (v.val.adicCompletion F)ˣ) :
    ∃ a : Fˣ, ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∈ T},
      IsSquare
        (Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a /
          aLocal v) := by
  obtain ⟨a, ha⟩ :=
    IdeleGroup.exists_principal_quotient_mem_openLocalSubgroups_finset T
      (IdeleGroup.ideleOfFiniteLocalFamily T aLocal)
      (fun v => finiteSquareSubgroup v.val)
      (fun v => finiteSquareSubgroup_isOpen v.val)
  refine ⟨a, fun v => ?_⟩
  have hv := ha v
  rw [IdeleGroup.ideleOfFiniteLocalFamily_finiteComponent] at hv
  have he : ((IdeleGroup.principalIdele F a).2 v.val) =
      Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a := by
    apply Units.ext
    exact IdeleGroup.finiteComponent_principalIdele a v.val
  rw [he] at hv
  obtain ⟨r, hr⟩ := hv
  have hs : IsSquare (aLocal v *
      (Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a)⁻¹) :=
    (isSquare_iff_exists_sq _).mpr ⟨r, hr.symm⟩
  simpa [div_eq_mul_inv, mul_comm] using hs.inv

theorem weil_dyadic_squareclass_approximation
    (F : Type) [Field F] [NumberField F]
    (v₀ : HeightOneSpectrum (𝓞 F)) (hv₀ : (2 : 𝓞 F) ∈ v₀.asIdeal)
    (a₀ : (v₀.adicCompletion F)ˣ) :
    ∃ a : Fˣ,
      IsSquare
        (Units.map (algebraMap F (v₀.adicCompletion F)).toMonoidHom a / a₀) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)), (2 : 𝓞 F) ∈ v.asIdeal → v ≠ v₀ →
        IsSquare (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := by
  classical
  have hfinite : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite :=
    (Ring.HasFiniteQuotients.finite_setOfPred_mem (2 : 𝓞 F) (by norm_num)).preimage
      (fun _ _ _ _ h => HeightOneSpectrum.ext h)
  let T := hfinite.toFinset
  have hT (v : HeightOneSpectrum (𝓞 F)) : v ∈ T ↔ (2 : 𝓞 F) ∈ v.asIdeal :=
    hfinite.mem_toFinset
  let aLocal : (v : {v : HeightOneSpectrum (𝓞 F) // v ∈ T}) →
      (v.val.adicCompletion F)ˣ :=
    fun v => if h : v.val = v₀ then h.symm ▸ a₀ else 1
  obtain ⟨a, ha⟩ := weil_finite_squareclass_approximation F T aLocal
  refine ⟨a, ?_, ?_⟩
  · have h := ha ⟨v₀, (hT v₀).mpr hv₀⟩
    simpa [aLocal] using h
  · intro v hv hne
    have h := ha ⟨v, (hT v).mpr hv⟩
    simpa [aLocal, hne] using h

end DedekindZetaZeroFree
