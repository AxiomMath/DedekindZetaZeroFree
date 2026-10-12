module

public import DedekindZetaZeroFree.Adeles.Quotients.PrincipalTorusCoordinateInjectivity

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.FrozenChoices
open KPGlobalProductPolarizationCharacter
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
open _root_.DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter renaming fromRawLocal → fromRawLocal

theorem exists_initial :
    ∃ P : CompatibleLocalData F A.zeta12 A.primitive_zeta12,
      ∀ q ∉ A.Sf, IsUnramified F A.zeta12 A.primitive_zeta12 q
        (P.localData (Sum.inr q)) := by
  let complexData (w : InfinitePlace F) :=
    (ProductPolarization.complex_local_polarization
      F A.zeta12 A.primitive_zeta12 w).choose
  let finiteData (q : HeightOneSpectrum (𝓞 F)) :
      LocalPolarization F A.zeta12 A.primitive_zeta12 (Sum.inr q) :=
    if h : q ∈ A.Sf then
      fromRawLocal F A.zeta12 A.primitive_zeta12 _
        (ProductPolarization.finite_local_polarization
          F A.zeta12 A.primitive_zeta12 q).some
    else fromRawLocal F A.zeta12 A.primitive_zeta12 _
      (ProductPolarization.good_local_extension
        F A.zeta12 A.primitive_zeta12 q (FrozenTorus.outside_good A q h)).choose
  have hf (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ A.Sf) :
      IsUnramified F A.zeta12 A.primitive_zeta12 q (finiteData q) := by
    unfold finiteData
    rw [dif_neg hq]
    exact (ProductPolarization.good_local_extension F A.zeta12 A.primitive_zeta12
      q (FrozenTorus.outside_good A q hq)).choose_spec
  refine ⟨{
    localData := fun v => match v with
      | Sum.inl w => fromRawLocal F A.zeta12 A.primitive_zeta12 _ (complexData w)
      | Sum.inr q => finiteData q
    complex_full := ?_
    unramified_almost_everywhere := ?_ }, hf⟩
  · intro w
    exact (ProductPolarization.complex_local_polarization
      F A.zeta12 A.primitive_zeta12 w).choose_spec
  · filter_upwards [A.Sf.finite_toSet.compl_mem_cofinite] with q hq
    exact hf q hq

end DedekindZetaZeroFree.EisensteinReferenceSections.FrozenChoices

end
