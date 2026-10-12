module

public import ClassFieldTheory.All

@[expose] public section

set_option maxRecDepth 2048

namespace DedekindZetaZeroFree.RMKummerLocalNormArtin
noncomputable section
open scoped NumberField TensorProduct Classical
open IsDedekindDomain

theorem continuous_of_open_kernel {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [ContinuousMul H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : Continuous f := by
  apply continuous_of_continuousAt_one f
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [h.mem_nhds (by simp)] with x hx
  change f x = 1 at hx
  simpa only [map_one] using hx

theorem arithmeticLocalArtin_ker (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsAbelianGalois F E]
    (v : HeightOneSpectrum (𝓞 F)) :
    (GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom F E v).ker =
      ClassFieldTheory.finitePlaceTensorNormSubgroup F E v := by
  ext t
  simp only [MonoidHom.mem_ker,
    GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply,
    inv_eq_one]
  rw [GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm,
    ← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup (K := F) (L := E) v]
  rfl

theorem arithmeticLocalArtin_continuous (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsAbelianGalois F E]
    (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom F E v) := by
  apply continuous_of_open_kernel
  rw [arithmeticLocalArtin_ker]
  change IsOpen ((_root_.localTensorNorm (K := F) (L := E) v).range : Set (v.adicCompletion F)ˣ)
  rw [finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup (K := F) (L := E) v]
  exact chosenFinitePlaceLocalNormSubgroup_isOpen (K := F) (L := E) v

theorem normConductorArtin_local (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsAbelianGalois F E]
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin F E
      ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele F
        (ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus F E)).symm
        (QuotientGroup.mk'
          (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F
            (ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus F E)).congruenceSubgroup
          (IdeleGroup.finitePlaceIdeleClass v t))) =
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom F E v t := by
  unfold ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin
    ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
    GlobalClassFieldTheory.IdealClassFieldTheory.idealRayClassArtinMap
  simp only [MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply,
    GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk]
  exact DFunLike.congr_fun
    (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
      (K := F) (L := E) v) t

theorem transported_normConductorArtin_local (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsAbelianGalois F E]
    (m : ClassFieldTheory.RayClassModulus F)
    (hm : m = ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus F E)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    (hm.symm ▸ ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin F E :
      ClassFieldTheory.RayClassGroup m →* (E ≃ₐ[F] E))
      ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele F m).symm
        (QuotientGroup.mk'
          (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F m).congruenceSubgroup
          (IdeleGroup.finitePlaceIdeleClass v t))) =
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom F E v t := by
  subst m
  exact normConductorArtin_local F E v t

end
end DedekindZetaZeroFree.RMKummerLocalNormArtin
