module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel

@[expose] public section

noncomputable section
open scoped Classical Valued
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeLocalFixedFinite
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {G H DD : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup DD] [Finite DD]
variable {T : LocalHeisenbergData H DD}

theorem principal_series_fixed_finite
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign) (s : ℂ) (J : CompactOpenLevel G)
    (hJ : (J.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup) :
    letI : AddCommGroup (sectionSpace A P ε s) := inferInstance
    Module.Finite ℂ (fixedSubmodule (principalSeries A P ε s) J.toOpenSubgroup.toSubgroup) := by
  letI : AddCommGroup (sectionSpace A P ε s) := inferInstance
  letI : AddCommGroup (compactPicture A P I ε) := inferInstance
  let L := compactLevel A P I ε J
  letI : AddCommGroup L := inferInstance
  letI : Module.Finite ℂ L := compact_level_finite A P I ε J hJ
  let e := compactTrivialization A P I ε s
  let f : (fixedSubmodule (principalSeries A P ε s) J.toOpenSubgroup.toSubgroup) →ₗ[ℂ] L :=
    { toFun := fun x => ⟨e.symm x.val, by
        apply (compact_level_identification A P I ε J hJ s (e.symm x.val)).mpr
        change e (e.symm x.val) ∈ _
        rw [LinearEquiv.apply_symm_apply]
        exact x.property⟩
      map_add' := by intros; apply Subtype.ext; exact map_add e.symm _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul e.symm _ _ }
  apply Module.Finite.of_injective f
  intro x y h
  apply Subtype.ext
  apply e.symm.injective
  exact congrArg Subtype.val h

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeLocalFixedFinite

end
