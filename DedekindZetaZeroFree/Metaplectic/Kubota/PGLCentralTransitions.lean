module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalPGLCoverModules

@[expose] public section

namespace DedekindZetaZeroFree.KPWildCompactProjectorKirillov.ClopenGluing

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

theorem ordinaryPGLMap_injective
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    Function.Injective (KPLocalSmoothRepresentation.ordinaryPGLMap F v) := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr v)
  letI : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr v)) :=
    @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr v))
      (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr v))
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  induction g using QuotientGroup.induction_on with
  | _ a =>
    apply (QuotientGroup.eq_one_iff _).mpr
    have ha : a ∈ Subgroup.center (KPLocalCover.LocalGL2 F (Sum.inr v)) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at ha
    exact ha

end
end DedekindZetaZeroFree.KPWildCompactProjectorKirillov.ClopenGluing
