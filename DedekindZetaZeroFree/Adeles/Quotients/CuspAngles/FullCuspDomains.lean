module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Cusps.AngularShellLaw
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.HighHoroballOverlap

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsActualAngularDomainSource
open KPMsActualAngularSource KPMsActualCuspSource
open KPMsResidualTailRestoration.SharpConstantTerm
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (S : SourceRecipe F ζ hζ R P H) (U : KPMsActualAngularSource.Level F ζ hζ)

theorem continuous_archBasepoint :
    Continuous (KPMsFixedHaarDisintegration.archBasepoint F) := by
  apply continuous_pi
  intro i
  have he : (fun a : KPSmoothActualFlowData.GInfinity F =>
      KPMsFixedHaarDisintegration.archBasepoint F a i) =
      (fun a => (a (KPCusp.complexPlace F i)) • ((0,0) : KPArch.H3)) := by
    funext a
    unfold KPMsFixedHaarDisintegration.archBasepoint
    generalize a (KPCusp.complexPlace F i) = g
    obtain ⟨b,rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    exact KPMsActualCuspSource.projective_action_mk b (0,0)
  rw [he]
  exact (continuous_apply _).smul continuous_const

theorem product_splitting :
    ∃ e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ*
      KPMsActualAngularSource.G F ζ hζ,
      ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
  obtain ⟨e,he,hi,hs,hker,hrest⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  have hf : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ =
      KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
    ext g
    constructor
    · intro hg
      have h : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g = 1 :=
        MonoidHom.mem_ker.mp (hker.symm ▸ hg)
      change KPCuspGenuineMonodromy.archProjection F ζ hζ g = 1
      funext w
      have hw := congrFun h w
      rw [KPMsActualCuspSource.projection_compare] at hw
      let eqv := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)
      have hh := congrArg (Matrix.ProjGenLinGroup.map eqv.symm.toRingHom) hw
      dsimp only [eqv] at hh
      simpa only [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp,
        RingEquiv.symm_toRingHom_comp_toRingHom, Matrix.ProjGenLinGroup.map_id,
        MonoidHom.id_apply, map_one, Pi.one_apply] using hh
    · intro hg
      rw [← hker]
      apply MonoidHom.mem_ker.mpr
      funext v
      rw [KPMsActualCuspSource.projection_compare]
      have h : KPCuspGenuineMonodromy.archProjection F ζ hζ g = 1 := hg
      rw [h]
      exact map_one _
  change ∃ e : (PGLComplex.AdelicSlicesRaw.ArchGroup F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* _, _
  rw [← hf]
  exact ⟨e,he⟩

end DedekindZetaZeroFree.KPMsActualAngularDomainSource

end
