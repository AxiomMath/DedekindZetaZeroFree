module

public import DedekindZetaZeroFree.Metaplectic.Unipotent.RationalFrameConjugation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField NNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
open KPMsClearedTruncationL2
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
theorem fullCusp_finiteSubgroup_eq :
    PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ = KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  obtain ⟨e,he,hi,hs,hker,hrest⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  rw [← hker]
  ext g
  constructor
  · intro hg
    exact complex_kernel_mem F ζ hζ hg
  · intro hg
    rw [MonoidHom.mem_ker]
    funext w
    rw [archProjection_compare]
    have h : KPCuspGenuineMonodromy.archProjection F ζ hζ g = 1 := hg
    rw [h]
    exact map_one _

theorem fullCusp_product_splitting :
    ∃ e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* G F ζ hζ,
      ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
  obtain ⟨e,he,hrest⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  have hf := fullCusp_finiteSubgroup_eq F ζ hζ
  change ∃ e : (PGLComplex.AdelicSlicesRaw.ArchGroup F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* _, _
  rw [← hf]
  exact ⟨e,he⟩
variable {F ζ hζ}
variable {C : ModelData F ζ hζ} {D : Iwasawa F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ C D R P H}
variable {U : Level F ζ hζ}

end DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent

end
