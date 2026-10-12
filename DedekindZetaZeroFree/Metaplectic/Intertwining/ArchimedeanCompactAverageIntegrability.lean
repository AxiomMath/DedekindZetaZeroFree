module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.GaussChartBumps
public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationSubgroupCharacters
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactConjugationInvariance

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel
open MeasureTheory Set Topology
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

theorem pgl_t2 : T2Space PGLComplex.Group := by
  have hc : IsClosed (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ) :
      Set (Matrix.GeneralLinearGroup (Fin 2) ℂ)) := by
    have he : (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ) :
        Set (Matrix.GeneralLinearGroup (Fin 2) ℂ)) =
        ⋂ g : Matrix.GeneralLinearGroup (Fin 2) ℂ, {x | x * g = g * x} := by
      ext x
      simp [Subgroup.mem_center_iff]
      exact ⟨fun h g => (h g).symm, fun h g => (h g).symm⟩
    rw [he]
    exact isClosed_iInter fun g => isClosed_eq (continuous_mul_const g) (continuous_const_mul g)
  letI : IsClosed (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ) :
      Set (Matrix.GeneralLinearGroup (Fin 2) ℂ)) := hc
  change T2Space (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸ Subgroup.center _)
  infer_instance

theorem pgl_locallyCompact : LocallyCompactSpace PGLComplex.Group := by
  letI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
    change LocallyCompactSpace (Fin 2 → Fin 2 → ℂ)
    infer_instance
  change LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸ Subgroup.center _)
  infer_instance

theorem pgl_secondCountable : SecondCountableTopology PGLComplex.Group := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI : SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  change SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸ Subgroup.center _)
  infer_instance

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

end
