module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactProbabilityMeasure
public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicPGL.CompactIwasawa
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGL.BorelModularCharacter
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CompactOpenFixedExactness

@[expose] public section

section
noncomputable section
set_option maxHeartbeats 1200000
open scoped Topology NNReal
namespace DedekindZetaZeroFree.KPLocalInducedCompactPairing

def bidualMap {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : SmoothRepresentation ρ) :
    V →ₗ[ℂ] smoothSubmodule (smoothPart ρ.dual).dual := by
  let j : V →ₗ[ℂ] Module.Dual ℂ (smoothSubmodule ρ.dual) :=
    { toFun := fun v =>
        { toFun := fun ℓ => ℓ.val v
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  refine j.codRestrict _ ?_
  intro v
  rw [mem_smoothSubmodule]
  obtain ⟨U, hU⟩ := hρ v
  refine ⟨U, ?_⟩
  intro g hg
  ext ℓ
  change ℓ.val (ρ (g⁻¹)⁻¹ v) = ℓ.val v
  rw [inv_inv, hU g hg]

end DedekindZetaZeroFree.KPLocalInducedCompactPairing

end

end

section

noncomputable section

set_option linter.style.haveILetI false

namespace DedekindZetaZeroFree.KPLocalInducedSmoothDual

section Dual

variable {G V : Type*} [Group G] [TopologicalSpace G]
  [AddCommGroup V] [Module ℂ V]

abbrev SmoothDual (ρ : Representation ℂ G V) := smoothSubmodule ρ.dual

abbrev smoothDualRepresentation [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) : Representation ℂ G (SmoothDual ρ) :=
  smoothPart ρ.dual

end Dual

end DedekindZetaZeroFree.KPLocalInducedSmoothDual

end

end

section

noncomputable section
set_option maxHeartbeats 1200000
open scoped Topology NNReal
namespace DedekindZetaZeroFree.KPLocalInducedCompactPairing

open scoped NumberField NNReal
open NumberField IsDedekindDomain KPLocalSmoothRepresentation
section AlgebraicAveraging

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]

theorem smooth_orbit_locallyConstant (ρ : Representation ℂ G V) (v : V)
    (hv : SmoothVector ρ v) : IsLocallyConstant (fun g => ρ g v) := by
  obtain ⟨J, hJ⟩ := hv
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun y => g⁻¹ * y) ⁻¹' (J : Set G),
    J.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using J.one_mem
  · intro y hy
    have heq : y = g * (g⁻¹ * y) := by simp
    rw [heq, map_mul, Module.End.mul_apply, hJ _ hy]

end AlgebraicAveraging

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)

end DedekindZetaZeroFree.KPLocalInducedCompactPairing

end
end
