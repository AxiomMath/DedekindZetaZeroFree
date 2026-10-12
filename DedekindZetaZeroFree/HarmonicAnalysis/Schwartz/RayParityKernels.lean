module

public import DedekindZetaZeroFree.Theta.Profiles.RayParityKernels

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity

variable (K : Type) [Field K] [NumberField K]

theorem exists_rayParitySchwartz (δ : Finset (RayCoset.RealPlaces K)) :
    ∃ f : SchwartzMap (euclidean.mixedSpace K) ℂ,
      ∀ x, f x = gδ K δ x := by

  let g : euclidean.mixedSpace K → ℂ :=
    fun x ↦ ∏ v ∈ δ, (Theta.traceRealCoordinateCLM K v x : ℂ)
  have hP : Function.HasTemperateGrowth g := by
    change Function.HasTemperateGrowth
      (fun x : euclidean.mixedSpace K ↦
        ∏ v ∈ δ, (Theta.traceRealCoordinateCLM K v x : ℂ))
    classical
    induction δ using Finset.induction_on with
    | empty => simpa using Function.HasTemperateGrowth.const (1 : ℂ)
    | insert a s ha ih =>
      have ha' : Function.HasTemperateGrowth
          (fun x : euclidean.mixedSpace K ↦
            (Theta.traceRealCoordinateCLM K a x : ℂ)) := by fun_prop
      have h : (fun x : euclidean.mixedSpace K ↦
            ∏ v ∈ insert a s, (Theta.traceRealCoordinateCLM K v x : ℂ))
          = (fun x : euclidean.mixedSpace K ↦
            (Theta.traceRealCoordinateCLM K a x : ℂ) *
              ∏ v ∈ s, (Theta.traceRealCoordinateCLM K v x : ℂ)) := by
        funext x
        rw [Finset.prod_insert ha]
      rw [h]
      exact ha'.mul ih
  refine ⟨SchwartzMap.smulLeftCLM ℂ g (Theta.traceGaussianSchwartz K), fun x ↦ ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply hP, Theta.traceGaussianSchwartz_apply]
  change g x * Theta.latticeGaussian Real.pi x = gδ K δ x
  rw [gδ]

def rayParitySchwartz (δ : Finset (RayCoset.RealPlaces K)) :
    SchwartzMap (euclidean.mixedSpace K) ℂ :=
  Classical.choose (exists_rayParitySchwartz K δ)

@[simp] theorem rayParitySchwartz_apply (δ : Finset (RayCoset.RealPlaces K))
    (x : euclidean.mixedSpace K) :
    rayParitySchwartz K δ x = gδ K δ x :=
  Classical.choose_spec (exists_rayParitySchwartz K δ) x

end DedekindZetaZeroFree.AbelianQuotient.RayParity

end
