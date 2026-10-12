module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactWordNumerator

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NativeProjectedNumerator
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming finite_literal_compact_numerator → finite_literal_compact_numerator

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false

section Integration
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace X] [BorelSpace X]

 def weightedOrbitFunctional (q : C(X, Y))
    (μ : Measure X) [IsFiniteMeasure μ] (h : C(X, ℂ)) :
    C(Y, ℂ) →L[ℂ] ℂ := by
  let l : C(Y, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ x, h x * v (q x) ∂μ
      map_add' := by
        intro v w
        simp only [ContinuousMap.add_apply, mul_add]
        exact integral_add
          ((h * v.comp q).continuous.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
          ((h * w.comp q).continuous.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
      map_smul' := by
        intro z v
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm (h _) z]
        exact integral_const_mul z _ }
  refine l.mkContinuous (μ.real Set.univ * ‖h‖) ?_
  intro v
  change ‖∫ x, h x * v (q x) ∂μ‖ ≤ (μ.real Set.univ * ‖h‖) * ‖v‖
  calc
    _ ≤ (‖h‖ * ‖v‖) * μ.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      exact Filter.Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul (h.norm_coe_le_norm x) (v.norm_coe_le_norm (q x))
          (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

 theorem weightedOrbitFunctional_apply (q : C(X, Y))
    (μ : Measure X) [IsFiniteMeasure μ] (h : C(X, ℂ)) (v : C(Y, ℂ)) :
    weightedOrbitFunctional q μ h v = ∫ x, h x * v (q x) ∂μ := rfl

 theorem meromorphic_comp_functional (L : C(Y, ℂ) →L[ℂ] ℂ)
    {S : ℂ → C(Y, ℂ)} {O : Set ℂ} (hS : MeromorphicOn S O) :
    MeromorphicOn (fun s => L (S s)) O := by
  intro s hs
  obtain ⟨n, hn⟩ := hS s hs
  refine ⟨n, ?_⟩
  simpa only [Function.comp_def, map_smul] using (L.analyticAt _).comp hn
end Integration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

end DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NativeProjectedNumerator

end
