module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.FiniteTensorSectionsAndTopology

@[expose] public section

section

noncomputable section

set_option maxHeartbeats 200000

set_option maxRecDepth 4096

namespace DedekindZetaZeroFree.KPWildCompactProjectorKirillov.GlobalEvaluation

open scoped NumberField Topology Classical

open NumberField IsDedekindDomain KPKirillovGenuineSectionCharts

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
  (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F v m)
  (ψ : Multiplicative (K F v) →* ℂˣ) (hψ : IsLocallyConstant ψ)

local notation "topology" => KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ v m

def evaluationMap :
    letI := topology
    ∀ (lift : (K F v)ˣ → P F ζ hζ v), Continuous lift →
      (∀ t, slope F ζ hζ v (lift t) = t) →
      Sections F ζ hζ v m ψ ℂ →ₗ[ℂ] CompactFunctions (K F v)ˣ ℂ := by
  letI := topology
  intro lift hlift hslope
  let T := compactLCEquiv F ζ hζ v m hm ψ hψ ℂ
  let q := quotientHomeomorph F ζ hζ v m hm
  refine { toFun := fun f => ⟨fun t => sectionValue F ζ hζ v m ψ f (lift t), ?_⟩
           map_add' := ?_
           map_smul' := ?_ }
  · constructor
    · have h := (T f).property.1.comp_continuous hlift
      have he : (fun t => (T f).val (lift t)) =
          (fun t => sectionValue F ζ hζ v m ψ f (lift t)) := by
        funext t
        exact compactLCEquiv_value F ζ hζ v m hm ψ hψ f (lift t)
      change IsLocallyConstant (fun t => (T f).val (lift t)) at h
      rwa [he] at h
    · let S := closure ((Quotient.mk (QuotientGroup.rightRel (H F ζ hζ v))) ''
          Function.support (T f).val)
      have hc : IsCompact S := (T f).property.2.1
      have hcq : IsCompact (q '' S) := hc.image q.continuous
      have hsub : Function.support (fun t => sectionValue F ζ hζ v m ψ f (lift t)) ⊆
          q '' S := by
        intro t ht
        refine ⟨Quotient.mk (QuotientGroup.rightRel (H F ζ hζ v)) (lift t), ?_, ?_⟩
        · apply subset_closure
          refine ⟨lift t, ?_, rfl⟩
          rw [Function.mem_support, compactLCEquiv_value]
          exact ht
        · exact (quotientHomeomorph_mk F ζ hζ v m hm (lift t)).trans (hslope t)
      exact hcq.of_isClosed_subset isClosed_closure (closure_minimal hsub hcq.isClosed)
  · intro f g
    apply Subtype.ext
    rfl
  · intro c f
    apply Subtype.ext
    rfl

@[simp] theorem evaluationMap_value :
    letI := topology
    ∀ (lift : (K F v)ˣ → P F ζ hζ v) (hlift : Continuous lift)
      (hslope : ∀ t, slope F ζ hζ v (lift t) = t)
      (f : Sections F ζ hζ v m ψ ℂ) (t : (K F v)ˣ),
      (evaluationMap F ζ hζ v m hm ψ hψ lift hlift hslope f).val t =
        sectionValue F ζ hζ v m ψ f (lift t) := by
  intros
  rfl

end DedekindZetaZeroFree.KPWildCompactProjectorKirillov.GlobalEvaluation

end

end

section

noncomputable section

set_option maxHeartbeats 1000000

set_option maxRecDepth 4096

namespace DedekindZetaZeroFree.KPWildCompactProjectorKirillov.GlobalEvaluation

open scoped NumberField Topology Classical

open NumberField IsDedekindDomain KPKirillovGenuineSectionCharts

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
  (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F v m)
  (ψ : Multiplicative (K F v) →* ℂˣ) (hψ : IsLocallyConstant ψ)

noncomputable instance scalarSectionsAddCommGroup :
    AddCommGroup (Sections F ζ hζ v m ψ ℂ) :=
  Module.addCommMonoidToAddCommGroup ℂ

end DedekindZetaZeroFree.KPWildCompactProjectorKirillov.GlobalEvaluation

end

end

section

noncomputable section

set_option maxHeartbeats 200000

set_option maxRecDepth 4096

namespace DedekindZetaZeroFree.KPWildCompactProjectorKirillov

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable (v : HeightOneSpectrum (RingOfIntegers F))

abbrev standardCharacter := KPKirillovOrbitMapFaithful.ψ F v

end DedekindZetaZeroFree.KPWildCompactProjectorKirillov

end

end
