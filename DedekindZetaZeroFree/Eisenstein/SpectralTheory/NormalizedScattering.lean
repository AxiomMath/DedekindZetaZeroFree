module

public import DedekindZetaZeroFree.Theta.Whittaker.EulerFactors.ExteriorNormalization
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ScatteringIntegralExhaustion
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.GlobalExistence

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators Topology TensorProduct
open NumberField MeasureTheory Filter
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber renaming exterior_enlargement_tendsto → exterior_enlargement_tendsto
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open LiteralSource.CofactorChamber KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem current_normalized_scattering
    (s : RestrictedTensorSimple.Level (bad R P C))
    (K : Set (Raw R)) (hK : IsCompact K) :
    ∃ E : Finset (KPFinitePlace F), ∃ hsE : s.val.toRight ⊆ E, ∃ hCE : C.exceptional ⊆ E,
      ∀ a ∈ K, ∀ z : ℂ, (1 / 3 : ℝ) < z.re →
      ∀ v : RestrictedTensorSimple.Stage (Plus R N P C) s.val,
        LiteralSource.coreScattering R P C
          (coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s v)) z
          (scalarQuotient F ζ hζ (amalgamation F ζ hζ a)) =
        KPGlobalFiniteSIntertwiner.normalizer F  ζ hζ E z *
          (parameterStage R N P C (fullCompact R P C) (fullLevel R P C E hCE) a z
            (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
              (bad R P C) s (fullLevel R P C E hCE)
              (sourceStage_le_fullLevel R P C s E hCE hsE) v)).val.val 1 := by
  obtain ⟨E₀,hs₀,hC₀,hbox⟩ := current_source_box_integral R N P C s K hK
  obtain ⟨E₁,h01,hC₁,htail⟩ := compact_split_tail R P C K hK E₀
  let E := E₁ ∪ (finite_localDifferentSupport F).toFinset
  have h1E : E₁ ⊆ E := Finset.subset_union_left
  have h0E : E₀ ⊆ E := h01.trans h1E
  have hsE : s.val.toRight ⊆ E := hs₀.trans h0E
  have hCE : C.exceptional ⊆ E := hC₁.trans h1E
  have hD : localDifferentSupport F ⊆ (E : Set _) := by
    intro q hq
    exact Finset.mem_union_right E₁ ((finite_localDifferentSupport F).mem_toFinset.mpr hq)
  refine ⟨E,hsE,hCE,?_⟩
  intro a ha z hz v
  have hzD : z ∈ KPContinuation.spectralDomain := by
    change -(1 : ℝ) / 6 < z.re
    linarith
  let e := fullLevel R P C E hCE
  have hse : s ≤ e := sourceStage_le_fullLevel R P C s E hCE hsE
  let ve := RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
    (bad R P C) s e hse v
  let b := (parameterStage R N P C (fullCompact R P C) e a z ve).val.val 1
  have hb (Q : Finset (KPFinitePlace F)) (hEQ : E ⊆ Q) :
      (∫ y : KPGlobalTorusFunctionData.Adeles F,
        (LiteralSource.coreFlatInsertion R P C
          (coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s v))).val z
          (scalarQuotient F ζ hζ (amalgamation F ζ hζ (chamberRaw F ζ hζ y * a)))
        ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) =
        KPGlobalFiniteSIntertwiner.enlargementFactor F E Q z * b := by
    have h0Q := h0E.trans hEQ
    have hCQ := hCE.trans hEQ
    let q := fullLevel R P C Q hCQ
    have heq : e ≤ q := by
      intro p hp
      cases p with
      | inl w => simp [q,fullLevel,LiteralSource.cofactorSourceLevel]
      | inr r =>
        have hr : r ∈ E := by simpa [e,fullLevel,LiteralSource.cofactorSourceLevel] using hp
        simpa [q,fullLevel,LiteralSource.cofactorSourceLevel] using hEQ hr
    have hat : ∀ r : KPFinitePlace F, Sum.inr r ∈ q.val → Sum.inr r ∉ e.val →
        KPPGLLocalCover.coverQuotient F ζ hζ (.inr r) (a (.inr r)) ∈
          (C.canonical r).iwasawa.compact.toOpenSubgroup := by
      intro r _ hr
      have hrE : r ∉ E := by simpa [e,fullLevel,LiteralSource.cofactorSourceLevel] using hr
      exact htail a ha r (fun h => hrE (h1E h))
    have heuler := parameterStage_compact_euler_enlargement R N P C e q heq a hat z hzD ve
    have ht : RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
        (bad R P C) e q heq ve =
      RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
        (bad R P C) s q (hse.trans heq) v :=
      DirectedSystem.map_map (f := fun {i j} h =>
        RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
          (bad R P C) i j h) hse heq v
    rw [ht] at heuler
    have hv := congrArg (fun f : KPGlobalResidualConstruction.smoothRationalFiber F ζ hζ =>
      f.val.val 1) heuler
    simp only [Submodule.coe_smul,Pi.smul_apply,smul_eq_mul] at hv
    have hn := full_exterior_product R N P C E Q hCE hCQ hD z
    have hout := (hbox Q h0Q a ha z hzD v).2
    refine hout.trans (hv.trans ?_)
    apply congrArg (fun c : ℂ => c * b)
    calc
      _ = ∏ p ∈ (fullLevel R P C Q hCQ).val \ (fullLevel R P C E hCE).val,
          exteriorFactor R N z p := by
        apply Finset.prod_congr
        · ext p
          simp [q,e]
        · intro p _
          rfl
      _ = _ := hn
  have hl := current_scattering_integral_exhaustion R N P C
    (RestrictedTensorSimple.stageInclusion _ _ _ s v) a z hz
  have hl₁ := hl.comp (tendsto_atTop_mono (fun T : Finset (KPFinitePlace F) =>
    (Finset.subset_union_right : T ⊆ E ∪ T)) tendsto_id)
  have he := (exterior_enlargement_tendsto R  E z hz).mul_const b
  have he₁ := he.congr' (Filter.Eventually.of_forall (fun T =>
    (hb (E ∪ T) Finset.subset_union_left).symm))
  exact tendsto_nhds_unique hl₁ he₁

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
