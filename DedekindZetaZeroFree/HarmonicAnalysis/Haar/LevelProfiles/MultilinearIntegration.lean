module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LevelProfiles.ProductIntegration

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem full_multilinear_integral (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (hD : localDifferentSupport F ⊆ (Q : Set _))
    {J : (fullLevel R P C Q hQ).val → Type} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    {V : (fullLevel R P C Q hQ).val → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (e : ∀ i, V i ≃ₗ[ℂ] (J i → ℂ)) (L : MultilinearMap ℂ V ℂ)
    (f : ∀ i, RootPoint R i.val → V i) (v : ∀ i, V i)
    (hf : ∀ i j, Integrable (fun x => e i (f i x) j) (arithmeticRootMeasure R N i.val))
    (hv : ∀ i j, e i (v i) j = ∫ x, e i (f i x) j ∂arithmeticRootMeasure R N i.val) :
    Integrable (fun x : KPGlobalTorusFunctionData.Adeles F => L (fun i => f i (rootCoordinate R x i.val)))
      ((KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) ∧
      (∫ x : KPGlobalTorusFunctionData.Adeles F, L (fun i => f i (rootCoordinate R x i.val))
        ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) = L v := by
  let w (i : (fullLevel R P C Q hQ).val) (j : J i) := (e i).symm (Pi.single j 1)
  have he (y : ∀ i, V i) : L y =
      ∑ r : ∀ i, J i, (∏ i, e i (y i) (r i)) * L (fun i => w i (r i)) := by
    have hex (i : (fullLevel R P C Q hQ).val) : y i = ∑ j, e i (y i) j • w i j := by
      apply (e i).injective
      simp only [map_sum, map_smul, w, LinearEquiv.apply_symm_apply]
      rw [← Finset.univ_sum_single (e i (y i))]
      apply Finset.sum_congr rfl
      intro j _
      funext k
      simp [Pi.single_apply]
    calc
      L y = L (fun i => ∑ j, e i (y i) j • w i j) := congrArg L (funext hex)
      _ = ∑ r : ∀ i, J i, (∏ i, e i (y i) (r i)) * L (fun i => w i (r i)) := by
        rw [L.map_sum_finset]
        apply Finset.sum_congr rfl
        intro r _
        simpa only [smul_eq_mul] using
          L.map_smul_univ (fun i => e i (y i) (r i)) (fun i => w i (r i))
  have hi (r : ∀ i, J i) : Integrable
      (fun x : KPGlobalTorusFunctionData.Adeles F => (∏ i, e i (f i (rootCoordinate R x i.val)) (r i)) * L (fun i => w i (r i)))
      ((KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) := (full_product_integrable R N P C Q hQ hD (fun i x => e i (f i x) (r i)) (fun i => hf i (r i))).mul_const _
  have hef : (fun x : KPGlobalTorusFunctionData.Adeles F => L (fun i => f i (rootCoordinate R x i.val))) =
      (fun x => ∑ r : ∀ i, J i, (∏ i, e i (f i (rootCoordinate R x i.val)) (r i)) * L (fun i => w i (r i))) :=
    funext (fun x => he (fun i => f i (rootCoordinate R x i.val)))
  constructor
  · rw [hef]
    exact integrable_finsetSum _ (fun r _ => hi r)
  · rw [hef, he v]
    rw [integral_finsetSum _ (fun r _ => hi r)]
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_mul_const]
    have hp := full_product_integral R N P C Q hQ hD (fun i x => e i (f i x) (r i))
    rw [hp]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact (hv i (r i)).symm

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
