module

public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.FiniteTensorSectionsAndTopology

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildJointBorelKernel
open KPKirillovFiniteTensor KPKirillovGenuineSectionCharts
open _root_.DedekindZetaZeroFree.KPKirillovFiniteTensor renaming scalarSectionAddCommGroup → scalarSectionAddCommGroup
open _root_.DedekindZetaZeroFree.KPKirillovFiniteTensor renaming tensorSectionAddCommGroup → tensorSectionAddCommGroup
attribute [local instance] scalarSectionAddCommGroup tensorSectionAddCommGroup
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable (W : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (m : W → ℕ)
  (hm : ∀ v, KPLocalChartTopology.MatrixChartDepth F v.val (m v))
  (ψ : ∀ v : W, Multiplicative (K F v.val) →* ℂˣ)
  (V : W → Type) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  (ρ : ∀ v : W, Representation ℂ (G F ζ hζ v.val) (V v))
  (D : LocalEmbeddingData F ζ hζ W m hm ψ V ρ)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

theorem evaluation_pure_sections (f : ∀ v, ScalarSections F ζ hζ W m ψ v)
    (e : JacquetTensor F ζ hζ W ψ V ρ) :
    tensorEvaluation F ζ hζ W m ψ V ρ (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e) =
      (∏ v, sectionValue F ζ hζ v.val (m v) (ψ v) (f v) 1) • e := by
  have hp (x : ∀ v, Jacquet F ζ hζ W ψ V ρ v) :
      tensorEvaluation F ζ hζ W m ψ V ρ
        (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ x) =
      (∏ v, sectionValue F ζ hζ v.val (m v) (ψ v) (f v) 1) • PiTensorProduct.tprod ℂ x := by
    change PiTensorProduct.map (localEvaluation F ζ hζ W m ψ V ρ)
      (tensorShuffle F ζ hζ W m ψ V ρ
        (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ x)) = _
    calc
      _ = PiTensorProduct.map (localEvaluation F ζ hζ W m ψ V ρ)
          (PiTensorProduct.tprod ℂ (fun v => f v ⊗ₜ[ℂ] x v)) :=
        congrArg (PiTensorProduct.map (localEvaluation F ζ hζ W m ψ V ρ))
          (tensorShuffle_tmul F ζ hζ W m ψ V ρ f x)
      _ = PiTensorProduct.tprod ℂ (fun v =>
          sectionValue F ζ hζ v.val (m v) (ψ v) (f v) 1 • x v) :=
        PiTensorProduct.map_tprod _ _
      _ = _ := (PiTensorProduct.tprod ℂ).map_smul_univ _ _
  induction e using PiTensorProduct.induction_on with
  | add e d he hd => simp only [TensorProduct.tmul_add,map_add,he,hd,smul_add]
  | smul_tprod c e =>
    simp only [TensorProduct.tmul_smul,map_smul,hp]
    exact smul_comm _ _ _

theorem translated_quotient (a : ProductAffine F ζ hζ W)
    (f : ∀ v, ScalarSections F ζ hζ W m ψ v)
    (e : JacquetTensor F ζ hζ W ψ V ρ) :
    tensorQuotient F ζ hζ W ψ V ρ
      (ambientAction F ζ hζ W V ρ a
        (tensorEmbedding F ζ hζ W m hm ψ V ρ D (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e))) =
      (∏ v, sectionValue F ζ hζ v.val (m v) (ψ v)
        (rightAction F ζ hζ v.val (m v) (hm v) (ψ v) ℂ (a v) (f v)) 1) • e := by
  let y := PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e
  let b := inducedAction F ζ hζ W m hm ψ (JacquetTensor F ζ hζ W ψ V ρ) a y
  calc
    _ = tensorQuotient F ζ hζ W ψ V ρ
        (tensorEmbedding F ζ hζ W m hm ψ V ρ D b) :=
      congrArg (tensorQuotient F ζ hζ W ψ V ρ)
        (tensorEmbedding_equivariant F ζ hζ W m hm ψ V ρ D a y).symm
    _ = tensorEvaluation F ζ hζ W m ψ V ρ b :=
      LinearMap.congr_fun (tensor_evaluation_square F ζ hζ W m hm ψ V ρ D) b
    _ = tensorEvaluation F ζ hζ W m ψ V ρ
        (PiTensorProduct.tprod ℂ (fun v =>
          rightAction F ζ hζ v.val (m v) (hm v) (ψ v) ℂ (a v) (f v)) ⊗ₜ[ℂ] e) := by
      congr 1
      simp only [b,y,inducedAction,MonoidHom.coe_mk,OneHom.coe_mk,TensorProduct.map_tmul,
        PiTensorProduct.map_tprod,LinearMap.id_apply]
    _ = _ := evaluation_pure_sections F ζ hζ W m ψ V ρ _ e

theorem full_borel_kernel_zero
    (L : AmbientTensor F W V →ₗ[ℂ] ℂ)
    (l : JacquetTensor F ζ hζ W ψ V ρ →ₗ[ℂ] ℂ)
    (hL : l.comp (tensorQuotient F ζ hζ W ψ V ρ) = L)
    (a : ProductAffine F ζ hζ W) (f : ∀ v, ScalarSections F ζ hζ W m ψ v)
    (e : JacquetTensor F ζ hζ W ψ V ρ) (he : l e = 0) :
    L (ambientAction F ζ hζ W V ρ a
      (tensorEmbedding F ζ hζ W m hm ψ V ρ D (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e))) = 0 := by
  have hp := LinearMap.congr_fun hL
    (ambientAction F ζ hζ W V ρ a
      (tensorEmbedding F ζ hζ W m hm ψ V ρ D (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e)))
  calc
    _ = l (tensorQuotient F ζ hζ W ψ V ρ
        (ambientAction F ζ hζ W V ρ a
          (tensorEmbedding F ζ hζ W m hm ψ V ρ D (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e)))) := hp.symm
    _ = l ((∏ v, sectionValue F ζ hζ v.val (m v) (ψ v)
        (rightAction F ζ hζ v.val (m v) (hm v) (ψ v) ℂ (a v) (f v)) 1) • e) :=
      congrArg l (translated_quotient F ζ hζ W m hm ψ V ρ D a f e)
    _ = _ • l e := l.map_smul _ e
    _ = _ • (0 : ℂ) := congrArg (fun z : ℂ =>
      (∏ v, sectionValue F ζ hζ v.val (m v) (ψ v)
        (rightAction F ζ hζ v.val (m v) (hm v) (ψ v) ℂ (a v) (f v)) 1) • z) he
    _ = 0 := smul_zero _

end DedekindZetaZeroFree.FourierContinuation.WildJointBorelKernel

end
