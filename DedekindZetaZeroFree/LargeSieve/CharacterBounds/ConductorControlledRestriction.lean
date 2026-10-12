module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.UniformNormalizationData
public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

def CoreGood (Q : QuadraticHeckeFamily F c) : Prop :=
  ∀ a, Squarefree a → a ⊔ c = ⊤ → a ∣ Q.cond a ∧ Q.cond a ∣ a * c

theorem coprime_original {q a : Ideal (𝓞 F)} (hcq : c ∣ q)
    (haq : a ⊔ q = ⊤) : a ⊔ c = ⊤ := by
  rw [eq_top_iff, ← haq]
  exact sup_le_sup_left (Ideal.dvd_iff_le.mp hcq) a

def restrictFamily (Q : QuadraticHeckeFamily F c) (q : Ideal (𝓞 F))
    (hcq : c ∣ q) : QuadraticHeckeFamily F q where
  cond := Q.cond
  χ := Q.χ
  primitive := fun a ha haq => Q.primitive a ha (coprime_original hcq haq)
  quadratic := fun a b ha haq => Q.quadratic a b ha (coprime_original hcq haq)
  G := Q.G
  instGroup := Q.instGroup
  instFinite := Q.instFinite
  cls := Q.cls
  cls_top := Q.cls_top
  cls_mul := fun a b haq hbq =>
    Q.cls_mul a b (coprime_original hcq haq) (coprime_original hcq hbq)
  C := Q.C
  C_sq := Q.C_sq
  reciprocity := fun a b ha haq hb hbq hab =>
    Q.reciprocity a b ha (coprime_original hcq haq) hb (coprime_original hcq hbq) hab
  product_primitive := fun a b ha haq hb hbq hab hcls =>
    Q.product_primitive a b ha (coprime_original hcq haq) hb
      (coprime_original hcq hbq) hab hcls

@[simp] theorem restrictFamily_cond (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hcq : c ∣ q) (a : Ideal (𝓞 F)) :
    (restrictFamily Q q hcq).cond a = Q.cond a := rfl

@[simp] theorem restrictFamily_χ (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hcq : c ∣ q) (a : Ideal (𝓞 F)) :
    (restrictFamily Q q hcq).χ a = Q.χ a := rfl

@[simp] theorem restrictFamily_G (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hcq : c ∣ q) :
    (restrictFamily Q q hcq).G = Q.G := rfl

@[simp] theorem restrictFamily_instGroup (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hcq : c ∣ q) :
    (restrictFamily Q q hcq).instGroup = Q.instGroup := rfl

@[simp] theorem restrictFamily_instFinite (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hcq : c ∣ q) :
    (restrictFamily Q q hcq).instFinite = Q.instFinite := rfl

@[simp] theorem restrictFamily_cls (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hcq : c ∣ q) (a : Ideal (𝓞 F)) :
    (restrictFamily Q q hcq).cls a = Q.cls a := rfl

@[simp] theorem restrictFamily_C (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hcq : c ∣ q) (g h : Q.G) :
    (restrictFamily Q q hcq).C g h = Q.C g h := rfl

theorem exists_coreGood_restrictFamily (hc : c ≠ ⊥)
    (Q : QuadraticHeckeFamily F c) :
    ∃ q : Ideal (𝓞 F), q ≠ ⊥ ∧ ∃ hcq : c ∣ q,
      (∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ c = ⊤ →
        Q.cond a ∣ a * q ∧ a ∣ Q.cond a * q) ∧
      CoreGood (restrictFamily Q q hcq) := by
  obtain ⟨q, hq, hcq, H, hcore, _⟩ := allIndexConductorControl hc Q
  refine ⟨q, hq, hcq, H, ?_⟩
  intro a ha haq
  exact ⟨hcore a ha haq, (H a ha (coprime_original hcq haq)).1⟩

def CoreGood.allIndexNormalizedFamilyData {Q : QuadraticHeckeFamily F c}
    (hQ : CoreGood Q) (hc : c ≠ ⊥) : AllIndexNormalizedFamilyData Q where
  bad := c
  bad_ne_bot := hc
  original_dvd_bad := dvd_refl c
  index_dvd_conductor := fun a ha hac => (hQ a ha hac).1
  conductor_dvd_index_bad := fun a ha hac => (hQ a ha hac).2
  original_ne_bot := hc
  all_conductor_dvd := fun a ha hac => (hQ a ha hac).2
  all_index_dvd := fun a ha hac => dvd_mul_of_dvd_left (hQ a ha hac).1 c

abbrev CoreGood.allIndexData {Q : QuadraticHeckeFamily F c}
    (hQ : CoreGood Q) (hc : c ≠ ⊥) : AllIndexNormalizedFamilyData Q :=
  hQ.allIndexNormalizedFamilyData hc

@[simp] theorem CoreGood.allIndexNormalizedFamilyData_bad
    {Q : QuadraticHeckeFamily F c} (hQ : CoreGood Q) (hc : c ≠ ⊥) :
    (hQ.allIndexNormalizedFamilyData hc).bad = c := rfl

end DedekindZetaZeroFree.LargeSieve.Sieve
