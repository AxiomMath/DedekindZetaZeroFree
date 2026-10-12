module

public import ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteAbelianization
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
public import ClassFieldTheory.Definitions.GlobalClassFieldTheory.IdeleClassConnectedQuotient
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Topological global reciprocity in Mathlib's groups

The existing maximal-abelian Artin isomorphism is transported through the
topological comparison of idèle class groups and the canonical comparison of
absolute Galois abelianizations. This module proves the small-universe case;
universe transport for the public statement is separate.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

/-- The maximal-abelian Artin isomorphism, expressed entirely in Mathlib's
idèle-class and absolute-Galois groups, for a small number-field carrier. -/
noncomputable def mathlibIdeleClassConnectedQuotientEquivAbelianization
    (K : Type) [Field K] [NumberField K] :
    ClassFieldTheory.IdeleClassConnectedQuotient K ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K := by
  let classEquiv : IdeleClassGroup K ≃ₜ*
      NumberField.IdeleClassGroup (𝓞 K) K :=
    IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K
  let compEquiv := ClassFieldTheory.connectedComponentQuotientCongr classEquiv
  let e₁ : ClassFieldTheory.IdeleClassConnectedQuotient K ≃ₜ*
      ideleClassComponentQuotient K := compEquiv.symm
  let e₂ : ideleClassComponentQuotient K ≃ₜ*
      Gal(maximalAbelianExtension K / K) :=
    ideleClassComponentQuotientEquivMaximalAbelianGalois K
  let e₃ : TopologicalAbelianization Gal(SeparableClosure K / K) ≃ₜ*
      Gal(maximalAbelianExtension K / K) :=
    absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K
  let e₄ : Field.absoluteGaloisGroupAbelianization K ≃ₜ*
      TopologicalAbelianization Gal(SeparableClosure K / K) :=
    absoluteGaloisGroupAbelianizationEquivSeparable K
  exact e₁.trans (e₂.trans (e₃.symm.trans e₄.symm))

end GlobalClassFieldTheory.Reciprocity

end
