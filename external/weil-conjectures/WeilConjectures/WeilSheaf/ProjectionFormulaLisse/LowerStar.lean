/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.IhomLisse.UpperStar
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# The projection formula for the pushforward of pro-étale Weil sheaves

For a morphism `φ : X ⟶ Y` of `k₀`-schemes and a pro-étale Weil sheaf `A` on `Y` with lisse
underlying sheaf, the pushforward commutes with internal homs:
`[A, φ_* N] ≅ φ_* [φ^* A, N]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCompIhomFunctorIso`).

The comparison is the mate, under the adjunction `φ^* ⊣ φ_*` of pro-étale Weil sheaves, of the
isomorphism `φ^* [A, -] ≅ [φ^* A, φ^* -]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso`); in particular it is a
morphism of pro-étale Weil sheaves. On underlying sheaves it is the mate of the comparison
`g^* 𝓗om(M, -) ⟶ 𝓗om(g^* M, g^* -)`, itself the mate of the isomorphism
`g^*(- ⊗ M) ≅ g^* - ⊗ g^* M` under the tensor–hom adjunctions; the iterated mate is a conjugate
of an isomorphism, hence an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_mateEquiv_adicUpperStarIhomComparison`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {Y Z : Scheme.{u}} (g : Z ⟶ Y)

variable (l) in
/-- The comparison `g^* 𝓗om(M, -) ⟶ 𝓗om(g^* M, g^* -)` as a natural transformation. -/
noncomputable def adicUpperStarIhomComparisonNatTrans (M : AdicSheaf l Y) :
    AdicSheaf.ihom M ⋙ (g)^*ᵃ[l] ⟶ (g)^*ᵃ[l] ⋙ AdicSheaf.ihom ((g)^*ᵃ[l].obj M) where
  app N := adicUpperStarIhomComparison l g M N
  naturality _ _ f := adicUpperStarIhomComparison_naturality g M f

/-- The comparison `g^* 𝓗om(M, -) ⟶ 𝓗om(g^* M, g^* -)` is the mate of the inverse of the
isomorphism `g^*(- ⊗ M) ≅ g^* - ⊗ g^* M` under the tensor–hom adjunctions. -/
lemma mateEquiv_adicUpperStarTensorLeftIso_inv (M : AdicSheaf l Y) :
    (mateEquiv (Mod.ihomAdjunction M) (Mod.ihomAdjunction ((g)^*ᵃ[l].obj M))
      (TwoSquare.mk _ _ _ _ (adicUpperStarTensorLeftIso l g M).inv)) =
      adicUpperStarIhomComparisonNatTrans l g M := by
  ext N
  simp only [mateEquiv_apply]
  simp [adicUpperStarIhomComparisonNatTrans, adicUpperStarIhomComparison,
    Adjunction.homEquiv_unit]

/-- **The projection formula for the internal hom, as a mate**: the mate under `g^* ⊣ g_*` of the
comparison `g^* 𝓗om(M, -) ⟶ 𝓗om(g^* M, g^* -)` is an isomorphism
`g_* ⋙ 𝓗om(M, -) ≅ 𝓗om(g^* M, -) ⋙ g_*`: it is the conjugate of the isomorphism
`g^*(- ⊗ M) ≅ g^* - ⊗ g^* M` (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`). -/
instance isIso_mateEquiv_adicUpperStarIhomComparison (M : AdicSheaf l Y) :
    IsIso (mateEquiv (adicUpperStarLowerStarAdjunction l g) (adicUpperStarLowerStarAdjunction l g)
      (TwoSquare.mk _ _ _ _ (adicUpperStarIhomComparisonNatTrans l g M))) := by
  rw [← mateEquiv_adicUpperStarTensorLeftIso_inv, iterated_mateEquiv_conjugateEquiv]
  infer_instance

end ProEtale

namespace ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The comparison `[A, φ_* N] ⟶ φ_* [φ^* A, N]` of pro-étale Weil sheaves, for `A` with lisse
underlying sheaf: the mate under `φ^* ⊣ φ_*` of `φ^* [A, -] ≅ [φ^* A, φ^* -]`. -/
noncomputable def lowerStarCompIhomFunctorHom (A : ProEtaleWeilSheaf k₀ l Y)
    (hA : ProEtale.IsAdicLisseSheaf A.carrier) :
    lowerStar k₀ l φ ⋙ ihomFunctor k₀ l Y A ⟶
      ihomFunctor k₀ l X ((upperStar k₀ l φ).obj A) ⋙ lowerStar k₀ l φ :=
  (mateEquiv (upperStarLowerStarAdjunction k₀ l φ) (upperStarLowerStarAdjunction k₀ l φ)
    (TwoSquare.mk _ _ _ _ (ihomFunctorCompUpperStarIso φ A hA).hom))

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] in
/-- The underlying morphism of the comparison `[A, φ_* N] ⟶ φ_* [φ^* A, N]` is the mate of the
comparison of `ℓ`-adic sheaves. -/
lemma lowerStarCompIhomFunctorHom_app_hom_f (A : ProEtaleWeilSheaf k₀ l Y)
    (hA : ProEtale.IsAdicLisseSheaf A.carrier) (N : ProEtaleWeilSheaf k₀ l X) :
    ((lowerStarCompIhomFunctorHom φ A hA).app N).hom.f =
      (mateEquiv (ProEtale.adicUpperStarLowerStarAdjunction l
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _)))
        (ProEtale.adicUpperStarLowerStarAdjunction l
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _)))
        (TwoSquare.mk _ _ _ _ (ProEtale.adicUpperStarIhomComparisonNatTrans l
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _)) A.carrier))).app
        N.carrier := by
  simp only [lowerStarCompIhomFunctorHom, mateEquiv_apply]
  rfl

instance isIso_lowerStarCompIhomFunctorHom (A : ProEtaleWeilSheaf k₀ l Y)
    (hA : ProEtale.IsAdicLisseSheaf A.carrier) :
    IsIso (lowerStarCompIhomFunctorHom φ A hA) := by
  have (N : ProEtaleWeilSheaf k₀ l X) : IsIso ((lowerStarCompIhomFunctorHom φ A hA).app N) := by
    have : IsIso ((IsoAlgebra.forget _).map ((lowerStarCompIhomFunctorHom φ A hA).app N)) := by
      change IsIso ((lowerStarCompIhomFunctorHom φ A hA).app N).hom.f
      rw [lowerStarCompIhomFunctorHom_app_hom_f]
      infer_instance
    exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)
  exact NatIso.isIso_of_isIso_app _

/-- **The projection formula for pro-étale Weil sheaves**: for `A` with lisse underlying sheaf,
`[A, φ_* N] ≅ φ_* [φ^* A, N]` naturally in `N`. -/
noncomputable def lowerStarCompIhomFunctorIso (A : ProEtaleWeilSheaf k₀ l Y)
    (hA : ProEtale.IsAdicLisseSheaf A.carrier) :
    lowerStar k₀ l φ ⋙ ihomFunctor k₀ l Y A ≅
      ihomFunctor k₀ l X ((upperStar k₀ l φ).obj A) ⋙ lowerStar k₀ l φ :=
  asIso (lowerStarCompIhomFunctorHom φ A hA)

end ProEtaleWeilSheaf

end AlgebraicGeometry
