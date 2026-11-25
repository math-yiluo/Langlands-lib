/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeTest

/-!

# The transport map of classes along a proper morphism

For a proper morphism `f : X ⟶ Y`, `q = f × f` and `K' = Rf_* K`, the *transport*
`Rp₁'_! (Lp₂'^* K' ⊗ Rq_* Z) ⟶ Rf_* Rp₁_! (Lp₂^* K ⊗ Z)`, natural in `Z`
(`ProEtale.CondensedRing.classTransport`), defines the transport map
`Φ : Rq_* RHom(Lp₂^* K, Rp₁^! K) ⟶ RHom(Lp₂'^* K', Rp₁'^! K')`
(`ProEtale.CondensedRing.classTransportMap`, blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 1). Its test maps are computed by
`ProEtale.CondensedRing.classTest_map_comp_classTransportMap`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- The left projection morphism of `q` with fixed left factor, as a natural transformation
`Rq_! ⋙ (A ⊗ -) ⟶ (Lq^* A ⊗ -) ⋙ Rq_!`. -/
noncomputable def leftProjectionNatTrans {P Q : Over (Spec (.of k))} [LocallyOfFiniteType P.hom]
    [QuasiCompact P.hom] [IsSeparated P.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    [IsSeparated Q.hom] (q : P ⟶ Q) (A : Dᵇc(Q.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleLowerShriek ℓ q ⋙ tensorLeft A ⟶
      tensorLeft ((boundedConstructibleUpperStar _ ℓ q).obj A) ⋙
        boundedConstructibleLowerShriek ℓ q where
  app T := Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ q) A T
  naturality _ _ u := Verdier.leftProjection_naturality _ A u

/-- The *transport* `Rp₁'_! (Lp₂'^* K' ⊗ Rq_* Z) ⟶ Rf_* Rp₁_! (Lp₂^* K ⊗ Z)` along `q = f × f`,
natural in `Z`: `Rq_* ≅ Rq_!`, the left projection morphism of `q`, the composition law for
`q ≫ p₁' = p₁ ≫ f`, the transported counit `Lq^* Lp₂'^* Rf_* K ⟶ Lp₂^* K` and `Rf_! ≅ Rf_*`. -/
noncomputable def classTransport :
    boundedConstructibleLowerStar ℓ (prod.map f f) ⋙
        tensorLeft ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ f).obj K)) ⋙
        boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y) ⟶
      tensorLeft ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K) ⋙
        boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X) ⋙
        boundedConstructibleLowerStar ℓ f :=
  Functor.whiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (prod.map f f)).inv
      (tensorLeft ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ f).obj K)) ⋙
        boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (leftProjectionNatTrans ℓ (prod.map f f) _)
      (boundedConstructibleLowerShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (tensorLeft ((boundedConstructibleUpperStar _ ℓ (prod.map f f)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ f).obj K))))
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom ≫
    Functor.whiskerRight ((curriedTensor _).map (prodUpperStarCounit ℓ (prod.map_snd f f) K))
      (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X) ⋙
        boundedConstructibleLowerShriek ℓ f) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerLeft (tensorLeft ((boundedConstructibleUpperStar _ ℓ
        (prod.snd : X ⨯ X ⟶ X)).obj K) ⋙
        boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X))
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom ≫
    (Functor.associator _ _ _).hom

/-- The *transport map* `Φ : Rq_* RHom(Lp₂^* K, Rp₁^! K) ⟶ RHom(Lp₂'^* K', Rp₁'^! K')`
(blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, Step 1). -/
noncomputable def classTransportMap :
    (boundedConstructibleLowerStar ℓ (prod.map f f)).obj
        ((ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj K)) ⟶
      (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ f).obj K))).obj
        ((boundedConstructibleUpperShriek ℓ (prod.fst : Y ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar ℓ f).obj K)) :=
  curry (((boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : Y ⨯ Y ⟶ Y)).homEquiv _ _)
    ((classTransport ℓ f K).app _ ≫ (boundedConstructibleLowerStar ℓ f).map (classTest ℓ K
        (𝟙 _))))

-- the compactly supported direct images are unfolded in the defeq checks
/-- **The test maps of the transport map** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 1): `test(Rq_* ψ ≫ Φ) = Rf_* test(ψ)` read
through the transport. -/
lemma classTest_map_comp_classTransportMap {Z : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : Z ⟶ (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K)).obj
      ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj K)) :
    classTest ℓ ((boundedConstructibleLowerStar ℓ f).obj K)
        ((boundedConstructibleLowerStar ℓ (prod.map f f)).map ψ ≫ classTransportMap ℓ f K) =
      (classTransport ℓ f K).app Z ≫
        (boundedConstructibleLowerStar ℓ f).map (classTest ℓ K ψ) := by
  have hψ := classTest_comp ℓ ψ (𝟙 _)
  rw [Category.comp_id] at hψ
  have hΦ : classTest ℓ ((boundedConstructibleLowerStar ℓ f).obj K) (classTransportMap ℓ f K) =
      (classTransport ℓ f K).app _ ≫
        (boundedConstructibleLowerStar ℓ f).map (classTest ℓ K (𝟙 _)) :=
    by simp only [classTest, classTransportMap, uncurry_curry, Equiv.symm_apply_apply]
  rw [classTest_comp]
  rw [hΦ]
  conv_rhs => rw [hψ, Functor.map_comp]
  exact (classTransport ℓ f K).naturality_assoc ψ _

end AlgebraicGeometry.ProEtale.CondensedRing
