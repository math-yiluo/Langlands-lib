/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeOpen
public import WeilConjectures.TraceFormula.CompactPullback
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-!

# Coherences for the open piece of the trace additivity

For an open immersion `j : U ⟶ X` stable under the Frobenius, the extension by zero commutes with
the pullbacks along the Frobenii on compactly supported cohomology. This is the first square of
the open piece in blueprint `lemma-additivity-open-subscheme-complement` (Steps 2(a) and 3).

## Main input

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion`:
  for vertical open immersions, `Ex_!` is the extension-by-zero base change through
  `Rj_! ≅ j_!` (blueprint `def-exchange-projection`). It is computed with the trivial
  compactification `j = 𝟙 ∘ j`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_comp_isoOpen`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The exchange `H ⋙ jS' ⟶ jS ⋙ H'` of an isomorphism `θ : jU ⋙ H ≅ H' ⋙ jU'` along the
adjunctions `jS ⊣ jU` and `jS' ⊣ jU'` is compatible with the counits. -/
lemma Adjunction.exchangeLeft_app_comp_map_counit_app {A B A' B' : Type*} [Category A]
    [Category B] [Category A'] [Category B'] {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'}
    {jU' : B' ⥤ A'} {H : A ⥤ A'} {H' : B ⥤ B'} (aj : jS ⊣ jU) (aj' : jS' ⊣ jU')
    (θ : jU ⋙ H ≅ H' ⋙ jU') (M : B) :
    (Adjunction.exchangeLeft aj aj' θ).app (jU.obj M) ≫ H'.map (aj.counit.app M) =
      jS'.map (θ.hom.app M) ≫ aj'.counit.app (H'.obj M) := by
  rw [Adjunction.exchangeLeft_app]
  have hε := aj'.counit.naturality (H'.map (aj.counit.app M))
  have hθ := θ.hom.naturality (aj.counit.app M)
  simp only [Functor.comp_map, Functor.id_map] at hε hθ
  simp only [Category.assoc]
  erw [← hε]
  rw [← jS'.map_comp_assoc (θ.hom.app _)]
  erw [← hθ]
  rw [← jS'.map_comp_assoc, ← Category.assoc,
    ← H.map_comp]
  erw [aj.right_triangle_components]
  simp

/-- A base change compatible with an exchange and a comparison of counits also intertwines
the original counits. -/
private lemma map_counit_eq_of_baseChange {A B : Type*} [Category A] [Category B]
    {jL jS : A ⥤ B} {jU : B ⥤ A} {H : A ⥤ A} {H' : B ⥤ B}
    (e : jL ⟶ jS) (ε : jU ⋙ jL ⟶ 𝟭 B) (εS : jU ⋙ jS ⟶ 𝟭 B)
    (θ : jU ⋙ H ⟶ H' ⋙ jU) (β : jL ⋙ H' ⟶ H ⋙ jL) (δ : H ⋙ jS ⟶ jS ⋙ H')
    (M : B) (hε : ε.app M = e.app (jU.obj M) ≫ εS.app M)
    (hε' : ε.app (H'.obj M) = e.app (jU.obj (H'.obj M)) ≫ εS.app (H'.obj M))
    (hβ : β.app (jU.obj M) ≫ e.app (H.obj (jU.obj M)) ≫ δ.app (jU.obj M) =
      H'.map (e.app (jU.obj M)))
    (hδ : δ.app (jU.obj M) ≫ H'.map (εS.app M) =
      jS.map (θ.app M) ≫ εS.app (H'.obj M)) :
    H'.map (ε.app M) = β.app (jU.obj M) ≫ jL.map (θ.app M) ≫ ε.app (H'.obj M) := by
  rw [hε, hε', Functor.map_comp, ← hβ]
  simp only [Category.assoc]
  rw [hδ, reassoc_of% e.naturality (θ.app M)]

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]


section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **`Ex_!` for open immersions is the extension-by-zero base change** (blueprint
`def-exchange-projection`: `Ex_!` is represented, for the compactification `f = 𝟙 ∘ f` of an open
immersion, by the canonical identification `Lg^* f_! ≅ f'_! Lg'^*`): through `Rf_! ≅ f_!`, the
compact-support base change of a cartesian square with vertical open immersions is the inverse of
the extension-by-zero exchange morphism. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion
    (sq : IsPullback g' f' f g) [IsOpenImmersion f.left] [IsOpenImmersion f'.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K ≫
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f').hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj K) ≫
        (boundedConstructibleOpenImmersionLowerShriekBaseChange' (Profinite.padicAlgClRingObj ℓ) ℓ
          sq.toCommSq).app K =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f).hom.app
          K) := by
  have h := congr_app (boundedConstructibleLowerShriekBaseChange_padicAlgCl_comp_isoOpen ℓ sq) K
  simpa using h

end BaseChange
section OpenImmersion

variable {X U : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The counit of `Rj_! ⊣ Lj^*` (the adjunction `Rj_! ⊣ Rj^!` transported along
`Rj^! ≅ Lj^*`) is the counit of `j_! ⊣ Lj^*` through `Rj_! ≅ j_!`. -/
lemma counit_app_ofNatIsoRight_upperShriekIsoUpperStar
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperShriekAdjunction ℓ j).ofNatIsoRight
        (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)).counit.app M =
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj M) ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app M := by
  have h := conjugateEquiv_counit
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleUpperShriekAdjunction ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom M
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl,
    conjugateIsoEquiv_apply_inv, Iso.symm_inv]
  exact h

omit [Fact (Nat.Prime (ringChar k))] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] in
/-- An open immersion `j` stable under universal homeomorphisms `Φ_U ≫ j = j ≫ Φ` is the base
change of itself along `Φ`: the square `Φ_U ≫ j = j ≫ Φ` is cartesian. -/
lemma isPullback_of_comp_eq_of_isOpenImmersion {Φ : X ⟶ X} {ΦU : U ⟶ U}
    [IsUniversalHomeomorphism Φ.left] [IsUniversalHomeomorphism ΦU.left]
    (hj : ΦU ≫ j = j ≫ Φ) : IsPullback ΦU j j Φ := by
  have hjl : ΦU.left ≫ j.left = j.left ≫ Φ.left := by
    rw [← Over.comp_left, hj, Over.comp_left]
  have H' : Φ.left ⁻¹ᵁ j.left.opensRange = j.left.opensRange := by
    refine TopologicalSpace.Opens.ext (Set.ext fun x ↦ ?_)
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨u', rfl⟩ := ΦU.left.surjective u
      refine ⟨u', Φ.left.injective ?_⟩
      rw [← hu, ← Scheme.Hom.comp_apply, ← hjl, Scheme.Hom.comp_apply]
    · rintro ⟨u, rfl⟩
      exact ⟨ΦU.left u, by rw [← Scheme.Hom.comp_apply, hjl, Scheme.Hom.comp_apply]⟩
  exact IsPullback.of_map (Over.forget _) hj
    (IsOpenImmersion.isPullback ΦU.left j.left j.left Φ.left hjl.symm H')

omit [IsOpenImmersion j.left] in
/-- The Frobenius comparison `LΦ_U^* Lj^* ≅ Lj^* LΦ^*` of the pullback is the pullback comparison
of the (flipped) square `Φ_U ≫ j = j ≫ Φ`. -/
lemma weilUpperStarComparison_hom_app_eq {Φ : X ⟶ X} {ΦU : U ⟶ U} (hj : ΦU ≫ j = j ≫ Φ)
    (sq : CommSq j ΦU Φ j) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K =
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        sq).hom.app K := by
  rw [weilUpperStarComparison_hom_app, boundedConstructiblePullbackSquareComparison_hom_app]

/-- **The extension by zero commutes with the pullbacks along the Frobenii** (blueprint
`lemma-additivity-open-subscheme-complement`, Step 2(a), the open piece): for `Φ_U ≫ j = j ≫ Φ`, the
map `RΓ_c(U, Lj^* K) ≅ RΓ_c(X, Rj_! Lj^* K) --RΓ_c(ε)--> RΓ_c(X, K)` intertwines `Φ_U^♯`
(followed by the Frobenius comparison of the pullback) and `Φ^♯`. -/
lemma compToPoint_inv_app_comp_counit_comp_compactPullback {Φ : X ⟶ X} {ΦU : U ⟶ U}
    [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left]
    [IsUniversalHomeomorphism ΦU.left] (hj : ΦU ≫ j = j ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        (((boundedConstructibleUpperShriekAdjunction ℓ
          j).ofNatIsoRight (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)).counit.app
            K) ≫
      (compactPullback ℓ Φ).app K =
    (compactPullback ℓ ΦU).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint U)).map
        ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K)) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        (((boundedConstructibleUpperShriekAdjunction ℓ
          j).ofNatIsoRight (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)).counit.app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K)) := by
  have sq := isPullback_of_comp_eq_of_isOpenImmersion j hj
  have hC1 := boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion ℓ sq
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)
  have hEx := Adjunction.exchangeLeft_app_comp_map_counit_app
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq.flip) K
  rw [← boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft
    (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq] at hEx
  have hB := compactPullback_app_comp_baseChange ℓ sq
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)
  have hε := map_counit_eq_of_baseChange
    (jL := boundedConstructibleLowerShriek ℓ j)
    (jS := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (jU := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (H := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦU)
    (H' := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom
    (((boundedConstructibleUpperShriekAdjunction ℓ j).ofNatIsoRight
      (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)).counit)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j).counit
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq.flip).hom
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (boundedConstructibleOpenImmersionLowerShriekBaseChange' (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq) K
    (counit_app_ofNatIsoRight_upperShriekIsoUpperStar ℓ j K)
    (counit_app_ofNatIsoRight_upperShriekIsoUpperStar ℓ j _) hC1 hEx
  rw [weilUpperStarComparison_hom_app_eq ℓ j hj sq.toCommSq.flip]
  have hcp := (compactPullback ℓ Φ).naturality
    (((boundedConstructibleUpperShriekAdjunction ℓ j).ofNatIsoRight
      (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)).counit.app K)
  have hn := (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.naturality
    ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq.flip).hom.app K)
  have hB' : (compactPullback ℓ Φ).app ((boundedConstructibleLowerShriek
        ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) =
      (boundedConstructibleLowerShriekCompToPoint ℓ j).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
        (compactPullback ℓ ΦU).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.app _ := by
    rw [← reassoc_of% hB, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  simp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hcp hn
  rw [hcp, hε]
  simp only [Functor.map_comp]
  rw [reassoc_of% hB', Iso.inv_hom_id_app_assoc, reassoc_of% hn]

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing
