/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ExceptionalKunnethFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalShift
public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange

/-!

# The Künneth–Verdier map and closed pushforward in the second factor

Let `g : Z ⟶ Y` be a closed immersion of separated `k`-schemes of finite type and
`G = 𝟙_X × g : X ⨯ Z ⟶ X ⨯ Y`. For `M ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and `N' ∈ Dᵇc(Z)⟦ℚ̲̄_ℓ⟧`, the Künneth–Verdier
map `κ_Y(M, Rg_! N')` (`ProEtale.CondensedRing.kunnethVerdierMap`) is an isomorphism if and only
if `κ_Z(M, N')` is
(`ProEtale.CondensedRing.isIso_kunnethVerdierMap_lowerShriek_iff_of_isClosedImmersion`).

Indeed there is a commutative square
```
RG_! (M ⊠ D_Z N') ──RG_! κ_Z──▶ RG_! RHom(Lq_Z^* N', Rp_Z^! M)
        │σ                                  │τ
        ▼                                   ▼
  M ⊠ D_Y (Rg_! N') ──κ_Y──▶ RHom(Lq^* Rg_! N', Rp^! M)
```
whose vertical maps are isomorphisms: `σ` is the trace map of the cartesian square
`q_Z ≫ g = G ≫ q` (`ProEtale.CondensedRing.exceptionalKunnethTraceOfSquare`, here for the
absolute Verdier exchange `Rg_! D_Z N' ≅ D_Y Rg_! N'`), and `τ` is `Rp_Z^! M ≅ RG^! Rp^! M`, the
Verdier exchange of `G` and compact-support base change. The square is the abstract chase
`CategoryTheory.ProjectionBaseChange.trace_comp_curry`, whose inputs are the functoriality of the
exceptional Künneth map `α` along `G` (`ProEtale.CondensedRing.exceptionalKunnethMap_comp_prodMap`),
the compatibilities of the projection formula with base change and, for proper morphisms, with
the adjunction `Lf^* ⊣ Rf_!` (`WeilConjectures.TraceFormula.LowerShriekCoherence`,
`WeilConjectures.PoincareDuality.ProjectionFormulaCoherence`), and the
compatibility of compact-support base change with the units of `Lf^* ⊣ Rf_!`
(`map_unit_app_comp_boundedConstructibleLowerShriekBaseChange_padicAlgCl_app`).
Finally `RG_!` reflects isomorphisms, `G` being a monomorphism
(`ProEtale.CondensedRing.isIso_of_isIso_lowerShriek_map_of_mono`).

The chase is first carried out for an arbitrary cartesian square
(`ProEtale.CondensedRing.isIso_curry_kunnethPairing_iff_of_isPullback`): stating it for general
objects keeps the terms compared by the kernel small.

## Main statements

- `ProEtale.CondensedRing.isIso_kunnethVerdierMap_lowerShriek_iff_of_isClosedImmersion`

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

section Mono

variable {W V : Over (Spec (.of k))}
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

/-- For a monomorphism `G`, the compactly supported direct image `RG_!` reflects isomorphisms: by
compact-support base change in the cartesian square `𝟙 ≫ G = 𝟙 ≫ G`, `LG^* RG_! ≅ R𝟙_! L𝟙^*`. -/
lemma isIso_of_isIso_lowerShriek_map_of_mono (G : W ⟶ V) [Mono G]
    {A B : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : A ⟶ B)
    [IsIso ((boundedConstructibleLowerShriek ℓ G).map φ)] : IsIso φ := by
  have sq : IsPullback (𝟙 W) (𝟙 W) G G := IsKernelPair.id_of_mono G
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have hn := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).naturality φ
  have : IsIso ((boundedConstructibleLowerShriek ℓ (𝟙 W)).map
      ((boundedConstructibleUpperStar _ ℓ (𝟙 W)).map φ)) := by
    have : IsIso (((boundedConstructibleLowerShriek ℓ G ⋙
        boundedConstructibleUpperStar _ ℓ G).map φ ≫
          (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app B)) := by
      dsimp only [Functor.comp_map]
      infer_instance
    rw [hn] at this
    dsimp only [Functor.comp_map] at this
    exact IsIso.of_isIso_comp_left
      ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app A) _
  rw [NatIso.isIso_map_iff (boundedConstructibleLowerShriekId ℓ W)] at this
  dsimp only [Functor.id_obj, Functor.id_map] at this
  rw [NatIso.isIso_map_iff (boundedConstructibleUpperStarId _ ℓ W)] at this
  exact this

end Mono

attribute [local irreducible] boundedConstructibleLowerShriek boundedConstructibleUpperStar
  boundedConstructibleUpperShriek

section Square

variable {X Y Z W V : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

-- The instantiation of the abstract chase involves large terms.
/-- **The Künneth–Verdier pairing and closed pushforward along a cartesian square**: for a
cartesian square `q_W ≫ g = G ≫ q_V` with `G` and `g` proper and `G` a monomorphism, where
`(p_W, q_W)` and `(p_V, q_V)` exhibit `W` and `V` as fibre products over the base point, and for
morphisms `α_Y`, `α_Z` related by the functoriality of the exceptional Künneth map along `G`
(`hstar`), the transpose of the Künneth–Verdier pairing of `(M, Rg_! N')` with `α_Y` is an
isomorphism if and only if that of `(M, N')` with `α_Z` is. -/
theorem isIso_curry_kunnethPairing_iff_of_isPullback (pW : W ⟶ X) (qW : W ⟶ Z) (pV : V ⟶ X)
    (qV : V ⟶ Y) (G : W ⟶ V) (g : Z ⟶ Y) [IsProper G.left] [IsProper g.left] [Mono G]
    (sq : IsPullback qW G g qV) (hp : G ≫ pV = pW)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (αY : (boundedConstructibleUpperStar _ ℓ pV).obj M ⊗
        (boundedConstructibleUpperStar _ ℓ qV).obj (dualizingComplex' ℓ Y) ⟶
      (boundedConstructibleUpperShriek ℓ pV).obj M)
    (αZ : (boundedConstructibleUpperStar _ ℓ pW).obj M ⊗
        (boundedConstructibleUpperStar _ ℓ qW).obj (dualizingComplex' ℓ Z) ⟶
      (boundedConstructibleUpperShriek ℓ pW).obj M)
    (hstar : αZ = (boundedConstructibleUpperShriekAdjunction ℓ G).homEquiv _ _
        (exceptionalKunnethTraceOfSquare ℓ pW qW pV qV G g sq hp M ≫ αY) ≫
      (boundedConstructibleUpperShriekCompOfEq ℓ hp).inv.app M)
    (N' : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (curry ((α_ _ _ _).inv ≫
        ((β_ ((boundedConstructibleUpperStar _ ℓ qV).obj
          ((boundedConstructibleLowerShriek ℓ g).obj N'))
          ((boundedConstructibleUpperStar _ ℓ pV).obj M)).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ qV)
          ((boundedConstructibleLowerShriek ℓ g).obj N')
          ((ihom ((boundedConstructibleLowerShriek ℓ g).obj N')).obj (dualizingComplex' ℓ Y))) ≫
        (_ ◁ (boundedConstructibleUpperStar _ ℓ qV).map
          ((ihom.ev ((boundedConstructibleLowerShriek ℓ g).obj N')).app
            (dualizingComplex' ℓ Y))) ≫ αY)) ↔
      IsIso (curry ((α_ _ _ _).inv ≫
        ((β_ ((boundedConstructibleUpperStar _ ℓ qW).obj N')
          ((boundedConstructibleUpperStar _ ℓ pW).obj M)).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ qW) N'
          ((ihom N').obj (dualizingComplex' ℓ Z))) ≫
        (_ ◁ (boundedConstructibleUpperStar _ ℓ qW).map
          ((ihom.ev N').app (dualizingComplex' ℓ Z))) ≫ αZ)) := by
  have ibs := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have hstar' : (boundedConstructibleLowerShriek ℓ G).map
      (αZ ≫ (boundedConstructibleUpperShriekCompOfEq ℓ hp).hom.app M) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ G).counit.app
        ((boundedConstructibleUpperShriek ℓ pV).obj M) =
      ProjectionBaseChange.trace
        (fun A B ↦ ((boundedConstructibleExceptionalProjection ℓ G).app A).app B)
        (boundedConstructibleUpperStar _ ℓ qV) (boundedConstructibleUpperStar _ ℓ qW)
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
        ((boundedConstructibleUpperStar _ ℓ pV).obj M)
        ((boundedConstructibleUpperStarCompOfEq ℓ hp).hom.app M) (dualizingComplex' ℓ Z)
        (dualizingComplex' ℓ Y)
        ((boundedConstructibleLowerShriek ℓ g).map (dualizingComplexComp ℓ g).inv ≫
          (boundedConstructibleUpperShriekAdjunction ℓ g).counit.app (dualizingComplex' ℓ Y)) ≫
        αY := by
    rw [hstar, Category.assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    rw [Category.comp_id]
    refine ((boundedConstructibleUpperShriekAdjunction ℓ G).homEquiv_counit _ _ _).symm.trans ?_
    exact Equiv.symm_apply_apply _ _
  refine (ProjectionBaseChange.isIso_curry_iff
    (aG := boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ G)
    (aGu := boundedConstructibleUpperShriekAdjunction ℓ G)
    (pfG := boundedConstructibleExceptionalProjection ℓ G)
    (hcG := fun A B ↦ upperStar_map_exceptionalProjection_comp_counit ℓ G A B)
    (ag := boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ g)
    (agu := boundedConstructibleUpperShriekAdjunction ℓ g)
    (pfg := boundedConstructibleExceptionalProjection ℓ g)
    (q := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ qV)
    (qZ := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ qW)
    (BC := boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (θ := boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq)
    (hmate := ProjectionBaseChange.counit_mate_of_unit
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ G)
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ g)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ qV)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ qW)
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        sq.toCommSq)
      (fun M ↦ map_unit_app_comp_boundedConstructibleLowerShriekBaseChange_padicAlgCl_app ℓ sq M))
    (hPF2 := boundedConstructibleExceptionalProjectionMorphism_baseChange ℓ sq)
    (hsymm := fun A B ↦ boundedConstructible_braiding_hom_braiding_hom A B)
    (hsymm' := fun A B ↦ boundedConstructible_braiding_hom_braiding_hom A B)
    (P := (boundedConstructibleUpperStar _ ℓ pV).obj M)
    (e := (boundedConstructibleUpperStarCompOfEq ℓ hp).hom.app M)
    (d := dualizingComplexComp ℓ g) (αY := αY) (αZ := αZ)
    (eT := (boundedConstructibleUpperShriekCompOfEq ℓ hp).hom.app M) (hstar := hstar') N').trans
    ⟨fun _ ↦ isIso_of_isIso_lowerShriek_map_of_mono ℓ G _, fun _ ↦ inferInstance⟩

end Square

section Product

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

omit [Fact (ringChar k).Prime] in
/-- The product `𝟙 × g : X ⨯ Z ⟶ X ⨯ Y` of a closed immersion `g` is a closed immersion, being the
base change of `g` along the second projection. -/
instance isClosedImmersion_prodMap_left (g : Z ⟶ Y) [IsClosedImmersion g.left] :
    IsClosedImmersion (prod.map (𝟙 X) g).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    ((isPullback_prodMap_id X g).map (Over.forget _))
    (inferInstanceAs (IsClosedImmersion g.left))

/-- **The Künneth–Verdier map and closed pushforward in the second factor**: for a closed
immersion `g : Z ⟶ Y`, `M ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and `N' ∈ Dᵇc(Z)⟦ℚ̲̄_ℓ⟧`, the Künneth–Verdier map of
`(M, Rg_! N')` is an isomorphism if and only if that of `(M, N')` is. -/
theorem isIso_kunnethVerdierMap_lowerShriek_iff_of_isClosedImmersion (g : Z ⟶ Y)
    [IsClosedImmersion g.left] (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N' : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (kunnethVerdierMap ℓ (Y := Y) M
      ((boundedConstructibleLowerShriek ℓ g).obj N')) ↔
      IsIso (kunnethVerdierMap ℓ (Y := Z) M N') := by
  have : Mono g := Over.mono_of_mono_left g
  unfold kunnethVerdierMap kunnethVerdierPairing
  exact isIso_curry_kunnethPairing_iff_of_isPullback ℓ prod.fst prod.snd prod.fst prod.snd
    (prod.map (𝟙 X) g) g (isPullback_prodMap_id X g) (prodMap_id_fst X g) M
    (exceptionalKunnethMap ℓ (Y := Y) M) (exceptionalKunnethMap ℓ (Y := Z) M)
    (by rw [← exceptionalKunnethProdMapTrace_eq]; exact exceptionalKunnethMap_comp_prodMap ℓ M g) N'

end Product

end AlgebraicGeometry.ProEtale.CondensedRing
