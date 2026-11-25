/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChangeComp
public import WeilConjectures.TraceFormula.ExceptionalKunnethFunctoriality
import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion
import WeilConjectures.TraceFormula.OpenPieceCoherence

/-!

# The projection formula is compatible with base change

For a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
of separated `k`-schemes of finite type, the exceptional projection morphisms
`PF^!_f : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` of `f` and `f'` are compatible with compact-support
base change `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` (SGA 4, Exposé XVII, §5.2): the square
```
Lg^* (Rf_! K ⊗ᴸ B) ──Lg^* PF──▶ Lg^* Rf_! (K ⊗ᴸ Lf^* B) ──Ex_!──▶ Rf'_! Lg'^* (K ⊗ᴸ Lf^* B)
       │≅                                                               │≅
       ▼                                                               ▼
Rf'_! Lg'^* K ⊗ᴸ Lg^* B ─────────────PF'────────────▶ Rf'_! (Lg'^* K ⊗ᴸ Lf'^* Lg^* B)
```
commutes. In the formalism of `CategoryTheory.ProjectionBaseChange` this is
`CategoryTheory.ProjectionBaseChange.PFBaseChange`.

## Proof

Factor `f = i ≫ p` through its compactification `compactificationOverField f`, with `i` an open
immersion and `p` proper, and base change both pieces along `g`. For `p` the statement is
`ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_baseChange`
(`WeilConjectures.TraceFormula.LowerShriekCoherence`). For `i` the projection morphisms are the
inverses of the projection comparisons of the extensions by zero and `Ex_!` is the inverse of the
base change of extension by zero; this is
`ProEtale.CondensedRing.pfBaseChange_boundedConstructibleExceptionalProjection_of_isOpenImmersion`.
The two are assembled by the compatibilities of the projection formula, of `Ex_!` and of the
pullback comparisons with composition
(`ProEtale.CondensedRing.pfBaseChange_boundedConstructibleExceptionalProjection_of_factorisation`).
The diagram chases are carried out for abstract functors in
`WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChangeComp`.

## Main statements

- `ProEtale.CondensedRing.pfBaseChange_boundedConstructibleExceptionalProjection`: the clause
  "compatible with base change" of blueprint `proposition-composition-base-change-rf-shriek--1`
  (section `chap-The-six-operations-on-Dbctf`).

## Implementation notes

As in `WeilConjectures.TraceFormula.KunnethVerdierOpen`, the projection of the monoidal category
instance is made the preferred tensor structure, and the composition law of the projection
formula is restated accordingly
(`ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_comp_of_eq'`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

-- see the implementation notes of `WeilConjectures.TraceFormula.KunnethVerdierOpen`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

/-- The pullback comparison of the transposed square is the inverse of the pullback comparison. -/
lemma boundedConstructiblePullbackSquareComparison_flip (sq : CommSq g' f' f g) :
    boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq.flip =
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq).symm := by
  ext K
  rw [boundedConstructiblePullbackSquareComparison_hom_app, Iso.symm_hom,
    boundedConstructiblePullbackSquareComparison_inv_app]

/-- **The projection formula of an open immersion is compatible with base change**: for a
cartesian square with `f` and `f'` open immersions, the projection morphisms are the inverses of
the projection comparisons of `f_! ⊣ Lf^*` and `f'_! ⊣ Lf'^*`
(`boundedConstructibleExceptionalProjectionMorphism_comp_projectionComparison`) and `Ex_!` is
the inverse of the base change of extension by zero
(`boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion`), the exchange
morphism of the pullback comparison; this is
`CategoryTheory.ProjectionBaseChange.pfBaseChange_of_projectionComparison`. -/
theorem pfBaseChange_boundedConstructibleExceptionalProjection_of_isOpenImmersion
    (sq : IsPullback g' f' f g) [IsOpenImmersion f.left] [IsOpenImmersion f'.left] :
    ProjectionBaseChange.PFBaseChange
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        sq.toCommSq)
      (boundedConstructibleExceptionalProjection ℓ f)
      (boundedConstructibleExceptionalProjection ℓ f') := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  refine ProjectionBaseChange.pfBaseChange_of_projectionComparison
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ f)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ f')
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f') _ _ _ _ _ _
    (fun A B ↦ boundedConstructibleExceptionalProjectionMorphism_comp_projectionComparison ℓ f A B)
    (fun A B ↦ boundedConstructibleExceptionalProjectionMorphism_comp_projectionComparison ℓ f' A B)
    (fun K ↦ ?_) ?_
  · rw [← boundedConstructiblePullbackSquareComparison_flip,
      ← boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft]
    exact boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion ℓ sq K
  · exact fun A B ↦ boundedConstructiblePullbackSquareComparison_hom_app_δ ℓ sq.toCommSq A B

section Paste

variable {Z Z' : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]

/-- The composition isomorphism along the trivial factorisation `i ≫ p = i ≫ p`. -/
lemma boundedConstructibleUpperStarCompOfEq_rfl {i : X ⟶ Z} {p : Z ⟶ Y} (hf : i ≫ p = i ≫ p) :
    boundedConstructibleUpperStarCompOfEq ℓ hf =
      boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i p := by
  simp [boundedConstructibleUpperStarCompOfEq]

/-- The projection formula along a factorisation `i ≫ p = f`
(`boundedConstructibleExceptionalProjectionMorphism_comp_of_eq`), stated with the projection of
the monoidal category instance as tensor structure. -/
lemma boundedConstructibleExceptionalProjectionMorphism_comp_of_eq' {i : X ⟶ Z} {p : Z ⟶ Y}
    (hf : i ≫ p = f) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ f K B ≫
        (boundedConstructibleLowerShriekCompOfEq ℓ hf).hom.app
          (K ⊗ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj B) ≫
        (boundedConstructibleLowerShriek ℓ p).map
          ((boundedConstructibleLowerShriek ℓ i).map
          (K ◁ (boundedConstructibleUpperStarCompOfEq ℓ hf).hom.app B)) =
      (boundedConstructibleLowerShriekCompOfEq ℓ hf).hom.app K ▷ B ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ p
          ((boundedConstructibleLowerShriek ℓ i).obj K) B ≫
        (boundedConstructibleLowerShriek ℓ p).map
          (boundedConstructibleExceptionalProjectionMorphism ℓ i K
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj B)) := by
  subst hf
  simpa [boundedConstructibleLowerShriekCompOfEq, boundedConstructibleUpperStarCompOfEq] using
    boundedConstructibleExceptionalProjectionMorphism_comp ℓ i p K B

/-- The diagram chase behind `boundedConstructiblePullbackSquareComparison_inv_app_paste_vert`,
in an arbitrary category: a composite `x₁ ≫ c₂⁻¹ ≫ e₁ ≫ c₃ ≫ m₁ ≫ m₂ ≫ m₃ ≫ c₄⁻¹` is computed by
successive rewritings. -/
lemma comp_eq_of_paste_aux {𝒟 : Type*} [Category 𝒟] {P₀ P₁ P₂ P₃ Q₁ Q₂ Q₃ Q₄ Q₆ Q₇ R₁ R₂ R₃
    R₄ R₅ R₆ : 𝒟} {a : P₀ ⟶ P₁} {e₀ : P₁ ⟶ P₂} {b : P₂ ⟶ P₃} {x₁ : P₀ ⟶ Q₁} {c₂' : Q₁ ⟶ Q₂}
    {e₁ : Q₂ ⟶ Q₃} {c₃ : Q₃ ⟶ Q₄} {m₁ : Q₄ ⟶ R₄} {m₂ : R₄ ⟶ Q₆} {m₃ : Q₆ ⟶ Q₇} {c₄' : Q₇ ⟶ P₃}
    {e₃ : P₁ ⟶ R₁} {cL : R₁ ⟶ Q₂} {c₂ : Q₂ ⟶ Q₁} {e₆ : R₁ ⟶ R₂} {cL' : R₂ ⟶ Q₃}
    {e₄ : R₂ ⟶ R₃} {cM : R₃ ⟶ R₄} {n₁ : R₄ ⟶ Q₄} {e₇ : R₃ ⟶ R₅} {cN : R₅ ⟶ Q₆}
    {e₅ : R₅ ⟶ R₆} {b' : R₆ ⟶ P₃}
    (hx₁ : x₁ = a ≫ e₃ ≫ cL ≫ c₂) (hc₂ : c₂ ≫ c₂' = 𝟙 _) (hL : cL ≫ e₁ = e₆ ≫ cL')
    (h₂ : cL' ≫ c₃ = e₄ ≫ cM ≫ n₁) (hn : n₁ ≫ m₁ = 𝟙 _) (hR : cM ≫ m₂ = e₇ ≫ cN)
    (h₃ : cN ≫ m₃ ≫ c₄' = e₅ ≫ b') (he : e₃ ≫ e₆ ≫ e₄ ≫ e₇ ≫ e₅ ≫ b' = e₀ ≫ b) :
    a ≫ e₀ ≫ b = x₁ ≫ c₂' ≫ e₁ ≫ c₃ ≫ m₁ ≫ m₂ ≫ m₃ ≫ c₄' := by
  rw [hx₁, ← he]
  simp only [Category.assoc]
  rw [reassoc_of% hc₂, reassoc_of% hL, reassoc_of% h₂, reassoc_of% hn, reassoc_of% hR, h₃]

/-- **Vertical pasting of pullback comparisons**: for commutative squares `g' ≫ i = i' ≫ gZ` and
`gZ ≫ p = p' ≫ g` with `i ≫ p = f` and `i' ≫ p' = f'`, the inverse of the pullback comparison
`Lf'^* Lg^* ≅ Lg'^* Lf^*` of the outer square is the composite of those of the two squares,
through `Lf^* ≅ Li^* Lp^*` and `Lf'^* ≅ Li'^* Lp'^*`. -/
lemma boundedConstructiblePullbackSquareComparison_inv_app_paste_vert {i : X ⟶ Z} {p : Z ⟶ Y}
    {i' : X' ⟶ Z'} {p' : Z' ⟶ Y'} {gZ : Z' ⟶ Z} (sq : CommSq g' f' f g)
    (s₁ : CommSq g' i' i gZ) (s₂ : CommSq gZ p' p g) (hf : i ≫ p = f) (hf' : i' ≫ p' = f')
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq).inv.app
        B =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
          ((boundedConstructibleUpperStarCompOfEq ℓ hf).hom.app B) ≫
        (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
          s₁).inv.app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj B) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i').map
          ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
            s₂).inv.app B) ≫
        (boundedConstructibleUpperStarCompOfEq ℓ hf').inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj B) := by
  subst hf hf'
  have A₁ := boundedConstructibleUpperStarComp_assoc_app (Profinite.padicAlgClRingObj ℓ) ℓ g' i p B
  have A₂ := boundedConstructibleUpperStarComp_assoc_app (Profinite.padicAlgClRingObj ℓ) ℓ i' gZ p B
  have A₃ := boundedConstructibleUpperStarComp_assoc_app (Profinite.padicAlgClRingObj ℓ) ℓ i' p' g B
  have hL {a a' : X' ⟶ Z} (e : a = a') :
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a p).hom.app B ≫
        eqToHom (congrArg (fun a ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
          ℓ a).obj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj B))
          e) =
      eqToHom (by rw [e]) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a' p).hom.app B := by
    subst e
    simp
  have hR {r r' : Z' ⟶ Y} (e : r = r') :
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i' r).hom.app B ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i').map
          (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar
            (Profinite.padicAlgClRingObj ℓ) ℓ r).obj B) e)) =
      eqToHom (by rw [e]) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i' r').hom.app B := by
    subst e
    simp
  have e₁ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i p).hom.app B) =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g' (i ≫ p)).inv.app B ≫
        eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (g' ≫ i) p).hom.app B ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g' i).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj B) := by
    rw [A₁]
    simp
  have e₃ : (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i'
        (p' ≫ g)).hom.app B ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i').map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p' g).hom.app B) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i' p').inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj B) =
      eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (i' ≫ p') g).hom.app
          B := by
    rw [← cancel_mono
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i' p').hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj B))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [A₃]
    simp
  rw [boundedConstructiblePullbackSquareComparison_inv_app,
    boundedConstructiblePullbackSquareComparison_inv_app,
    boundedConstructiblePullbackSquareComparison_inv_app]
  rw [boundedConstructibleUpperStarCompOfEq_rfl, boundedConstructibleUpperStarCompOfEq_rfl]
  simp only [Functor.map_comp, Category.assoc]
  refine comp_eq_of_paste_aux e₁ (Iso.hom_inv_id_app _ _) (hL s₁.w) A₂
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i').mapIso
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ gZ p).app B)).hom_inv_id
    (hR s₂.w) e₃ ?_
  simp only [eqToHom_trans_assoc]


/-- **The projection formula is compatible with base change, by factorisation**: for a cartesian
square `g' ≫ f = f' ≫ g` and factorisations `f = i ≫ p`, `f' = i' ≫ p'` into open immersions
followed by proper maps, through cartesian squares `g' ≫ i = i' ≫ gZ` and `gZ ≫ p = p' ≫ g`, the
compatibility for `f` follows from those for `i` and `p`
(`CategoryTheory.ProjectionBaseChange.pfBaseChange_comp`): the projection formula is compatible
with composition (`boundedConstructibleExceptionalProjectionMorphism_comp_of_eq`), and so are
compact-support base change
(`boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert_of_eq`) and the pullback
comparisons (`boundedConstructiblePullbackSquareComparison_inv_app_paste_vert`). -/
theorem pfBaseChange_boundedConstructibleExceptionalProjection_of_factorisation
    {Z Z' : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    {i : X ⟶ Z} {p : Z ⟶ Y} {i' : X' ⟶ Z'} {p' : Z' ⟶ Y'} {gZ : Z' ⟶ Z}
    (sq : IsPullback g' f' f g) (s₁ : IsPullback g' i' i gZ) (s₂ : IsPullback gZ p' p g)
    [IsOpenImmersion i.left] [IsOpenImmersion i'.left] [IsProper p.left] [IsProper p'.left]
    (hf : i ≫ p = f) (hf' : i' ≫ p' = f') :
    ProjectionBaseChange.PFBaseChange
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        sq.toCommSq)
      (boundedConstructibleExceptionalProjection ℓ f)
      (boundedConstructibleExceptionalProjection ℓ f') := by
  -- Eliminate the equality transports before comparing the composition laws.
  subst hf hf'
  refine ProjectionBaseChange.pfBaseChange_comp
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ gZ)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s₂)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s₁)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ s₂.toCommSq)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ s₁.toCommSq)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq)
    (boundedConstructibleExceptionalProjection ℓ p)
    (boundedConstructibleExceptionalProjection ℓ i)
    (boundedConstructibleExceptionalProjection ℓ (i ≫ p))
    (boundedConstructibleExceptionalProjection ℓ p')
    (boundedConstructibleExceptionalProjection ℓ i')
    (boundedConstructibleExceptionalProjection ℓ (i' ≫ p'))
    (boundedConstructibleLowerShriekCompOfEq ℓ (rfl : i ≫ p = i ≫ p))
    (boundedConstructibleLowerShriekCompOfEq ℓ (rfl : i' ≫ p' = i' ≫ p'))
    (boundedConstructibleUpperStarCompOfEq ℓ (rfl : i ≫ p = i ≫ p))
    (boundedConstructibleUpperStarCompOfEq ℓ (rfl : i' ≫ p' = i' ≫ p'))
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro K B
    exact boundedConstructibleExceptionalProjectionMorphism_comp_of_eq' ℓ
      (rfl : i ≫ p = i ≫ p) K B
  · intro K B
    exact boundedConstructibleExceptionalProjectionMorphism_comp_of_eq' ℓ
      (rfl : i' ≫ p' = i' ≫ p') K B
  · exact fun M ↦ boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert_of_eq ℓ sq s₁ s₂
      rfl rfl M
  · exact fun B ↦ boundedConstructiblePullbackSquareComparison_inv_app_paste_vert ℓ sq.toCommSq
      s₁.toCommSq s₂.toCommSq rfl rfl B
  · exact boundedConstructibleExceptionalProjectionMorphism_baseChange ℓ s₂
  · exact pfBaseChange_boundedConstructibleExceptionalProjection_of_isOpenImmersion ℓ s₁

end Paste

/-- **The projection formula is compatible with base change** (blueprint
`proposition-composition-base-change-rf-shriek--1`, section `chap-The-six-operations-on-Dbctf`, the
clause "it is compatible with base change: for a Cartesian square `(f', g', f, g)` [...] the square
[...] commutes"; SGA 4, Exposé XVII, §5.2): for a cartesian square, the exceptional projection
morphisms of `f` and `f'` are compatible with compact-support base change `Ex_!` and the pullback
comparison `Lf'^* Lg^* ≅ Lg'^* Lf^*`. -/
theorem pfBaseChange_boundedConstructibleExceptionalProjection (sq : IsPullback g' f' f g) :
    ProjectionBaseChange.PFBaseChange (boundedConstructibleUpperStar _ ℓ g)
      (boundedConstructibleUpperStar _ ℓ g')
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
      (boundedConstructiblePullbackSquareComparison _ ℓ sq.toCommSq)
      (boundedConstructibleExceptionalProjection ℓ f)
      (boundedConstructibleExceptionalProjection ℓ f') :=
  pfBaseChange_boundedConstructibleExceptionalProjection_of_factorisation ℓ sq
    ((compactificationOverField f).overBaseChange_isPullback_i sq)
    ((compactificationOverField f).overBaseChange_isPullback_g sq)
    (compactificationOverField f).overI_overG
    ((compactificationOverField f).ofIsPullback sq.overLeft).overI_overG

end AlgebraicGeometry.ProEtale.CondensedRing
