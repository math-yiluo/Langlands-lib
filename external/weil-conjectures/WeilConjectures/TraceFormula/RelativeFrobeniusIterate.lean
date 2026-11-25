/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.RelativeFrobenius
public import WeilConjectures.TraceFormula.RelativeFrobeniusComparison

/-!

# The relative Frobenius comparison in degree `m`

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type and `Φ_X`, `Φ_Y` finite
universal homeomorphisms with `Φ_X ≫ f = f ≫ Φ_Y`, for instance the model Frobenii of a morphism
of models over a finite field. For every `m` put `X'_m = Y ×_{Φ_Y^m, Y, f} X`, with projections
`f'_m : X'_m ⟶ Y`, `p_m : X'_m ⟶ X`, and let `r_m = (f, Φ_X^m) : X ⟶ X'_m` be the relative
Frobenius (`AlgebraicGeometry.relativeFrobenius`), a finite universal homeomorphism with
`p_m r_m = Φ_X^m` and `f'_m r_m = f` (blueprint `lemma-comparison-via-relative-frobenius--text-1`).
This file proves blueprint lemma `lemma-comparison-via-relative-frobenius`:

1. The Frobenius comparison in degree `m`
   (`ProEtale.CondensedRing.lowerShriekFrobeniusComparison`)
   ```
   θ_{f,m} : Φ_Y^{m*} Rf_! ≅ Rf'_{m!} p_m^* ≅ Rf'_{m!} Rr_{m*} r_m^* p_m^* ≅ Rf_! Φ_X^{m*}
   ```
   is compatible with iteration in `m`
   (`ProEtale.CondensedRing.lowerShriekFrobeniusComparison_add`).
2. For a Frobenius coefficient morphism `ψ : Φ_X^* K ⟶ K` the pushforward
   `ψ' = Rf_! ψ ∘ θ_{f,1}` on `L = Rf_! K` has iterates `ψ'_m = Rf_! ψ_m ∘ θ_{f,m}`
   (`ProEtale.CondensedRing.frobeniusCoefficientIterate_lowerShriekFrobeniusCoefficient`).
3. The composition isomorphism `RΓ_c(Y, L) ≅ RΓ_c(X, K)` intertwines the global operators
   `F_{c,m}(ψ')` and `F_{c,m}(ψ)`
   (`ProEtale.CondensedRing.frobeniusCompactOperator_lowerShriekFrobeniusCoefficient`).
4. At a point `y` fixed by `Φ_Y^m`, proper base change identifies the stalk map of `ψ'_m` with the
   degree-one global operator of the restriction of `ψ_m` to the fibre
   (`ProEtale.CondensedRing.stalk_lowerShriekFrobeniusCoefficient_iterate`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) [IsFinite ΦX.left] [IsUniversalHomeomorphism ΦX.left]
  [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left] {f : X ⟶ Y} (hf : ΦX ≫ f = f ≫ ΦY)

/-! ### The comparison in degree `m` -/

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [IsFinite ΦY.left]
  [IsUniversalHomeomorphism ΦY.left] in
/-- The cartesian square `p_m ≫ f = f'_m ≫ Φ_Y^m` defining `X'_m = Y ×_{Φ_Y^m, Y, f} X`
(blueprint `lemma-comparison-via-relative-frobenius--text-1`). -/
lemma isPullback_frobeniusIterate (m : ℕ) :
    IsPullback (pullback.snd (frobeniusIterate ΦY m) f) (pullback.fst (frobeniusIterate ΦY m) f)
      f (frobeniusIterate ΦY m) :=
  (IsPullback.of_hasPullback _ _).flip

/-- **The Frobenius comparison in degree `m`** (blueprint `lemma-comparison-via-relative-frobenius`
(1), `lemma-comparison-via-relative-frobenius` (1)): the natural isomorphism
```
θ_{f,m} : LΦ_Y^{m*} Rf_! ≅ Rf'_{m!} Lp_m^* ≅ Rf'_{m!} Rr_{m*} Lr_m^* Lp_m^* ≅ Rf_! LΦ_X^{m*}
```
of compact-support base change for `X'_m = Y ×_{Φ_Y^m, Y, f} X`, the unit of `Lr_m^* ⊣ Rr_{m*}`
(invertible by topological invariance, `r_m` being a finite universal homeomorphism), the
identification `Rr_{m*} ≅ Rr_{m!}` and the composition isomorphisms. -/
noncomputable def lowerShriekFrobeniusComparison (m : ℕ) :
    boundedConstructibleLowerShriek ℓ f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (frobeniusIterate ΦY m) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (frobeniusIterate ΦX m) ⋙
        boundedConstructibleLowerShriek ℓ f :=
  weilLowerShriekFrobeniusComparison ℓ (frobeniusIterate ΦX m) (frobeniusIterate ΦY m) f
    (isPullback_frobeniusIterate ΦY m)
    (relativeFrobenius f (frobeniusIterate ΦX m) (frobeniusIterate ΦY m)
      (frobeniusIterate_comp_of_comp hf m))
    (relativeFrobenius_snd ..) (relativeFrobenius_fst ..)

/-- **Compatibility of the Frobenius comparisons with iteration** (blueprint
`lemma-comparison-via-relative-frobenius` (1), `lemma-comparison-via-relative-frobenius--2` (1)):
after the composition isomorphisms `LΦ^{(m+n)*} ≅ LΦ^{n*} LΦ^{m*}` on `X` and on `Y`,
`θ_{f,m+n} = θ_{f,n}(LΦ_X^{m*} -) ∘ LΦ_Y^{n*} θ_{f,m}`. -/
theorem lowerShriekFrobeniusComparison_add (m n : ℕ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerShriekFrobeniusComparison ℓ ΦX ΦY hf (m + n)).hom.app K =
      eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
          ℓ g).obj ((boundedConstructibleLowerShriek ℓ f).obj K))
          (frobeniusIterate_add ΦY m n)) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate ΦY n) (frobeniusIterate ΦY m)).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate ΦY n)).map
          ((lowerShriekFrobeniusComparison ℓ ΦX ΦY hf m).hom.app K) ≫
        (lowerShriekFrobeniusComparison ℓ ΦX ΦY hf n).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (frobeniusIterate ΦX m)).obj K) ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
            (frobeniusIterate ΦX n) (frobeniusIterate ΦX m)).inv.app K ≫
            eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar
              (Profinite.padicAlgClRingObj ℓ) ℓ g).obj K) (frobeniusIterate_add ΦX m n).symm)) :=
  weilLowerShriekFrobeniusComparison_comp ℓ _ _ _ _ _ _ f _ _ _ _ _ _ _ _ _ _ _ _
    (frobeniusIterate_add ΦX m n).symm (frobeniusIterate_add ΦY m n).symm K



/-- The recursive description of the iterates of a Frobenius coefficient morphism. -/
lemma frobeniusCoefficientIterate_succ {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] {Φ : Z ⟶ Z}
    {K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (m : ℕ) :
    frobeniusCoefficientIterate ψ (m + 1) =
      eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
          ℓ g).obj K) (frobeniusIterate_succ Φ m)) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Φ
          (frobeniusIterate Φ m)).hom.app K ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
          (frobeniusCoefficientIterate ψ m) ≫ ψ :=
  rfl
/-! ### Iterates of the pushforward of a Frobenius coefficient morphism -/

/-- The diagram chase of the induction step for the iterates of the pushforward of a Frobenius
coefficient morphism, for opaque morphisms and functors. -/
private lemma frobeniusCoefficient_iterate_aux {D E : Type*}
    [Category D] [Category E]
    (F : D ⥤ E) (G : E ⥤ E) (H : D ⥤ D) {o₀ o₁ o₂ : E} {d₀ d₁ d₃ d₄ : D}
    (e : o₀ ⟶ o₁) (c : o₁ ⟶ G.obj o₂) (θm : o₂ ⟶ F.obj d₀) (ψm : d₀ ⟶ d₁)
    (θK : G.obj (F.obj d₁) ⟶ F.obj (H.obj d₁)) (ψ : H.obj d₁ ⟶ d₁)
    (θ'' : G.obj (F.obj d₀) ⟶ F.obj (H.obj d₀)) (cinv : H.obj d₀ ⟶ d₃) (e₂ : d₃ ⟶ d₄)
    (e₃ : d₄ ⟶ d₃) (chom : d₃ ⟶ H.obj d₀) (h₁ : e₂ ≫ e₃ = 𝟙 _) (h₂ : cinv ≫ chom = 𝟙 _)
    (N : G.map (F.map ψm) ≫ θK = θ'' ≫ F.map (H.map ψm)) {ψ'm : o₂ ⟶ F.obj d₁}
    (hih : ψ'm = θm ≫ F.map ψm) :
    e ≫ c ≫ G.map ψ'm ≫ θK ≫ F.map ψ =
      (e ≫ c ≫ G.map θm ≫ θ'' ≫ F.map (cinv ≫ e₂)) ≫ F.map (e₃ ≫ chom ≫ H.map ψm ≫ ψ) := by
  rw [hih, G.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% N, ← F.map_comp, ← F.map_comp]
  simp only [Category.assoc, reassoc_of% h₁, reassoc_of% h₂]

/-- The *pushforward* `ψ' = Rf_! ψ ∘ θ_{f,1} : LΦ_Y^* Rf_! K ⟶ Rf_! K` of a Frobenius
coefficient morphism `ψ : LΦ_X^* K ⟶ K` along `f` (blueprint
`lemma-comparison-via-relative-frobenius` (2), `lemma-comparison-via-relative-frobenius` (2)). For
the structure isomorphism of a Weil object it is the structure of the lower shriek of Weil objects
`ProEtale.CondensedRing.weilLowerShriekOfFrobenius`.
-/
noncomputable def lowerShriekFrobeniusCoefficient
    {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K ⟶ K) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦY).obj
        ((boundedConstructibleLowerShriek ℓ f).obj K) ⟶
      (boundedConstructibleLowerShriek ℓ f).obj K :=
  (weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f (IsPullback.of_hasPullback ΦY f).flip
      (relativeFrobenius f ΦX ΦY hf) (relativeFrobenius_snd ..) (relativeFrobenius_fst ..)).hom.app
      K ≫
    (boundedConstructibleLowerShriek ℓ f).map ψ

/-- The Frobenius comparisons for equal endomorphisms agree up to the casts. -/
lemma weilLowerShriekFrobeniusComparison_hom_app_congr {aX aX' : X ⟶ X} {aY aY' : Y ⟶ Y}
    (eX : aX = aX') (eY : aY = aY') (h : aX ≫ f = f ≫ aY) (h' : aX' ≫ f = f ≫ aY')
    [IsFinite aX.left] [IsUniversalHomeomorphism aX.left] [IsFinite aY.left]
    [IsUniversalHomeomorphism aY.left] [IsFinite aX'.left] [IsUniversalHomeomorphism aX'.left]
    [IsFinite aY'.left] [IsUniversalHomeomorphism aY'.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilLowerShriekFrobeniusComparison ℓ aX aY f (IsPullback.of_hasPullback aY f).flip
        (relativeFrobenius f aX aY h) (relativeFrobenius_snd ..) (relativeFrobenius_fst ..)).hom.app
        K =
      eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
          ℓ g).obj ((boundedConstructibleLowerShriek ℓ f).obj K))
          eY) ≫
        (weilLowerShriekFrobeniusComparison ℓ aX' aY' f (IsPullback.of_hasPullback aY' f).flip
          (relativeFrobenius f aX' aY' h') (relativeFrobenius_snd ..)
          (relativeFrobenius_fst ..)).hom.app K ≫
        (boundedConstructibleLowerShriek ℓ f).map
          (eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar
            (Profinite.padicAlgClRingObj ℓ) ℓ g).obj K) eX.symm)) := by
  subst eX eY
  simp

-- the instances of the categories of sheaves make the unification slow
/-- **The iterates of the pushforward** (blueprint `lemma-comparison-via-relative-frobenius` (2),
`lemma-comparison-via-relative-frobenius--2` (2)): for a Frobenius coefficient morphism
`ψ : LΦ_X^* K ⟶ K` (not necessarily invertible) and `m ≥ 1`, the iterates of its pushforward
`ψ' = Rf_! ψ ∘ θ_{f,1}` are `ψ'_m = Rf_! ψ_m ∘ θ_{f,m}`. -/
theorem frobeniusCoefficientIterate_lowerShriekFrobeniusCoefficient
    {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K ⟶ K)
    {m : ℕ} (hm : 1 ≤ m) :
    frobeniusCoefficientIterate (lowerShriekFrobeniusCoefficient ℓ ΦX ΦY hf ψ) m =
      (lowerShriekFrobeniusComparison ℓ ΦX ΦY hf m).hom.app K ≫
        (boundedConstructibleLowerShriek ℓ f).map
          (frobeniusCoefficientIterate ψ m) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [frobeniusCoefficientIterate_one, frobeniusCoefficientIterate_one,
      lowerShriekFrobeniusComparison, weilLowerShriekFrobeniusComparison_hom_app_congr ℓ
        (frobeniusIterate_one ΦX) (frobeniusIterate_one ΦY) _ hf K,
      lowerShriekFrobeniusCoefficient]
    simp only [Category.assoc, ← Functor.map_comp, eqToHom_refl,
      Category.id_comp]
  | succ m hm ih =>
    have h := weilLowerShriekFrobeniusComparison_comp ℓ ΦX (frobeniusIterate ΦX m)
      (frobeniusIterate ΦX (m + 1)) ΦY (frobeniusIterate ΦY m) (frobeniusIterate ΦY (m + 1)) f
      (IsPullback.of_hasPullback ΦY f).flip (relativeFrobenius f ΦX ΦY hf)
      (relativeFrobenius_snd ..) (relativeFrobenius_fst ..) (isPullback_frobeniusIterate ΦY m)
      (relativeFrobenius f _ _ (frobeniusIterate_comp_of_comp hf m)) (relativeFrobenius_snd ..)
      (relativeFrobenius_fst ..) (isPullback_frobeniusIterate ΦY (m + 1))
      (relativeFrobenius f _ _ (frobeniusIterate_comp_of_comp hf (m + 1)))
      (relativeFrobenius_snd ..) (relativeFrobenius_fst ..) (frobeniusIterate_succ ΦX m).symm
      (frobeniusIterate_succ ΦY m).symm K
    rw [lowerShriekFrobeniusComparison] at ih ⊢
    rw [h]
    rw [frobeniusCoefficientIterate_succ ℓ (lowerShriekFrobeniusCoefficient ℓ ΦX ΦY hf ψ) m,
      frobeniusCoefficientIterate_succ ℓ ψ m,
      lowerShriekFrobeniusCoefficient]
    refine frobeniusCoefficient_iterate_aux
      (boundedConstructibleLowerShriek ℓ f)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦY)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX) _ _ _
      (frobeniusCoefficientIterate ψ m) _ ψ _ _ _ _ _ ?_ ?_ ?_ ?_
    · rw [eqToHom_trans, eqToHom_refl]
    · exact Iso.inv_hom_id_app _ _
    · have hn := (weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f (IsPullback.of_hasPullback ΦY f).flip
        (relativeFrobenius f ΦX ΦY hf) (relativeFrobenius_snd ..)
        (relativeFrobenius_fst ..)).hom.naturality (frobeniusCoefficientIterate ψ m)
      simp only [Functor.comp_map] at hn
      convert hn using 3
    · rw [lowerShriekFrobeniusCoefficient] at ih
      convert ih using 3


/-! ### The global operators -/

/-- **The global operators of the pushforward** (blueprint `lemma-comparison-via-relative-frobenius`
(3), `lemma-comparison-via-relative-frobenius--4` (1)): the composition isomorphism
`c_f : RΓ_c(Y, Rf_! K) ≅ RΓ_c(X, K)` intertwines the global operators `F_{c,m}(ψ')` of the
pushforward `ψ' = Rf_! ψ ∘ θ_{f,1}` and `F_{c,m}(ψ)` of the Frobenius coefficient morphism `ψ`,
for every `m`. -/
theorem frobeniusCompactOperator_lowerShriekFrobeniusCoefficient
    {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K ⟶ K)
    (m : ℕ) :
    frobeniusCompactOperator ℓ (lowerShriekFrobeniusCoefficient ℓ ΦX ΦY hf ψ) m ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app K =
      (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app K ≫
        frobeniusCompactOperator ℓ ψ m := by
  have h₁ : frobeniusCompactOperator ℓ (lowerShriekFrobeniusCoefficient ℓ ΦX ΦY hf ψ) 1 ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app K =
      (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app K ≫
        frobeniusCompactOperator ℓ ψ 1 := by
    have hn := (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.naturality ψ
    simp only [Functor.comp_map] at hn
    rw [frobeniusCompactOperator_one, frobeniusCompactOperator_one,
      lowerShriekFrobeniusCoefficient, Functor.map_comp, Category.assoc, Category.assoc, hn]
    exact compactPullback_comp_weilLowerShriekFrobeniusComparison_assoc ℓ _ _ _ K _
  rw [frobeniusCompactOperator_eq_pow ℓ (lowerShriekFrobeniusCoefficient ℓ ΦX ΦY hf ψ) m,
    frobeniusCompactOperator_eq_pow ℓ ψ m]
  exact End.asHom_pow_comp_eq_comp_asHom_pow h₁ m

/-! ### The stalks at fixed points -/

section Stalk

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

-- the defeq of the carriers of the lower shriek with `Rf_! K` is slow
omit [IsFinite ΦX.left] [IsUniversalHomeomorphism ΦX.left] [IsFinite ΦY.left]
  [IsUniversalHomeomorphism ΦY.left] in
/-- The stalk of the pushforward of a Frobenius coefficient morphism at a fixed point, for an
arbitrary cartesian square and relative Frobenius (blueprint
`lemma-comparison-via-relative-frobenius--4` (2)): for `y` fixed by `Φ_Y` with fibre `Z = X ×_Y y`
carrying a Frobenius `Φ_Z` compatible with `Φ_X`, proper base change
`β : (Rf_! K)_ȳ ≅ RΓ_c(Z, K|_Z)` carries the stalk map of `Rf_! v ∘ θ_f` to the degree-one global
operator of the restriction `v|_Z` of `v`. -/
lemma stalk_weilLowerShriekFrobeniusComparison_comp {X' : Over (Spec (.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] {ΦX ΦY}
    {p : X' ⟶ X} {f' : X' ⟶ Y} (sq : IsPullback p f' f ΦY) (r : X ⟶ X') (hrp : r ≫ p = ΦX)
    (hrf : r ≫ f' = f) [IsFinite r.left] [IsUniversalHomeomorphism r.left] {ΦZ : Z ⟶ Z}
    [IsProper ΦZ.left] {i : Z ⟶ X} (hi : ΦZ ≫ i = i ≫ ΦX) {y : RationalPoint Y}
    (hy : y ≫ ΦY = y) (hZ : IsPullback i (toPoint Z) f y)
    {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K ⟶ K) :
    (eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ g).obj ((boundedConstructibleLowerShriek ℓ f).obj K))
        hy.symm) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ y ΦY).hom.app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        ((weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f sq r hrp hrf).hom.app K ≫
          (boundedConstructibleLowerShriek ℓ f).map v)) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app K =
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app K ≫
      frobeniusCompactOperator ℓ (Φ := ΦZ)
        (K := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)
        ((weilUpperStarComparison ℓ ΦZ ΦX i hi).hom.app K ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map v) 1 := by
  obtain ⟨j, hj₁, hj₂⟩ : ∃ j : Z ⟶ X', j ≫ p = i ∧ j ≫ f' = toPoint Z ≫ y :=
    ⟨sq.lift i (toPoint Z ≫ y) (by rw [hZ.w, Category.assoc, hy]), sq.lift_fst _ _ _,
      sq.lift_snd _ _ _⟩
  subst hj₁ hrp hrf
  have hL : IsPullback j (toPoint Z) f' y := IsPullback.of_right (by rw [hy]; exact hZ) hj₂ sq
  have hTw : (j ≫ p) ≫ r = ΦZ ≫ j := sq.hom_ext
    (by simp only [Category.assoc] at hi ⊢; exact hi.symm)
    (by rw [Category.assoc, hZ.w, Category.assoc, hj₂, ← Category.assoc, comp_toPoint])
  have hT : IsPullback (j ≫ p) ΦZ r j :=
    IsPullback.of_bot (by rw [comp_toPoint]; exact hZ) hTw hL
  have hn := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).naturality v
  simp only [Functor.comp_map] at hn
  rw [frobeniusCompactOperator_one, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hn]
  exact baseChange_comp_weilLowerShriekFrobeniusComparison_stalk_assoc ℓ sq hy hZ hL hT hi K _

/-- **The stalks of the pushforward at fixed points** (blueprint
`lemma-comparison-via-relative-frobenius` (4), `lemma-comparison-via-relative-frobenius--4` (2)):
let `m ≥ 1`, let `y` be a rational point of `Y` fixed by `Φ_Y^m`, and let `Z = X ×_Y y` be its
fibre, with `i : Z ⟶ X`, carrying the restriction `Φ_Z` of `Φ_X^m` (for model Frobenii, `Z` is the
base change of a scheme over `𝔽_{q^m}` with `Φ_Z` its `q^m`-power Frobenius:
`ProEtale.CondensedRing.IsModelFrobenius.isModelFrobenius_fibreFrobenius`). Then proper base
change `β : (Rf_! K)_ȳ ≅ RΓ_c(Z, K|_Z)` identifies the stalk map of the iterate `ψ'_m` of the
pushforward with the degree-one global operator `F_{c,1}(ψ_m|_Z)` of the restriction of `ψ_m`. -/
theorem stalk_lowerShriekFrobeniusCoefficient_iterate
    {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K ⟶ K)
    {m : ℕ} (hm : 1 ≤ m) {ΦZ : Z ⟶ Z} [IsProper ΦZ.left] {i : Z ⟶ X}
    (hi : ΦZ ≫ i = i ≫ frobeniusIterate ΦX m) {y : RationalPoint Y}
    (hy : y ≫ frobeniusIterate ΦY m = y) (hZ : IsPullback i (toPoint Z) f y) :
    (eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ g).obj ((boundedConstructibleLowerShriek ℓ f).obj K))
        hy.symm) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ y
        (frobeniusIterate ΦY m)).hom.app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        (frobeniusCoefficientIterate (lowerShriekFrobeniusCoefficient ℓ ΦX ΦY hf ψ) m)) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app K =
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app K ≫
      frobeniusCompactOperator ℓ (Φ := ΦZ)
        (K := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)
        ((weilUpperStarComparison ℓ ΦZ (frobeniusIterate ΦX m) i hi).hom.app K ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map
            (frobeniusCoefficientIterate ψ m)) 1 := by
  rw [frobeniusCoefficientIterate_lowerShriekFrobeniusCoefficient ℓ ΦX ΦY hf ψ hm,
    lowerShriekFrobeniusComparison]
  convert stalk_weilLowerShriekFrobeniusComparison_comp ℓ (isPullback_frobeniusIterate ΦY m)
    (relativeFrobenius f _ _ (frobeniusIterate_comp_of_comp hf m)) (relativeFrobenius_snd ..)
    (relativeFrobenius_fst ..) hi hy hZ _ using 3

end Stalk
end AlgebraicGeometry.ProEtale.CondensedRing
