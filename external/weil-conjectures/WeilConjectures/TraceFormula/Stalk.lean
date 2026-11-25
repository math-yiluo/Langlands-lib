/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.TraceFormula.Frobenius

/-!

# Stalks of Weil objects and the local Frobenius

Let `Φ : X ⟶ X` be an endomorphism of a scheme over `Spec k` and `x : s ⟶ X` a rational point
fixed by `Φ`, `x ≫ Φ = x`. The square
```
   s ──x──▶ X
   │𝟙       │Φ
   ▼        ▼
   s ──x──▶ X
```
commutes, so the derived pullback `Lx^*` of Weil objects
(`ProEtale.CondensedRing.weilUpperStar`) sends a Weil object `(K, φ)` for `Φ` to a Weil object
`(K_x̄, φ_x̄)` for the identity of the base point: the *stalk functor*
```
ProEtale.CondensedRing.weilStalk :
  WeilBoundedConstructible ℓ Φ ⥤ WeilBoundedConstructible ℓ (𝟙 s).
```
Its structure isomorphism is
```
L(𝟙 s)^* Lx^* K ≅ Lx^* LΦ^* K --Lx^* φ--> Lx^* K,
```
and the Frobenius `WeilBoundedConstructible.frobenius` of this Weil object for the identity is the
*local Frobenius* at `x`.

For a point `x` fixed by `Φ_m` the local Frobenius of the iterate `(K, φ_m)` is the operator
`F_{x,m} = (φ_m)_x̄` on the geometric stalk `K_x̄ = Lx^* K` of the trace formula
(`ProEtale.CondensedRing.WeilBoundedConstructible.stalkFrobenius`, blueprint
`definition-frobenius-correspondences-their-operators`).

The stalks at `x` and at its Frobenius translate `x ≫ Φ` are isomorphic Weil objects
(`ProEtale.CondensedRing.WeilBoundedConstructible.stalkTransport`), so their local Frobenii are
conjugate and have the same trace (blueprint `theorem-trace-formula-euler-product--1`); and at a
point fixed by `Φ_d` the operator `F_{x,dn}` is the `n`-th power of `F_{x,d}` (blueprint
`theorem-trace-formula-euler-product`).

## Main definitions

- `ProEtale.CondensedRing.weilStalk`: the stalk functor of Weil objects at a fixed point.
- `ProEtale.CondensedRing.WeilBoundedConstructible.iterateStalk`: the stalk `(K_x̄, (φ_m)_x̄)` of
  the iterate `(K, φ_m)` at a point fixed by `Φ_m`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.stalkFrobenius`: the local Frobenius
  `F_{x,m}` on `K_x̄`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.stalkTransport`: the isomorphism of Weil
  objects between the stalks at `x ≫ Φ` and at `x`.

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.stalkFrobenius_mul`: `F_{x,dn} = F_{x,d}ⁿ`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.trace_stalkFrobenius_comp`:
  `tr(F_{x ≫ Φ, m}) = tr(F_{x,m})`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### The stalk functor -/

section Stalk

variable (Φ : X ⟶ X)

/-- The *stalk functor* at a rational point `x` fixed by `Φ`: the derived pullback `Lx^*` of
Weil objects along the square `𝟙 s ≫ x = x ≫ Φ`, from Weil objects for `Φ` on `X` to Weil
objects for the identity of the base point `s`. -/
noncomputable def weilStalk (x : RationalPoint X) (hx : x ≫ Φ = x) :
    WeilBoundedConstructible ℓ Φ ⥤ WeilBoundedConstructible ℓ (𝟙 (point k)) :=
  weilUpperStar ℓ (𝟙 (point k)) Φ x (by rw [Category.id_comp, hx])

@[simp]
lemma weilStalk_obj_carrier (x : RationalPoint X) (hx : x ≫ Φ = x)
    (K : WeilBoundedConstructible ℓ Φ) :
    ((weilStalk ℓ Φ x hx).obj K).carrier =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier :=
  rfl

/-- The Frobenius of a stalk, with the stalk written as `Lx^* K`. -/
lemma weilStalk_obj_frobenius_hom (x : RationalPoint X) (hx : x ≫ Φ = x)
    (K : WeilBoundedConstructible ℓ Φ) :
    ((weilStalk ℓ Φ x hx).obj K).frobenius.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier) ≫
        ((weilStalk ℓ Φ x hx).obj K).str.hom :=
  WeilBoundedConstructible.frobenius_hom _

/-- The stalk functor lifts the derived pullback `Lx^*` along the forgetful functors. -/
lemma weilStalk_comp_forget (x : RationalPoint X) (hx : x ≫ Φ = x) :
    weilStalk ℓ Φ x hx ⋙ WeilBoundedConstructible.forget ℓ (𝟙 (point k)) =
      WeilBoundedConstructible.forget ℓ Φ ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x :=
  rfl

end Stalk

/-! ### The local Frobenius -/

namespace WeilBoundedConstructible

variable {ℓ} {Φ : X ⟶ X}

/-- The stalk `(K_x̄, (φ_m)_x̄)` at a rational point `x` fixed by `Φ_m` of the iterate `(K, φ_m)`
of a Weil object `(K, φ)`: a Weil object for the identity of the base point. -/
noncomputable def iterateStalk (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) : WeilBoundedConstructible ℓ (𝟙 (point k)) :=
  (weilStalk ℓ (frobeniusIterate Φ m) x hx).obj (K.iterate m)

/-- The *local Frobenius* `F_{x,m} = (φ_m)_x̄` of a Weil object `(K, φ)` at a rational point `x`
fixed by `Φ_m`: the Frobenius of the stalk at `x` of the iterate `(K, φ_m)`, an automorphism of
the geometric stalk `K_x̄ = Lx^* K`. Explicitly it is the composite
```
Lx^* K ≅ L(𝟙 s)^* Lx^* K ≅ Lx^* LΦ_m^* K --Lx^* φ_m--> Lx^* K
```
(blueprint `definition-frobenius-correspondences-their-operators`). -/
noncomputable def stalkFrobenius (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier :=
  eqToHom (congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      (K.iterate_carrier m).symm :
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier =
          (K.iterateStalk m x hx).carrier) ≫
    (K.iterateStalk m x hx).frobenius.hom ≫
    eqToHom (congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      (K.iterate_carrier m) :
        (K.iterateStalk m x hx).carrier =
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier)

/-- The local Frobenius is the Frobenius of the stalk of the iterate, read on `Lx^* K`. -/
lemma stalkFrobenius_eq_frobenius (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    K.stalkFrobenius m x hx = (K.iterateStalk m x hx).frobenius.hom := by
  rw [stalkFrobenius]
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The local Frobenius is invertible. -/
instance isIso_stalkFrobenius (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) : IsIso (K.stalkFrobenius m x hx) := by
  rw [stalkFrobenius_eq_frobenius]
  exact Iso.isIso_hom (K.iterateStalk m x hx).frobenius


omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The multiplicativity of the local Frobenii, for an abstract family of pullback functors: for
endomorphisms `P_a, P_b` fixing a point `x` and maps `φ_a : LP_a^* K ⟶ K`, `φ_b : LP_b^* K ⟶ K`,
the operator `Lx^* K ≅ L(x ≫ P)^* K ≅ Lx^* LP^* K ⟶ Lx^* K` of the composite
`φ_b ∘ LP_b^* φ_a` along `P_b ≫ P_a` is the composite of the operators of `φ_a` and `φ_b`. -/
lemma stalkFrobenius_add_aux {𝒞 : Type*} [Category 𝒞] {W X' : 𝒞} {DW DX : Type*}
    [Category DW] [Category DX] (UWX : (W ⟶ X') → DX ⥤ DW) (UXX : (X' ⟶ X') → DX ⥤ DX)
    (cWX : ∀ (a : W ⟶ X') (b : X' ⟶ X'), UWX (a ≫ b) ≅ UXX b ⋙ UWX a)
    (cXX : ∀ (a b : X' ⟶ X'), UXX (a ≫ b) ≅ UXX b ⋙ UXX a)
    (A : ∀ (a : W ⟶ X') (b c : X' ⟶ X') (K : DX),
      (cWX (a ≫ b) c).hom.app K ≫ (cWX a b).hom.app ((UXX c).obj K) =
        eqToHom (congrArg (fun f ↦ (UWX f).obj K) (Category.assoc a b c)) ≫
          (cWX a (b ≫ c)).hom.app K ≫ (UWX a).map ((cXX b c).hom.app K))
    {x : W ⟶ X'} {Pa Pb Pab : X' ⟶ X'} (hab : Pab = Pb ≫ Pa) (ha : x ≫ Pa = x)
    (hb : x ≫ Pb = x) (h : x ≫ Pab = x) {K : DX} (φa : (UXX Pa).obj K ⟶ K)
    (φb : (UXX Pb).obj K ⟶ K) (φab : (UXX Pab).obj K ⟶ K)
    (hφ : φab = eqToHom (congrArg (fun f ↦ (UXX f).obj K) hab) ≫ (cXX Pb Pa).hom.app K ≫
      (UXX Pb).map φa ≫ φb) :
    eqToHom (congrArg (fun f ↦ (UWX f).obj K) h.symm) ≫ (cWX x Pab).hom.app K ≫
        (UWX x).map φab =
      (eqToHom (congrArg (fun f ↦ (UWX f).obj K) ha.symm) ≫ (cWX x Pa).hom.app K ≫
        (UWX x).map φa) ≫
      eqToHom (congrArg (fun f ↦ (UWX f).obj K) hb.symm) ≫ (cWX x Pb).hom.app K ≫
        (UWX x).map φb := by
  subst hab hφ
  have hA : (cWX x (Pb ≫ Pa)).hom.app K ≫ (UWX x).map ((cXX Pb Pa).hom.app K) =
      eqToHom (congrArg (fun f ↦ (UWX f).obj K) (Category.assoc x Pb Pa)).symm ≫
        (cWX (x ≫ Pb) Pa).hom.app K ≫ (cWX x Pb).hom.app ((UXX Pa).obj K) := by
    rw [A, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hn := (cWX x Pb).hom.naturality φa
  simp only [Functor.comp_map] at hn
  have key (y : W ⟶ X') (hy : y = x)
      (e₁ : (UWX x).obj K = (UWX (y ≫ Pa)).obj K) :
      eqToHom e₁ ≫ (cWX y Pa).hom.app K ≫ (UWX y).map φa =
        eqToHom (congrArg (fun f ↦ (UWX f).obj K) ha.symm) ≫ (cWX x Pa).hom.app K ≫
          (UWX x).map φa ≫ eqToHom (congrArg (fun f ↦ (UWX f).obj K) hy.symm) := by
    subst hy
    simp
  simp only [eqToHom_refl, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hA, ← reassoc_of% hn, eqToHom_trans_assoc, reassoc_of% (key _ hb)]

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- `stalkFrobenius_add_aux` for maps defined on objects `K₁, K₂, K₃` equal to `K`, read on `K`
through `eqToHom`. -/
lemma stalkFrobenius_add_eqToHom_aux {𝒞 : Type*} [Category 𝒞] {W X' : 𝒞} {DW DX : Type*}
    [Category DW] [Category DX] (UWX : (W ⟶ X') → DX ⥤ DW) (UXX : (X' ⟶ X') → DX ⥤ DX)
    (cWX : ∀ (a : W ⟶ X') (b : X' ⟶ X'), UWX (a ≫ b) ≅ UXX b ⋙ UWX a)
    (cXX : ∀ (a b : X' ⟶ X'), UXX (a ≫ b) ≅ UXX b ⋙ UXX a)
    (A : ∀ (a : W ⟶ X') (b c : X' ⟶ X') (K : DX),
      (cWX (a ≫ b) c).hom.app K ≫ (cWX a b).hom.app ((UXX c).obj K) =
        eqToHom (congrArg (fun f ↦ (UWX f).obj K) (Category.assoc a b c)) ≫
          (cWX a (b ≫ c)).hom.app K ≫ (UWX a).map ((cXX b c).hom.app K))
    {x : W ⟶ X'} {Pa Pb Pab : X' ⟶ X'} (hab : Pab = Pb ≫ Pa) (ha : x ≫ Pa = x)
    (hb : x ≫ Pb = x) (h : x ≫ Pab = x) {K₁ K₂ K₃ K : DX} (h₁ : K₁ = K) (h₂ : K₂ = K)
    (h₃ : K₃ = K) (φa : (UXX Pa).obj K ⟶ K) (φb : (UXX Pb).obj K ⟶ K)
    (φab : (UXX Pab).obj K ⟶ K)
    (hφ : φab = eqToHom (congrArg (fun f ↦ (UXX f).obj K) hab) ≫ (cXX Pb Pa).hom.app K ≫
      (UXX Pb).map φa ≫ φb) :
    eqToHom (congrArg (UWX x).obj h₁.symm) ≫
        (eqToHom (congrArg (fun f ↦ (UWX f).obj K₁) h.symm) ≫ (cWX x Pab).hom.app K₁ ≫
          (UWX x).map ((UXX Pab).map (eqToHom h₁) ≫ φab ≫ eqToHom h₁.symm)) ≫
        eqToHom (congrArg (UWX x).obj h₁) =
      (eqToHom (congrArg (UWX x).obj h₂.symm) ≫
        (eqToHom (congrArg (fun f ↦ (UWX f).obj K₂) ha.symm) ≫ (cWX x Pa).hom.app K₂ ≫
          (UWX x).map ((UXX Pa).map (eqToHom h₂) ≫ φa ≫ eqToHom h₂.symm)) ≫
        eqToHom (congrArg (UWX x).obj h₂)) ≫
      eqToHom (congrArg (UWX x).obj h₃.symm) ≫
        (eqToHom (congrArg (fun f ↦ (UWX f).obj K₃) hb.symm) ≫ (cWX x Pb).hom.app K₃ ≫
          (UWX x).map ((UXX Pb).map (eqToHom h₃) ≫ φb ≫ eqToHom h₃.symm)) ≫
        eqToHom (congrArg (UWX x).obj h₃) := by
  subst h₁ h₂ h₃
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact stalkFrobenius_add_aux UWX UXX cWX cXX A hab ha hb h φa φb φab hφ

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The explicit form of the Frobenius of a stalk, for an abstract family of pullback functors:
`L(𝟙)^* Lx^* K ≅ L(𝟙 ≫ x)^* K = L(x ≫ P)^* K ≅ Lx^* LP^* K ⟶ Lx^* K` is
`Lx^* K = L(x ≫ P)^* K ≅ Lx^* LP^* K ⟶ Lx^* K`. -/
lemma stalkFrobenius_eq_aux {𝒞 : Type*} [Category 𝒞] {W X' : 𝒞} {DW DX : Type*}
    [Category DW] [Category DX] (UWW : (W ⟶ W) → DW ⥤ DW) (UWX : (W ⟶ X') → DX ⥤ DW)
    (UXX : (X' ⟶ X') → DX ⥤ DX)
    (cWW : ∀ (a : W ⟶ W) (b : W ⟶ X'), UWX (a ≫ b) ≅ UWX b ⋙ UWW a)
    (cWX : ∀ (a : W ⟶ X') (b : X' ⟶ X'), UWX (a ≫ b) ≅ UXX b ⋙ UWX a)
    (ιW : UWW (𝟙 W) ≅ 𝟭 DW)
    (hidl : ∀ (b : W ⟶ X') (K : DX), (cWW (𝟙 W) b).hom.app K ≫ ιW.hom.app ((UWX b).obj K) =
      eqToHom (show (UWX (𝟙 W ≫ b)).obj K = _ by rw [Category.id_comp]; rfl))
    {x : W ⟶ X'} {P : X' ⟶ X'} (hx : x ≫ P = x) (sq : 𝟙 W ≫ x = x ≫ P) {K : DX}
    (ψ : (UXX P).obj K ⟶ K) :
    ιW.inv.app ((UWX x).obj K) ≫ (cWW (𝟙 W) x).inv.app K ≫
        eqToHom (congrArg (fun f ↦ (UWX f).obj K) sq) ≫ (cWX x P).hom.app K ≫
        (UWX x).map ψ =
      eqToHom (congrArg (fun f ↦ (UWX f).obj K) hx.symm) ≫ (cWX x P).hom.app K ≫
        (UWX x).map ψ := by
  rw [PullbackFamily.inv_app_id_left UWW UWX cWW ιW hidl, Category.assoc,
    Iso.inv_hom_id_app_assoc, eqToHom_trans_assoc]

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The local Frobenius of degree `0` is the identity, for an abstract family of pullback
functors, for maps defined on `K'` and read on an equal object `K` through `eqToHom`. -/
lemma stalkFrobenius_zero_aux {𝒞 : Type*} [Category 𝒞] {W X' : 𝒞} {DW DX : Type*}
    [Category DW] [Category DX] (UWX : (W ⟶ X') → DX ⥤ DW) (UXX : (X' ⟶ X') → DX ⥤ DX)
    (cWX : ∀ (a : W ⟶ X') (b : X' ⟶ X'), UWX (a ≫ b) ≅ UXX b ⋙ UWX a)
    (ιX : UXX (𝟙 X') ≅ 𝟭 DX)
    (hidr : ∀ (a : W ⟶ X') (K : DX),
      (cWX a (𝟙 X')).hom.app K ≫ (UWX a).map (ιX.hom.app K) =
        eqToHom (congrArg (fun a ↦ (UWX a).obj K) (Category.comp_id a)))
    {x : W ⟶ X'} {P : X' ⟶ X'} (hP : P = 𝟙 X') (hx : x ≫ P = x) {K' K : DX} (hK : K' = K)
    (ψ : (UXX P).obj K ⟶ K)
    (hψ : ψ = eqToHom (congrArg (fun f ↦ (UXX f).obj K) hP) ≫ ιX.hom.app K) :
    eqToHom (congrArg (UWX x).obj hK.symm) ≫
      (eqToHom (congrArg (fun f ↦ (UWX f).obj K') hx.symm) ≫ (cWX x P).hom.app K' ≫
        (UWX x).map ((UXX P).map (eqToHom hK) ≫ ψ ≫ eqToHom hK.symm)) ≫
      eqToHom (congrArg (UWX x).obj hK) = 𝟙 _ := by
  subst hP hψ hK
  simp [hidr]

/-- The Frobenius of the stalk at `x` of a Weil object `(K, φ)` for `Φ`, for `x` fixed by `Φ`, is
`Lx^* K = L(x ≫ Φ)^* K ≅ Lx^* LΦ^* K --Lx^* φ--> Lx^* K`. -/
lemma weilStalk_obj_frobenius_hom_eq (x : RationalPoint X) (hx : x ≫ Φ = x)
    (K : WeilBoundedConstructible ℓ Φ) :
    ((weilStalk ℓ Φ x hx).obj K).frobenius.hom =
      eqToHom (congrArg (fun f ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ f).obj K.carrier) hx.symm) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x Φ).hom.app
          K.carrier ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map K.str.hom := by
  rw [weilStalk_obj_frobenius_hom]
  dsimp only [weilStalk]
  rw [weilUpperStar_obj_str]
  simp only [weilUpperStarComparison, boundedConstructiblePullbackSquareComparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
    eqToIso.inv, NatTrans.comp_app, eqToHom_app, Category.assoc]
  exact stalkFrobenius_eq_aux
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k))
    (fun b K ↦ boundedConstructibleUpperStarComp_id_left_app _ ℓ b K) hx
    (by rw [Category.id_comp, hx]) K.str.hom

/-- The local Frobenius as an explicit composite on the carrier of the iterate `(K, φ_m)`:
`Lx^* K = L(x ≫ Φ_m)^* K ≅ Lx^* LΦ_m^* K --Lx^* φ_m--> Lx^* K`. -/
lemma iterateStalk_frobenius_hom_eq (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    (K.iterateStalk m x hx).frobenius.hom =
      eqToHom (congrArg (fun f ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ f).obj (K.iterate m).carrier) hx.symm) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x
          (frobeniusIterate Φ m)).hom.app (K.iterate m).carrier ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
          (K.iterate m).str.hom :=
  weilStalk_obj_frobenius_hom_eq x hx (K.iterate m)


/-- The local Frobenius `F_{x,m}` as an explicit composite on the carrier `K'` of the iterate,
conjugated by the identification `K = K'`:
`Lx^* K = L(x ≫ Φ_m)^* K ≅ Lx^* LΦ_m^* K --Lx^* φ_m--> Lx^* K`. -/
lemma stalkFrobenius_eq_cast (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) :
    K.stalkFrobenius m x hx =
      eqToHom (congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
          (K.iterate_carrier m).symm) ≫
        (eqToHom (congrArg (fun f ↦
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
              (K.iterate m).carrier) hx.symm) ≫
          (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x
            (frobeniusIterate Φ m)).hom.app (K.iterate m).carrier ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              (frobeniusIterate Φ m)).map (eqToHom (K.iterate_carrier m)) ≫
              (K.iterateStr m).hom ≫ eqToHom (K.iterate_carrier m).symm)) ≫
        eqToHom (congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
          (K.iterate_carrier m)) := by
  rw [stalkFrobenius, iterateStalk_frobenius_hom_eq, iterate_str]
  simp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
/-- The local Frobenius depends on the degree only through its value. -/
lemma stalkFrobenius_congr (K : WeilBoundedConstructible ℓ Φ) {m m' : ℕ} (h : m = m')
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x)
    (hx' : x ≫ frobeniusIterate Φ m' = x) :
    K.stalkFrobenius m x hx = K.stalkFrobenius m' x hx' := by
  subst h
  rfl

/-- The local Frobenius of degree `0` is the identity. -/
lemma stalkFrobenius_zero (K : WeilBoundedConstructible ℓ Φ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ 0 = x) :
    K.stalkFrobenius 0 x hx = 𝟙 _ := by
  rw [stalkFrobenius_eq_cast]
  exact stalkFrobenius_zero_aux
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X)
    (fun a K ↦ boundedConstructibleUpperStarComp_id_right_app _ ℓ a K)
    (frobeniusIterate_zero Φ) hx (K.iterate_carrier 0) _ (by
      simp only [iterateStr, eqToHom_refl, Category.id_comp, Iso.app_hom])

/-- At a point fixed by `Φ_a` and `Φ_b`, `F_{x,a+b} = F_{x,b} ∘ F_{x,a}`. -/
lemma stalkFrobenius_add (K : WeilBoundedConstructible ℓ Φ) {a b : ℕ} (x : RationalPoint X)
    (ha : x ≫ frobeniusIterate Φ a = x) (hb : x ≫ frobeniusIterate Φ b = x)
    (hab : x ≫ frobeniusIterate Φ (a + b) = x) :
    K.stalkFrobenius (a + b) x hab = K.stalkFrobenius a x ha ≫ K.stalkFrobenius b x hb := by
  rw [stalkFrobenius_eq_cast, stalkFrobenius_eq_cast, stalkFrobenius_eq_cast]
  exact stalkFrobenius_add_eqToHom_aux
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b c K ↦ boundedConstructibleUpperStarComp_assoc_app _ ℓ a b c K)
    (frobeniusIterate_add Φ a b) ha hb hab (K.iterate_carrier (a + b)) (K.iterate_carrier a)
    (K.iterate_carrier b) _ _ _ (K.iterateStr_add a b)

/-- **The degree formula** (blueprint `theorem-trace-formula-euler-product`): at a point `x` fixed
by `Φ_d`, the local Frobenius of degree `d * n` is the `n`-th power of the local Frobenius of
degree `d`, `F_{x,dn} = F_{x,d}ⁿ`. -/
lemma stalkFrobenius_mul (K : WeilBoundedConstructible ℓ Φ) {d : ℕ} {x : RationalPoint X}
    (hx : x ≫ frobeniusIterate Φ d = x) (n : ℕ) :
    K.stalkFrobenius (d * n) x
        (by rw [frobeniusIterate_mul]; exact comp_frobeniusIterate_of_comp hx n) =
      (End.of (K.stalkFrobenius d x hx) ^ n).asHom := by
  induction n with
  | zero => exact K.stalkFrobenius_zero x _
  | succ n ih =>
    have hn : x ≫ frobeniusIterate Φ (d * n) = x := by
      rw [frobeniusIterate_mul]
      exact comp_frobeniusIterate_of_comp hx n
    have hn' : x ≫ frobeniusIterate Φ (d * n + d) = x := by
      rw [← Nat.mul_succ, frobeniusIterate_mul]
      exact comp_frobeniusIterate_of_comp hx (n + 1)
    rw [K.stalkFrobenius_congr (Nat.mul_succ d n) x _ hn', K.stalkFrobenius_add x hn hx hn', ih,
      pow_succ']
    rfl

/-- The iterate `φ_m` of a Weil structure commutes with `φ`: `φ ∘ LΦ^* φ_m = φ_m ∘ LΦ_m^* φ`
along `L(Φ ≫ Φ_m)^* = L(Φ_m ≫ Φ)^*`. -/
lemma iterateStr_comm (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) :
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Φ
        (frobeniusIterate Φ m)).hom.app K.carrier ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        (K.iterateStr m).hom ≫ K.str.hom =
    eqToHom (show (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (Φ ≫ frobeniusIterate Φ m)).obj K.carrier = _ by rw [comp_frobeniusIterate_comm]) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
        (frobeniusIterate Φ m) Φ).hom.app K.carrier ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (frobeniusIterate Φ m)).map K.str.hom ≫ (K.iterateStr m).hom := by
  have hcongr : ∀ {n n' : ℕ} (h : n = n'), (K.iterateStr n).hom =
      eqToHom (show (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (frobeniusIterate Φ n)).obj K.carrier = _ by rw [h]) ≫ (K.iterateStr n').hom := by
    intro n n' h
    subst h
    simp
  exact PullbackFamily.commute
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X)
    (fun a K ↦ boundedConstructibleUpperStarComp_id_right_app _ ℓ a K)
    (frobeniusIterate_zero Φ) (frobeniusIterate_succ Φ 0) (frobeniusIterate_succ Φ m)
    (frobeniusIterate_add Φ 1 m) (by rw [Nat.add_comm]) (comp_frobeniusIterate_comm Φ m)
    K.str.hom (K.iterateStr m).hom (K.iterateStr 0).hom (K.iterateStr 1).hom
    (K.iterateStr (m + 1)).hom (K.iterateStr (1 + m)).hom
    (by simp only [iterateStr, eqToHom_refl, Category.id_comp, Iso.app_hom])
    (by simp only [iterateStr, Iso.trans_hom, eqToIso.hom, Iso.app_hom,
      Functor.mapIso_hom])
    (by simp only [iterateStr, Iso.trans_hom, eqToIso.hom, Iso.app_hom,
      Functor.mapIso_hom])
    (iterateStr_add K 1 m) (hcongr (Nat.add_comm m 1))

/-- The isomorphism underlying the Frobenius transport `stalkTransport`:
```
L(x ≫ Φ)^* K ≅ Lx^* LΦ^* K --Lx^* φ--> Lx^* K.
```
It is stated on the carrier `(K.iterate m).carrier` of the iterate, equal to `K.carrier`; the
casts are explicit (`eqToIso`), since checking this equality by unfolding is expensive.
-/
noncomputable def stalkTransportIso (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    (K.iterateStalk m (x ≫ Φ) (comp_comp_frobeniusIterate hx)).carrier ≅
      (K.iterateStalk m x hx).carrier :=
  (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x Φ).app
      (K.iterate m).carrier ≪≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).mapIso
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).mapIso
        (eqToIso (K.iterate_carrier m)) ≪≫ K.str ≪≫ eqToIso (K.iterate_carrier m).symm)

/-- The *Frobenius transport* between the stalks at `x ≫ Φ` and at `x` of the iterate
`(K, φ_m)`, for `x` fixed by `Φ_m`: the isomorphism of Weil objects for the identity of `s` whose
underlying isomorphism is `stalkTransportIso`,
```
L(x ≫ Φ)^* K ≅ Lx^* LΦ^* K --Lx^* φ--> Lx^* K.
```
It intertwines the local Frobenii since `φ_m` commutes with `φ`. -/
noncomputable def stalkTransport (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) :
    K.iterateStalk m (x ≫ Φ) (comp_comp_frobeniusIterate hx) ≅ K.iterateStalk m x hx :=
  IsoAlgebra.isoMk (K.stalkTransportIso m x hx) (by
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom]
    dsimp only [iterateStalk, weilStalk]
    rw [weilUpperStar_obj_str, weilUpperStar_obj_str, iterate_str]
    simp only [stalkTransportIso, weilUpperStarComparison,
      boundedConstructiblePullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv, Functor.map_comp,
      eqToHom_map, NatTrans.comp_app, eqToHom_app, Category.assoc]
    have hψ := K.iterateStr_comm m
    exact PullbackFamily.transport_eqToHom
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k))
      (fun b K ↦ boundedConstructibleUpperStarComp_id_left_app _ ℓ b K)
      (fun a b c K ↦ boundedConstructibleUpperStarComp_assoc_app _ ℓ a b c K) hx
      (comp_frobeniusIterate_comm Φ m) (K.iterate_carrier m) K.str.hom (K.iterateStr m).hom hψ
      _ _ _ _ _ _ _ _ _ _)

attribute [local instance] boundedConstructibleBraiding in
/-- **Conjugacy of the local Frobenii** (blueprint `theorem-trace-formula-euler-product--1`): the
local Frobenii at `x` and at its Frobenius translate `x ≫ Φ` have the same trace. -/
theorem trace_stalkFrobenius_comp (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)]
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ Φ)).obj
      K.carrier)] :
    trace (K.stalkFrobenius m (x ≫ Φ) (comp_comp_frobeniusIterate hx)) =
      trace (K.stalkFrobenius m x hx) :=
  trace_eq_of_iso
    (X := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ Φ)).obj K.carrier)
    (X' := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier)
    ((IsoAlgebra.forget _).mapIso (K.stalkTransport m x hx)) _ _
    (by rw [stalkFrobenius_eq_frobenius, stalkFrobenius_eq_frobenius]
        exact frobenius_hom_naturality (K.stalkTransport m x hx).hom)

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
