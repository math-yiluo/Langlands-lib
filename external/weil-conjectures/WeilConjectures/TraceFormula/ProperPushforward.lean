/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverProper
public import WeilConjectures.TraceFormula.Correspondence

/-!

# Proper pushforward of a correspondence

Let `c = (C, c₁, c₂, u)` be an endocorrespondence of `(X, K)`. A *proper pushforward diagram*
`(f, g) : (C, c) ⟶ (D, b)` (blueprint `definition-pushforward-correspondence--1`) consists of a
proper morphism `f : X ⟶ Y`, a second support `b = (b₁, b₂) : D ⟶ Y × Y` and a proper morphism
`g : C ⟶ D` with `g ≫ bᵢ = cᵢ ≫ f`
(`ProEtale.CondensedRing.Correspondence.ProperPushforwardDiagram`). No cartesian condition on
the leg squares is imposed. With `K' = Rf_* K`, the *coefficient pushforward* of `u` is
```
[f, g]_! u = δ ∘ Rg_* u ∘ γ : Lb₂^* K' ⟶ Rb₁^! K',
```
where
* the *ordinary half* `γ : Lb₂^* K' ⟶ Rg_* Lc₂^* K` is the unit of `Lg^* ⊣ Rg_*`, followed by
  the pullback composition `Lg^* Lb₂^* ≅ L(g ≫ b₂)^* = L(c₂ ≫ f)^* ≅ Lc₂^* Lf^*` and the counit of
  `Lf^* ⊣ Rf_*` (`ProperPushforwardDiagram.pushforwardCoeffUnit`);
* the *exceptional half* `δ : Rg_* Rc₁^! K ⟶ Rb₁^! K'` is the adjoint for `Rb₁_! ⊣ Rb₁^!` of
  `Rb₁_! Rg_* Rc₁^! K ≅ Rb₁_! Rg_! Rc₁^! K ≅ Rf_! Rc₁_! Rc₁^! K ⟶ Rf_! K ≅ Rf_* K`
  (`ProperPushforwardDiagram.pushforwardCoeffCounit`).

This gives a correspondence `(D, b₁, b₂, [f, g]_! u)` of `(Y, Rf_* K)`
(`ProperPushforwardDiagram.pushforward`).

## The induced map of fixed loci

The relations `g ≫ bᵢ = cᵢ ≫ f` induce `h : Fix(c) ⟶ Fix(b)`, the restriction of `g`
(`ProperPushforwardDiagram.fixMap`). It factors as
```
Fix(c) --κ--> C ×_D Fix(b) --π--> Fix(b)
```
with `π` the base change of `g` and `κ` a base change of the relative diagonal
`X ⟶ X ×_Y X` (`ProperPushforwardDiagram.isPullback_fixMapFactor`), hence a closed immersion;
so `h` is proper (`ProperPushforwardDiagram.isProper_fixMap`, blueprint
`definition-pushforward-correspondence--2`), and so is `q = f × f`
(`ProperPushforwardDiagram.isProper_prodMap`).

## Maps along proper morphisms

For the kernel maps of a proper pushforward diagram (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`) we construct the trace `τ_f : Rf_* ω_X ⟶ ω_Y`
(`lowerStarDualizingComplexTrace`) and the multiplication
`μ_f : Rf_* M ⊗ Rf_* N ⟶ Rf_* (M ⊗ N)` (`lowerStarTensorMap`). For a commutative square
`g ≫ b = c ≫ f` with `g`, `f` proper we construct the composition isomorphism
`Ξ : Rb_! Rg_* ≅ Rf_* Rc_!` (`lowerStarLowerShriekCompIso`) and its mate, the exchange map
`E : Rg_* Rc^! ⟶ Rb^! Rf_*` (`lowerStarUpperShriekExchange`); the exceptional half `δ` above is
`E` for the square `g ≫ b₁ = c₁ ≫ f`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Maps along proper morphisms -/

section ProperMaps

variable (ℓ) {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The *trace along a proper morphism* `τ_f : Rf_* ω_X ⟶ ω_Y` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, item 2):
```
Rf_* ω_X ≅ Rf_! ω_X ≅ Rf_! Rf^! ω_Y --ε--> ω_Y,
```
using `Rf_! ≅ Rf_*` for the proper `f`, the composition isomorphism `Rf^! ω_Y ≅ ω_X`
(`dualizingComplexComp`) and the counit of `Rf_! ⊣ Rf^!`. -/
noncomputable def lowerStarDualizingComplexTrace (f : X ⟶ Y) [IsProper f.left] :
    (boundedConstructibleLowerStar ℓ f).obj
        (dualizingComplex' ℓ X) ⟶ dualizingComplex' ℓ Y :=
  (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app _ ≫
    (boundedConstructibleLowerShriek ℓ f).map
      (dualizingComplexComp ℓ f).inv ≫
    (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app _

/-- The *multiplication* `μ_f : Rf_* M ⊗ Rf_* N ⟶ Rf_* (M ⊗ N)` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, item 3): the adjoint for `Lf^* ⊣ Rf_*` of
```
Lf^* (Rf_* M ⊗ Rf_* N) ≅ Lf^* Rf_* M ⊗ Lf^* Rf_* N --ε ⊗ ε--> M ⊗ N,
```
the monoidal structure of `Lf^*` followed by the counits. -/
noncomputable def lowerStarTensorMap (f : X ⟶ Y)
    (M N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar ℓ f).obj M ⊗
        (boundedConstructibleLowerStar ℓ f).obj N ⟶
      (boundedConstructibleLowerStar ℓ f).obj (M ⊗ N) :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).homEquiv
    _ _
    (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
        _ _ ≫
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          f).counit.app M ⊗ₘ
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ
          f).counit.app N))

end ProperMaps

section Exchange

variable (ℓ) {C D X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {c : C ⟶ X} {g : C ⟶ D} {b : D ⟶ Y} {f : X ⟶ Y} [IsProper g.left] [IsProper f.left]

/-- The *composition isomorphism* `Ξ : Rb_! Rg_* ≅ Rf_* Rc_!` of a commutative square
`g ≫ b = c ≫ f` with proper `g` and `f` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, item 9):
```
Rb_! Rg_* ≅ Rb_! Rg_! ≅ R(g ≫ b)_! = R(c ≫ f)_! ≅ Rf_! Rc_! ≅ Rf_* Rc_!,
```
using `Rg_! ≅ Rg_*`, `Rf_! ≅ Rf_*` and the composition isomorphisms of the lower shriek. -/
noncomputable def lowerStarLowerShriekCompIso (w : g ≫ b = c ≫ f) :
    boundedConstructibleLowerStar ℓ g ⋙
        boundedConstructibleLowerShriek ℓ b ≅
      boundedConstructibleLowerShriek ℓ c ⋙
        boundedConstructibleLowerStar ℓ f :=
  Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).symm _ ≪≫
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).symm ≪≫
    eqToIso (by rw [w]) ≪≫
    boundedConstructibleLowerShriekComp_padicAlgCl ℓ c f ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)

/-- The *exchange map* `E : Rg_* Rc^! ⟶ Rb^! Rf_*` of a commutative square `g ≫ b = c ≫ f` with
proper `g` and `f` (blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, item 9): the
exceptional adjoint of
```
Rb_! Rg_* Rc^! ≅ Rf_* Rc_! Rc^! --Rf_* ε_c--> Rf_*,
```
that is, the mate of the composition isomorphism `lowerStarLowerShriekCompIso` for the
adjunctions `Rc_! ⊣ Rc^!` and `Rb_! ⊣ Rb^!`. No cartesian condition on the square is needed. -/
noncomputable def lowerStarUpperShriekExchange (w : g ≫ b = c ≫ f) :
    boundedConstructibleUpperShriek ℓ c ⋙
        boundedConstructibleLowerStar ℓ g ⟶
      boundedConstructibleLowerStar ℓ f ⋙
        boundedConstructibleUpperShriek ℓ b :=
  mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ c)
    (boundedConstructibleUpperShriekAdjunction ℓ b)
    (lowerStarLowerShriekCompIso ℓ w).hom

end Exchange

namespace Correspondence

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-! ### Proper pushforward diagrams -/

variable (c : Correspondence ℓ K) (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-! ### The universal property of the fixed locus -/

namespace FixedLocus

variable {c} (F : c.FixedLocus)

@[reassoc (attr := simp)]
lemma lift_ι {W : Over (Spec (.of k))} (t : W ⟶ c.C) (h : t ≫ c.c₁ = t ≫ c.c₂) :
    Fork.IsLimit.lift F.isLimit t h ≫ F.ι = t :=
  Fork.IsLimit.lift_ι' _ _ _

lemma hom_ext {W : Over (Spec (.of k))} {t t' : W ⟶ F.F} (h : t ≫ F.ι = t' ≫ F.ι) : t = t' :=
  Fork.IsLimit.hom_ext F.isLimit h

end FixedLocus

/-- A *proper pushforward diagram* `(f, g) : (C, c) ⟶ (D, b)` of an endocorrespondence `c` of
`(X, K)` to a scheme `Y` (blueprint `definition-pushforward-correspondence--1`): a proper morphism
`f : X ⟶ Y`, a separated `k`-scheme of finite type `D` with morphisms `b₁, b₂ : D ⟶ Y`, and a
proper morphism `g : C ⟶ D` with `g ≫ bᵢ = cᵢ ≫ f`. No cartesian condition is imposed on the
leg squares. -/
structure ProperPushforwardDiagram where
  /-- the proper morphism `f : X ⟶ Y`. -/
  f : X ⟶ Y
  [isProper_f : IsProper f.left]
  /-- the support `D` of the target correspondence. -/
  D : Over (Spec (.of k))
  [locallyOfFiniteType : LocallyOfFiniteType D.hom]
  [quasiCompact : QuasiCompact D.hom]
  [isSeparated : IsSeparated D.hom]
  /-- the exceptional leg `b₁ : D ⟶ Y`. -/
  b₁ : D ⟶ Y
  /-- the ordinary leg `b₂ : D ⟶ Y`. -/
  b₂ : D ⟶ Y
  /-- the proper morphism `g : C ⟶ D`. -/
  g : c.C ⟶ D
  [isProper_g : IsProper g.left]
  w₁ : g ≫ b₁ = c.c₁ ≫ f
  w₂ : g ≫ b₂ = c.c₂ ≫ f

namespace ProperPushforwardDiagram

attribute [instance] isProper_f isProper_g locallyOfFiniteType quasiCompact isSeparated

variable {c Y} (P : c.ProperPushforwardDiagram Y)

/-- The pushforward coefficient `K' = Rf_* K` of a proper pushforward diagram. -/
noncomputable abbrev coeff : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleLowerStar ℓ P.f).obj K

/-- The *ordinary half* `γ : Lb₂^* K' ⟶ Rg_* Lc₂^* K` of the coefficient pushforward (blueprint
`definition-pushforward-correspondence--1`, item 1):
```
Lb₂^* K' --η_g--> Rg_* Lg^* Lb₂^* K' ≅ Rg_* L(g ≫ b₂)^* K' = Rg_* L(c₂ ≫ f)^* K'
  ≅ Rg_* Lc₂^* Lf^* Rf_* K --Rg_* Lc₂^* ε_f--> Rg_* Lc₂^* K.
```
-/
noncomputable def pushforwardCoeffUnit :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.b₂).obj P.coeff ⟶
      (boundedConstructibleLowerStar ℓ P.g).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K) :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ
      P.g).unit.app _ ≫
    (boundedConstructibleLowerStar ℓ P.g).map
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ P.g P.b₂).inv.app _ ≫
        eqToHom (by rw [P.w₂]) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂ P.f).hom.app _ ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            P.f).counit.app K))

/-- The *exceptional half* `δ : Rg_* Rc₁^! K ⟶ Rb₁^! K'` of the coefficient pushforward
(blueprint `definition-pushforward-correspondence--1`, item 2): the adjoint for `Rb₁_! ⊣ Rb₁^!` of
```
Rb₁_! Rg_* Rc₁^! K ≅ Rb₁_! Rg_! Rc₁^! K ≅ R(g ≫ b₁)_! Rc₁^! K = R(c₁ ≫ f)_! Rc₁^! K
  ≅ Rf_! Rc₁_! Rc₁^! K ≅ Rf_* Rc₁_! Rc₁^! K --Rf_* ε_{c₁}--> Rf_* K,
```
using `Rg_! ≅ Rg_*`, `Rf_! ≅ Rf_*` for the proper `g`, `f` and the composition isomorphisms of
the lower shriek: the exchange map `lowerStarUpperShriekExchange` of the square
`g ≫ b₁ = c₁ ≫ f` at `K`. -/
noncomputable def pushforwardCoeffCounit :
    (boundedConstructibleLowerStar ℓ P.g).obj
        ((boundedConstructibleUpperShriek ℓ c.c₁).obj K) ⟶
      (boundedConstructibleUpperShriek ℓ P.b₁).obj P.coeff :=
  (lowerStarUpperShriekExchange ℓ P.w₁).app K

/-- The *coefficient pushforward* `[f, g]_! u = δ ∘ Rg_* u ∘ γ : Lb₂^* K' ⟶ Rb₁^! K'` of the
coefficient map of `c` along a proper pushforward diagram (blueprint
`definition-pushforward-correspondence--1`, item 3). -/
noncomputable def pushforwardCoeff :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.b₂).obj P.coeff ⟶
      (boundedConstructibleUpperShriek ℓ P.b₁).obj P.coeff :=
  P.pushforwardCoeffUnit ≫
    (boundedConstructibleLowerStar ℓ P.g).map c.u ≫
    P.pushforwardCoeffCounit

/-- The *proper pushforward* `(D, b₁, b₂, [f, g]_! u)` of the correspondence `c`, a
correspondence of `(Y, Rf_* K)` (blueprint `definition-pushforward-correspondence--1`). -/
noncomputable abbrev pushforward : Correspondence ℓ P.coeff where
  C := P.D
  c₁ := P.b₁
  c₂ := P.b₂
  u := P.pushforwardCoeff


/-! ### The induced map of fixed loci -/

lemma pushforward_c₁ : P.pushforward.c₁ = P.b₁ := rfl

lemma pushforward_c₂ : P.pushforward.c₂ = P.b₂ := rfl

variable (Fc : c.FixedLocus) (Fb : P.pushforward.FixedLocus)

omit [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
lemma fixedLocus_ι_comp_g_comp_b₁ :
    (Fc.ι ≫ P.g) ≫ P.b₁ = (Fc.ι ≫ P.g) ≫ P.b₂ := by
  rw [Category.assoc, Category.assoc, P.w₁, P.w₂, ← Category.assoc, Fc.w, Category.assoc]

/-- The *induced map of fixed loci* `h : Fix(c) ⟶ Fix(b)` of a proper pushforward diagram, the
restriction of `g` (blueprint `definition-pushforward-correspondence--1`, item 4): the factorization
of `Fix(c) ⟶ C ⟶ D` through the equalizer `Fix(b) ⟶ D` of `b₁` and `b₂`. -/
noncomputable def fixMap : Fc.F ⟶ Fb.F :=
  Fork.IsLimit.lift Fb.isLimit (Fc.ι ≫ P.g) (P.fixedLocus_ι_comp_g_comp_b₁ Fc)

/-- The induced map of fixed loci satisfies `i_b ∘ h = g ∘ i_c`. -/
@[reassoc]
lemma fixMap_ι : P.fixMap Fc Fb ≫ Fb.ι = Fc.ι ≫ P.g :=
  Fb.lift_ι _ _

/-- The induced map of fixed loci satisfies `d_b ∘ h = f ∘ d_c`. -/
@[reassoc]
lemma fixMap_ι_b₁ : P.fixMap Fc Fb ≫ Fb.ι ≫ P.b₁ = Fc.ι ≫ c.c₁ ≫ P.f := by
  rw [fixMap_ι_assoc, P.w₁]

/-- The first factor `κ = (i_c, h) : Fix(c) ⟶ C ×_D Fix(b)` of the induced map of fixed loci
(blueprint `definition-pushforward-correspondence--2`). -/
noncomputable def fixMapFactor : Fc.F ⟶ pullback P.g Fb.ι :=
  pullback.lift Fc.ι (P.fixMap Fc Fb) (P.fixMap_ι Fc Fb).symm

@[reassoc]
lemma fixMapFactor_fst : P.fixMapFactor Fc Fb ≫ pullback.fst _ _ = Fc.ι :=
  pullback.lift_fst _ _ _

/-- The induced map of fixed loci factors as `h = π ∘ κ`, with `π : C ×_D Fix(b) ⟶ Fix(b)` the
base change of `g` (blueprint `definition-pushforward-correspondence--2`, item 1). -/
@[reassoc]
lemma fixMapFactor_snd : P.fixMapFactor Fc Fb ≫ pullback.snd _ _ = P.fixMap Fc Fb :=
  pullback.lift_snd _ _ _

/-- The map `λ = (c₁, c₂) ∘ j : C ×_D Fix(b) ⟶ X ×_Y X`: on `C ×_D Fix(b)` the two legs agree
after composing with `f`. -/
noncomputable def fixMapFactorDiagonalLift : pullback P.g Fb.ι ⟶ pullback P.f P.f :=
  pullback.lift (pullback.fst _ _ ≫ c.c₁) (pullback.fst _ _ ≫ c.c₂) (by
    rw [Category.assoc, Category.assoc, ← P.w₁, ← P.w₂, pullback.condition_assoc,
      pullback.condition_assoc]
    exact pullback.snd _ _ ≫= Fb.w)

@[reassoc]
lemma fixMapFactorDiagonalLift_fst :
    P.fixMapFactorDiagonalLift Fb ≫ pullback.fst _ _ = pullback.fst _ _ ≫ c.c₁ :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma fixMapFactorDiagonalLift_snd :
    P.fixMapFactorDiagonalLift Fb ≫ pullback.snd _ _ = pullback.fst _ _ ≫ c.c₂ :=
  pullback.lift_snd _ _ _

/-- The first factor `κ` of the induced map of fixed loci is the base change of the relative
diagonal `X ⟶ X ×_Y X` along `λ : C ×_D Fix(b) ⟶ X ×_Y X` (blueprint
`definition-pushforward-correspondence--2`, item 1). -/
lemma isPullback_fixMapFactor :
    IsPullback (P.fixMapFactor Fc Fb) (Fc.ι ≫ c.c₁) (P.fixMapFactorDiagonalLift Fb)
      (pullback.diagonal P.f) := by
  have hs (s : PullbackCone (P.fixMapFactorDiagonalLift Fb) (pullback.diagonal P.f)) :
      s.fst ≫ pullback.fst _ _ ≫ c.c₁ = s.snd ∧ s.fst ≫ pullback.fst _ _ ≫ c.c₂ = s.snd := by
    have h₁ := s.condition =≫ pullback.fst P.f P.f
    have h₂ := s.condition =≫ pullback.snd P.f P.f
    rw [Category.assoc, Category.assoc, fixMapFactorDiagonalLift_fst, pullback.diagonal_fst,
      Category.comp_id] at h₁
    rw [Category.assoc, Category.assoc, fixMapFactorDiagonalLift_snd, pullback.diagonal_snd,
      Category.comp_id] at h₂
    exact ⟨h₁, h₂⟩
  have hc (s : PullbackCone (P.fixMapFactorDiagonalLift Fb) (pullback.diagonal P.f)) :
      (s.fst ≫ pullback.fst _ _) ≫ c.c₁ = (s.fst ≫ pullback.fst _ _) ≫ c.c₂ := by
    rw [Category.assoc, Category.assoc, (hs s).1, (hs s).2]
  have w : P.fixMapFactor Fc Fb ≫ P.fixMapFactorDiagonalLift Fb =
      (Fc.ι ≫ c.c₁) ≫ pullback.diagonal P.f := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, fixMapFactorDiagonalLift_fst, fixMapFactor_fst_assoc,
        pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, fixMapFactorDiagonalLift_snd, fixMapFactor_fst_assoc,
        pullback.diagonal_snd, Category.comp_id, Fc.w]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ w) (PullbackCone.IsLimit.mk w
    (fun s ↦ Fork.IsLimit.lift Fc.isLimit (s.fst ≫ pullback.fst _ _) (hc s)) (fun s ↦ ?_)
    (fun s ↦ ?_) (fun s m hm _ ↦ ?_))
  · apply pullback.hom_ext
    · rw [Category.assoc, fixMapFactor_fst, Fc.lift_ι]
    · rw [Category.assoc, fixMapFactor_snd]
      apply Fb.hom_ext
      rw [Category.assoc, Category.assoc, fixMap_ι, Fc.lift_ι_assoc, Category.assoc,
        pullback.condition]
  · rw [Fc.lift_ι_assoc]
    exact (hs s).1
  · apply Fc.hom_ext
    rw [Fc.lift_ι, ← hm, Category.assoc, fixMapFactor_fst]

/-- The first factor `κ : Fix(c) ⟶ C ×_D Fix(b)` of the induced map of fixed loci is a closed
immersion, as a base change of the relative diagonal of the separated morphism `f` (blueprint
`definition-pushforward-correspondence--2`, item 1). -/
instance isClosedImmersion_fixMapFactor : IsClosedImmersion (P.fixMapFactor Fc Fb).left :=
  MorphismProperty.of_isPullback ((P.isPullback_fixMapFactor Fc Fb).map (Over.forget _)).flip
    (inferInstanceAs (IsClosedImmersion (pullback.diagonal P.f).left))

/-- The second factor `π : C ×_D Fix(b) ⟶ Fix(b)` of the induced map of fixed loci is proper, as
the base change of the proper `g` along `i_b : Fix(b) ⟶ D` (blueprint
`definition-pushforward-correspondence--2`, item 1). -/
instance isProper_pullbackSnd_g : IsProper (pullback.snd P.g Fb.ι).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback P.g Fb.ι).map (Over.forget _))
    (inferInstanceAs (IsProper P.g.left))

/-- **The induced map of fixed loci is proper** (blueprint
`definition-pushforward-correspondence--2`, item 2): `h = π ∘ κ` is the composite of the closed
immersion `κ` and the base change `π` of the proper `g`. -/
instance isProper_fixMap : IsProper (P.fixMap Fc Fb).left := by
  rw [← P.fixMapFactor_snd Fc Fb, Over.comp_left]
  infer_instance

/-- The product `q = f × f : X ×_k X ⟶ Y ×_k Y` of the proper `f` is proper (blueprint
`definition-pushforward-correspondence--2`, item 2). -/
instance isProper_prodMap : IsProper (prod.map P.f P.f).left :=
  inferInstance

end ProperPushforwardDiagram

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
